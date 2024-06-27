(*
Constraint types. We try to make little internal distinction,
so that what you see in the code is also what you get in a generated
constraint file.
*)

(* Actually, for now, we're not worrying about generalization.
   For now, for the purpose of demonstration, we're going to intentionally
   over-generalize let-bindings. In the future, we can match OCaml's
   value-restriction and do proper level-based generalization.
   A union-find adaptation of the lazy level algorithm should work. *)
(** See https://okmij.org/ftp/ML/generalization.html *)
type level = int

(** A modified (and restricted) clone of Types.type_desc. *)
type ztype =
    (* 'a for example. Tvar names are globally unique and are emitted in constraints. *)
  | Tvar of string (* string option to support holes in future maybe *)
    (** A single type arrow t1 -> t2. *)
  | Tarrow of ztype * ztype (* Asttypes.arg_label for labeled/optional args in future maybe *)
    (** A tuple, (t1 * t2 * ... * tn). *)
  | Ttuple of ztype list 
    (** A type constructor, (t1, ..., tn) t.
      Resolution of type synonyms happens separately before emitting constraints.
      We will need some mechanism of recovering the alias used at each source location
      in order to provide good error messages from the SMT response. *)
  | Tconstr of Path.t * ztype list
    (* We can add objects (and fields) / variants in the future. *)

(** A counter for producing globally unique Tvar names. *)
let tvar_ctr = ref (-1)

(** Reset the tvar_ctr. *)
let reset_tvar_ctr () = tvar_ctr := 0

(** Produce a globally unique name for a Tvar. *)
let gensym ?(name="_") () =
  let c = incr tvar_ctr; !tvar_ctr in
  name ^ "." ^ string_of_int c

(** Create a new type variable at the current level.
    All names produced by this function are globally unique. *)
let newvar ?(name="_") () =
  (* let level = Ctype.get_current_level () *)
  let name' = gensym ~name () in
  Tvar name'

let tvar_name = function
  | Tvar n -> n
  | _ -> failwith "tvar_name: not a tvar!"

let print ?(fmt=Format.std_formatter) ty =
  let parens f = Format.pp_print_char fmt '('; f (); Format.pp_print_char fmt ')' in

  let rec go = function
  | Tvar name -> Format.pp_print_string fmt name
  | Tarrow (ty1, ty2) -> parens @@ fun () ->
    go ty1;
    Format.pp_print_string fmt " -> ";
    go ty2
  | Ttuple tys ->
    begin match tys with
    | [] -> failwith "Ztype.print: empty tuple?"
    | (one::more) -> parens @@ fun () ->
      go one;
      List.iter (fun ty' -> Format.pp_print_string fmt " * "; go ty') more
    end
  | Tconstr (name, tys) ->
    begin match tys with
    | [] -> Path.print fmt name
    | [one] -> parens (fun () -> go one); Path.print fmt name
    | (one::more) ->
      parens (fun () ->
        go one;
        List.iter (fun ty' -> Format.pp_print_string fmt ", "; go ty') more);
      Path.print fmt name
    end
  in go ty

module rec Constraint : sig
  type 'loc t =
    | Equal of 'loc * ztype * ztype 
    | Scheme of 'loc * string * string list (** where, scheme name, qvar instances *)
  val map : ('locA -> 'locB) -> 'locA t -> 'locB t
  val print : ?fmt:Format.formatter -> ?print_loc:('loc -> unit) -> 'loc t -> unit
end = struct
(** A ZGen typing constraint. At some program location, we have some
    equality, or some scheme instance.
    Parametric in locations; initially Location.t, but a
    location enumeration pass will eventually replace these with `int`. *)
  type 'loc t =
    | Equal of 'loc * ztype * ztype
    | Scheme of 'loc * string * string list

  let map (f : 'locA -> 'locB) = function
    | Equal (loc, t1, t2) -> Equal (f loc, t1, t2)
    | Scheme (loc, name, ivars) -> Scheme (f loc, name, ivars)

  let print ?(fmt=Format.std_formatter) ?print_loc c =
    let print_loc loc =
      begin match print_loc with
      | None -> Format.pp_print_string fmt "<loc>"
      | Some p -> p loc
      end
    in
    match c with
      (* note that references to 'print' here refer to Ztype.print *)
    | Equal (loc, ty1, ty2) ->
      print_loc loc; Format.pp_print_char fmt ' ';
      print ~fmt ty1; Format.pp_print_string fmt " = "; print ~fmt ty2
    | Scheme (loc, name, vars) ->
      print_loc loc; Format.pp_print_char fmt ' ';
      Format.pp_print_string fmt name;
      Format.pp_print_char fmt '(';
      begin match vars with
      | [] -> ()
      | (one::more) ->
        Format.pp_print_string fmt one;
        List.iter (fun v -> Format.pp_print_string fmt @@ ","^v) more
      end;
      Format.pp_print_char fmt ')'
end

(** Schemes over ztypes. A scheme is a ztype, with some number (possibly 0)
    of its Tvars universally quantified. Additionally, it tracks the
    constraints associated with that ztype, and the location at which
    the scheme was plotted. This information goes directly to the output.
    When no vars are quantified, the type is monomorphic and Scheme
    constraints are not emitted. *)
and Scheme : sig
  type forall = Forall of string list
  (* name, qvars, ty, cs, where *)
  type 'loc t = Scheme of string * forall * ztype * 'loc Constraint.t list * 'loc

  val mono : 'loc -> ztype -> 'loc t
  val instantiate : 'loc -> 'loc t -> (ztype * 'loc Constraint.t)

  val map : ('locA -> 'locB) -> 'locA t -> 'locB t
  val loc_of : 'loc t -> 'loc

  val print : ?fmt:Format.formatter -> ?print_loc:('a -> unit) -> 'a t -> unit
end = struct
  (** Keep the quantified vars list explicit, as we need it when we emit schemes. *)
  type forall = Forall of string list [@@unpacked]

  type 'loc t = Scheme of string * forall * ztype * 'loc Constraint.t list * 'loc

  let mono loc ty = Scheme (gensym (), Forall [], ty, [], loc)
  let instantiate where (Scheme (name, Forall qvars, ty, _, _)) =
    let module Ht = Hashtbl in
    let ht = Ht.create 2 in
    let ivars = List.map (fun v -> newvar ~name:v ()) qvars in
    List.iter2 (fun qvar ivar -> Ht.add ht qvar ivar) qvars ivars;
    let lookup tv varname = match Ht.find_opt ht varname with
      | Some ivar -> ivar
      | None -> tv
    in
    let rec alpha_cvt = function
      | Tvar _ as tv -> lookup tv @@ tvar_name tv
      | Tarrow (ty1, ty2) -> Tarrow (alpha_cvt ty1, alpha_cvt ty2)
      | Ttuple tys -> Ttuple (List.map alpha_cvt tys)
      | Tconstr (name, tys) -> Tconstr (name, List.map alpha_cvt tys)
    in (alpha_cvt ty, Constraint.Scheme (where, name, List.map tvar_name ivars))

  let map (f : 'locA -> 'locB) (Scheme (name, forall, t, cs, loc)) =
    Scheme (name, forall, t, List.map (Constraint.map f) cs, f loc)

  let loc_of (Scheme (_, _, _, _, loc)) = loc

  let print ?(fmt=Format.std_formatter)
            ?(print_loc=fun _ -> Format.pp_print_string fmt "<loc> ")
            (Scheme (name, Forall qvars, _, cs, loc)) =
    let comma () = Format.pp_print_string fmt ", " in
    (* while printing constraints, we keep a vbox open,
      open it before the end of the first line. *)
    Format.pp_open_vbox fmt 2;
    print_loc loc; Format.pp_print_char fmt ' ';
    Format.pp_print_string fmt name; Format.pp_print_char fmt '(';
    begin match qvars with
      | [] -> ()
      | (one::more) ->
        Format.pp_print_string fmt one;
        List.iter (fun n -> comma (); Format.pp_print_string fmt n) more
    end; Format.pp_print_string fmt ") {";
    let print_c c =
      Format.pp_print_cut fmt ();
      Constraint.print ~fmt ~print_loc c in
    List.iter print_c cs;
    Format.pp_close_box fmt (); Format.pp_print_cut fmt ();
    Format.pp_print_char fmt '}';

end
