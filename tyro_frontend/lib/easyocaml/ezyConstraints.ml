open EzyOcamlmodules
open EzyUtils
open EzyUtils.Infix
open EzyTypingCoreTypes

let hard_loc_tbl : (ExtLocation.t, unit) Hashtbl.t = Hashtbl.create 1000
let make_loc_hard (loc : ExtLocation.t) = Hashtbl.add hard_loc_tbl loc ()
let is_loc_hard (loc : ExtLocation.t) = Hashtbl.mem hard_loc_tbl loc

(******************************************************************************)
(*                                 EqConstr                                   *
 * [EqConstr.t] is a constraint between two types annotated with a single     *
 * extended location.                                                         *)
(******************************************************************************)
module EqConstr = struct

  type t = {
    loc : ExtLocation.t ;
    tys : (Ty.t * Ty.t)
  }
  type printable = t
  type tyvar_container = t

  let create x loc y = 
    { loc = loc; tys = (x, y) }

  let compare c1 c2 =
    match ExtLocation.compare c1.loc c2.loc with
        0 -> lexical Ty.compare c1.tys c2.tys
      | n -> n

  let tyvars { tys = (x, y) ; _ } =
    TyVarSet.union (Ty.tyvars x) (Ty.tyvars y)

  let fresh_variant ?(create=true) ?(tyvarmap=TyVarMap.empty) c =
    let tyvarmap, ty1 = Ty.fresh_variant ~create ~tyvarmap (fst c.tys) in
    let tyvarmap, ty2 = Ty.fresh_variant ~create ~tyvarmap (snd c.tys) in
    tyvarmap, { loc = c.loc; tys = ty1, ty2 }

  let print ppf { loc = loc; tys = (x, y) } =
     Format.fprintf ppf "%a =%a= %a" Ty.print x ExtLocation.print loc Ty.print y 

  let type_substitute { loc = loc; tys = (x, y) } s =
    { loc = loc ; tys = Ty.type_substitute x s, Ty.type_substitute y s }
end

(******************************************************************************)
(*                                  Scheme                                    *
 * A scheme, as used by z3ml. Each scheme constitutes a name (identifying it  *
 * uniquely for the solver), as well as a list of quanitified variables,      *
 * the type of the schemed thing, where it was schemed, and the set of        *
 * constraints implied by a reference to the scheme.                          *)
(******************************************************************************)

module SchemeConstr = struct
  type t = {
    name  : string;
    ivars : TyVar.t list;
    loc   : ExtLocation.t
  }

  type printable = t
  type tyvar_container = t

  let create loc name vars = {
    name; ivars = vars; loc
  }

  let compare s1 s2 = match ExtLocation.compare s1.loc s2.loc with
    | 0 -> lexical2 String.compare (List.compare TyVar.compare)
            (s1.name, s1.ivars) (s2.name, s2.ivars)
    | n -> n

  let tyvars {ivars;_} = TyVarSet.from_list ivars

  (* substitution isn't defined for this because we can't instantiate
     a scheme with something that isn't a variable, but a substitution
     might tell us to! *)

  let print ppf { name; ivars; loc } =
    Format.fprintf ppf "%a %a(%a)" ExtLocation.print loc String.print name 
      (List.print TyVar.print ",") ivars
end

module type ConstrSet = sig
  type t
  val empty : t
  val tyvars : t -> TyVarSet.t
  val print : Format.formatter -> t -> unit
end

module type SchemeMT = sig
  type set
  type t = {
    name  : string;
    qvars : TyVar.t list;
    ty    : Ty.t;
    cstrs : set;
    loc   : ExtLocation.t
  }
  type printable = t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
  val poly : string -> Ty.t -> set -> ExtLocation.t -> t
  val mono : string -> ExtLocation.t -> Ty.t -> t
  val instantiate : ExtLocation.t -> t -> Ty.t * SchemeConstr.t option
  val loc_of : t -> ExtLocation.t
  end

module SchemeF (CS : ConstrSet) : SchemeMT with type set = CS.t = struct
  type set = CS.t
  type t = {
    name  : string;
    qvars : TyVar.t list;
    ty    : Ty.t;
    cstrs : CS.t;
    loc   : ExtLocation.t
  }
  type printable = t

  let compare s1 s2 = String.compare s1.name s2.name

  let name_ref = ref 0;;
  let uniqify name =
    let c = !name_ref in
    incr name_ref;
    name ^ "." ^ string_of_int c

  let mono name loc ty = { 
    name = uniqify name;
    qvars = [];
    ty;
    cstrs = CS.empty;
    loc = loc
  }

  let poly name ty cstrs loc = {
    name = uniqify name;
    (* Overgeneralize. Quantify every variable appearing anywhere
       in ty or cstrs, even if it might be free in the environment.
       To fix this, 'poly' would need to also take an EzyEnv...
       therefore, the better way to fix this would be to introduce
       levels, which would be a big task since Ezy isn't using them already. *)
    qvars = TyVarSet.elements (TyVarSet.union (CS.tyvars cstrs) (Ty.tyvars ty));
    ty;
    cstrs;
    loc
  }

  let instantiate where {name;qvars;ty;loc;_} =
    let svl = List.map (fun qv -> qv, TyVar.fresh ()) qvars in
    let ivars = List.map snd svl in
    let sl = List.map (fun (qv,iv) -> qv, Ty.Var iv) svl in
    let s = TyVarSubst.from_list sl in
    let sc = SchemeConstr.{ name; ivars; loc = where } in
    let mc = match loc with
      | ExtLocation.Source _ -> Some sc
      | ExtLocation.Interface _ -> None
    in
    (Ty.type_substitute ty s, mc)

  let loc_of { loc ; _ } = loc

  let print fmt { name; qvars; cstrs; loc; ty } =
    let comma () = Format.pp_print_string fmt ", " in
    (* while printing constraints, we keep a vbox open,
      open it before the end of the first line. *)
    Format.pp_open_vbox fmt 2;
    ExtLocation.print fmt loc; Format.pp_print_char fmt ' ';
    Format.pp_print_string fmt name; Format.pp_print_char fmt '(';
    begin match qvars with
      | [] -> ()
      | (one::more) ->
        TyVar.print fmt one;
        List.iter (fun n -> comma (); TyVar.print fmt n) more
    end; Format.fprintf fmt ") : %a {" Ty.print ty;
    let print_c c =
      Format.pp_print_cut fmt ();
      CS.print fmt c in
    print_c cstrs;
    Format.pp_close_box fmt (); Format.pp_print_cut fmt ();
    Format.pp_print_char fmt '}';

end

(******************************************************************************)
(*                               AtConstrSet                                  *
 * Sets of simple constraints [AtConstr.t]. They are stored in a map by their *
 * location to make operations fast which are based on the location (and are  *
 * heavily used while constraint solving).                                    *)
(******************************************************************************)

module AtConstr = struct
  type kind = EqC of EqConstr.t | SchemeC of SchemeConstr.t
  type printable = { loc : ExtLocation.t ; kind : kind }
  type tyvar_container = printable
  type t = printable

  let from_eq eq = { loc = eq.EqConstr.loc; kind = EqC eq }
  let from_scheme s = { loc = s.SchemeConstr.loc; kind = SchemeC s }

  (* Match interface. *)
  let create = EqConstr.create

  let compare t1 t2 = match t1.kind, t2.kind with
    | EqC e1, EqC e2 -> EqConstr.compare e1 e2
    | EqC _, SchemeC _ -> -1
    | SchemeC _, EqC _ -> 1
    | SchemeC s1, SchemeC s2 -> SchemeConstr.compare s1 s2

  let print ppf t = match t.kind with
    | EqC eq -> EqConstr.print ppf eq
    | SchemeC s -> SchemeConstr.print ppf s

  let tyvars t = match t.kind with
    | EqC e -> EqConstr.tyvars e
    | SchemeC s -> SchemeConstr.tyvars s

  let fresh_variant ?(create=true) ?(tyvarmap=TyVarMap.empty) { loc; kind } = match kind with
    | SchemeC _ -> tyvarmap, { loc; kind }
    | EqC eq -> let tv, eq = EqConstr.fresh_variant ~create ~tyvarmap eq in
                tv, { loc; kind = EqC eq }

  let type_substitute t s = match t.kind with
    | SchemeC s -> { t with kind = SchemeC s }
    | EqC eq -> { t with kind = EqC (EqConstr.type_substitute eq s) }
end

module AtConstrSet = struct

  module rec SimpleAtConstrSet : sig
    include Set.S with type elt = AtConstr.t
    val fresh_variant : ?create:bool -> ?tyvarmap:(TyVar.t TyVarMap.t) -> t -> TyVar.t TyVarMap.t * t
    val type_substitute : t -> TyVarSubst.t -> t
  end = struct (* scs *)
    include Set.Make(AtConstr)
    let fresh_variant ?(create=true) ?(tyvarmap=TyVarMap.empty) scs =
      let f c (tyvarmap, sofar) =
        let tyvarmap, ty' = AtConstr.fresh_variant ~create ~tyvarmap c in
        tyvarmap, add ty' sofar in
      fold f scs (tyvarmap, empty) 
    let type_substitute scs s =
      map (AtConstr.type_substitute // s) scs 
  end
  and SimpleSchemeSet : Set.S with type elt = Scheme.t = struct
    include Set.Make(Scheme)
  end
  and MainType : sig 
    type elt = { constraints : SimpleAtConstrSet.t; schemes : SimpleSchemeSet.t }
    type t = elt ExtLocationMap.t
    val empty : t 
    val main_printer : (Format.formatter -> t -> unit) ref
    val print : Format.formatter -> t -> unit
    val make : SimpleAtConstrSet.t -> SimpleSchemeSet.t -> elt
  end = struct
    type elt = { constraints : SimpleAtConstrSet.t; schemes : SimpleSchemeSet.t }
    type t = elt ExtLocationMap.t
    let make c s = { constraints = c; schemes = s }
    let empty = ExtLocationMap.empty
    let main_printer = ref (fun _ (_:t) -> ())
    let print ppf mt = !main_printer ppf mt
  end
  and AtConstrMap : ConstrSet with type t = SimpleAtConstrSet.t ExtLocationMap.t = struct
    type t = SimpleAtConstrSet.t ExtLocationMap.t
    let empty = ExtLocationMap.empty
    let print = ExtLocationMap.print SimpleAtConstrSet.print
    let tyvars t =
      let constrs = ExtLocationMap.fold (fun _ -> SimpleAtConstrSet.union) 
                      t SimpleAtConstrSet.empty in
      SimpleAtConstrSet.fold (fun c acc -> TyVarSet.union (AtConstr.tyvars c) acc)
        constrs TyVarSet.empty
  end
  and Scheme : SchemeMT with type set = AtConstrMap.t = SchemeF(AtConstrMap)

  type at_constr_set = MainType.t
  type tyvar_container = at_constr_set
  type printable = at_constr_set
  type t = MainType.t

  let empty = ExtLocationMap.empty
  let is_empty = ExtLocationMap.is_empty

  let empty_elt = MainType.make SimpleAtConstrSet.empty SimpleSchemeSet.empty
  let add_elt_constr (MainType.{constraints;_} as e) c =
    {e with constraints = SimpleAtConstrSet.add c constraints}
  let add_elt_scheme (MainType.{schemes;_} as e) s =
    {e with schemes = SimpleSchemeSet.add s schemes}

  let cardinal (cs : t) =
    let f _ scs sofar = sofar + SimpleAtConstrSet.cardinal scs.MainType.constraints in
    ExtLocationMap.fold f cs 0

  let locations (cs : t) =
    let folder l _ sofar = ExtLocationSet.add l sofar in
    ExtLocationMap.fold folder cs ExtLocationSet.empty

  let alter (f : MainType.elt option -> MainType.elt option) loc (cs : t) : t =
    match f (ExtLocationMap.find_opt loc cs) with
    | Some elt -> ExtLocationMap.add loc elt cs
    | None -> ExtLocationMap.remove loc cs

  let alter_constraints (f : SimpleAtConstrSet.t option -> SimpleAtConstrSet.t option)
                        loc (cs : t) =
    let elt = ExtLocationMap.find_opt loc cs in
    let scs = Option.map ~f:(fun e -> e.constraints) elt in
    let v = f scs in
    match elt, v with
      | None, None -> cs
      | None, Some scs -> ExtLocationMap.add loc {empty_elt with constraints = scs} cs
      | Some e, None -> ExtLocationMap.add loc { e with constraints = SimpleAtConstrSet.empty } cs
      | Some e, Some scs -> ExtLocationMap.add loc { e with constraints = scs } cs

  let alter_schemes (f : SimpleSchemeSet.t option -> SimpleSchemeSet.t option) loc (cs : t) =
    let elt = ExtLocationMap.find_opt loc cs in
    let scs = Option.map ~f:(fun e -> e.schemes) elt in
    let v = f scs in
    match elt, v with
      | None, None -> cs
      | None, Some ss -> ExtLocationMap.add loc {empty_elt with schemes = ss} cs
      | Some e, None -> ExtLocationMap.add loc { e with schemes = SimpleSchemeSet.empty } cs
      | Some e, Some ss -> ExtLocationMap.add loc { e with schemes = ss } cs

  let add_any (cs : t) c =
    let f v = Some begin match v with
      | None -> SimpleAtConstrSet.singleton c
      | Some scs -> SimpleAtConstrSet.add c scs end
    in alter_constraints f c.loc cs

  let add (cs : t) c = add_any cs (AtConstr.from_eq c)
  let add_scheme (cs : t) s = add_any cs (AtConstr.from_scheme s)
  
  (* Inserts a completely new scheme into the constraints. This includes tracking
     the newly plotted scheme for output at the end, and also emitting a constraint
     that enforces that the scheme itself is well-typed. *)
  let add_new_scheme (cs : t) s =
    let _,c = Scheme.instantiate s.Scheme.loc s in
    let f elt =
      let existing = Option.value ~default:empty_elt elt in
      let e = match c with | None -> existing | Some c -> add_elt_constr existing (AtConstr.from_scheme c) in
      let e = add_elt_scheme e s in
      Some e
    in alter f s.loc cs

  let from_list li =
    List.fold_left add empty li

  let union (cs1 : t) (cs2 : t) =
    let elt_union e1 e2 = MainType.
      { constraints = SimpleAtConstrSet.union e1.constraints e2.constraints
      ; schemes = SimpleSchemeSet.union e1.schemes e2.schemes } in
    let folder l scs sofar =
      let aux = 
        try ExtLocationMap.find l sofar
        with Not_found ->
          empty_elt in
      ExtLocationMap.add l (elt_union scs aux) sofar in
    ExtLocationMap.fold folder cs2 cs1
  let big_union css =
    List.fold_left union empty css

  let project_by_location cs l =
    ExtLocationMap.add l (ExtLocationMap.find l cs) empty

  let partition_by_location cs l  =
    project_by_location cs l, ExtLocationMap.remove l cs

  let project_by_locations cs ls  =
    let f l sofar =
      ExtLocationMap.add l (ExtLocationMap.find l cs) sofar in
    ExtLocationSet.fold f ls empty

  let singleton ty1 loc ty2  =
    let eq = EqConstr.create ty1 loc ty2 in
    ExtLocationMap.add loc
      {empty_elt with constraints = SimpleAtConstrSet.singleton (AtConstr.from_eq eq)}
      empty

  let from_single c = ExtLocationMap.add c.AtConstr.loc
    {empty_elt with constraints = SimpleAtConstrSet.singleton c}
    empty

  (* The simplest case of creating a scheme: plot over the entire
     set of constraints (not other schemes). The constraint set is cleared,
     then the new scheme is instantiated one time.
     Beyond just getting rid of ExtLocationMap and using sets directly (probably better),
     we might also benefit on the SMT side from only plotting constraints which
     mention type variables (otherwise the constraint is like int = bool and it doesn't
     have to be in the scheme).
     This is a potential thing that might need to be optimized.
     TODO: optimize. *)
  let plot ?name ty loc (cs : t) =
    let name = Option.value ~default:"scheme" name in
    let constraint_map = ExtLocationMap.map (fun e -> e.MainType.constraints) cs in
    let scheme_map = ExtLocationMap.merge
      (fun _ _ -> function
        | None -> None
        | Some e when SimpleSchemeSet.is_empty e.schemes -> None
        | Some MainType.{schemes;_} -> Some {empty_elt with schemes})
        ExtLocationMap.empty cs in
    let scheme = Scheme.poly name ty constraint_map loc in
    add_new_scheme scheme_map scheme , scheme

  let all_constraints cs =
    let folder _ cs sofar = SimpleAtConstrSet.union cs.MainType.constraints sofar in
    ExtLocationMap.fold folder cs SimpleAtConstrSet.empty

  let all_schemes cs =
    let folder _ cs sofar = SimpleSchemeSet.union cs.MainType.schemes sofar in
    ExtLocationMap.fold folder cs SimpleSchemeSet.empty

  let tyvars cs =
    (* Don't look into the schemes, because our over-generalization means
       that the schemes never have any free variables!
       If we were to fix that, then here we would need to compute the free vars
       of the contained AtConstrSet of each scheme and then remove the qvars. *)
    let folder c sofar =
      TyVarSet.union (AtConstr.tyvars c) sofar in
    SimpleAtConstrSet.fold folder (all_constraints cs) TyVarSet.empty

  let choose_location cs =
    let folder loc cs = function
      | None -> 
          if SimpleAtConstrSet.is_empty cs.MainType.constraints
          then None
          else Some loc
      | some_loc -> some_loc in
    ExtLocationMap.fold folder cs None

  let print ppf (cs:t) =
    SimpleAtConstrSet.print ppf (all_constraints cs);
    Format.pp_print_newline ppf ();
    SimpleSchemeSet.print ppf (all_schemes cs)
  
  let () = MainType.main_printer := print

end

module Scheme = AtConstrSet.Scheme

(******************************************************************************)
(*                                  Constr                                    * 
 * A constraint between two types annotated with a set of extended locations. *)
(******************************************************************************)


module Constr = struct

  type t = {
    locs : ExtLocationSet.t ;
    tys : Ty.t * Ty.t
  }

  type printable = t

  let create ty1 ls ty2 =
    { locs = ls ; tys = (ty1, ty2) }

  let compare c1 c2 =
    lexical2 ExtLocationSet.compare (lexical Ty.compare) (c1.locs, c1.tys) (c2.locs, c2.tys)

  let print ppf { locs = _locs ; tys = (x, y) } =
    Format.fprintf ppf "%a = %a" Ty.print x Ty.print y

  let from_eq_constr { EqConstr.loc = loc; tys = (x, y) } =
    create x (ExtLocationSet.singleton loc) y
end


(******************************************************************************)
(*                                ConstrSet                                   *)
(******************************************************************************)

module ConstrSet = struct

  module ConstrSet = Set.Make(Constr)

  type t = ConstrSet.t
  type printable = t

  let empty = ConstrSet.empty
  let is_empty = ConstrSet.is_empty

  let splint ds =
    if ConstrSet.is_empty ds then
      None
    else
      let c = ConstrSet.choose ds in
      Some (c, ConstrSet.remove c ds)

  let add ds c = ConstrSet.add c ds

  let union = ConstrSet.union

  let print = ConstrSet.print

  let map = ConstrSet.map

  let from_at_constr_set cs =
    let folder c sofar = match c.AtConstr.kind with
      | EqC c -> ConstrSet.add (Constr.from_eq_constr c) sofar
      | SchemeC _ -> sofar in
    AtConstrSet.SimpleAtConstrSet.fold folder (AtConstrSet.all_constraints cs) ConstrSet.empty
end

(******************************************************************************)
(*                                  DerEnv                                    *
 * The derived environment used while unifying the constraints to keep track  *
 * of the type assignments so far (see Haack & Wells for more information).   *)
(******************************************************************************)

module DerEnv = struct

  type t = (Ty.t * ExtLocationSet.t) TyVarMap.t

  type printable = t

  let empty = TyVarMap.empty

  let substitute e tyvar ty locs =
    TyVarMap.add tyvar (ty, locs) e

  let lookup e tyvar =
    try Some (TyVarMap.find tyvar e)
    with Not_found -> None

  (** Apply a derived environment to a type. It computes app(E)(ty) (see Typed Error Slicing, 6.1)
    * for an derived environment E and a type ty.
    *)
  let rec apply_to_ty e ty =
    match ty with
      | Ty.Var tyvar ->
          begin try 
            let ty', _ = TyVarMap.find tyvar e in
            apply_to_ty e ty'
          with Not_found ->
            ty
          end
      | Ty.Constr (l, k, tys) ->
          Ty.Constr (l, k, List.map (apply_to_ty e) tys)
      | Ty.Tuple (l, tys) ->
          Ty.Tuple (l, List.map (apply_to_ty e) tys)
      | Ty.Arrow (l, tx, tx') ->
          Ty.Arrow (l, apply_to_ty e tx, apply_to_ty e tx')

  let domain env =
    TyVarMap.fold (fun tyvar _ sofar -> TyVarSet.add tyvar sofar) env TyVarSet.empty

  let print ppf e =
    let iterator tyvar (ty, _locs) =
      Format.fprintf ppf "%a: %a, " TyVar.print tyvar Ty.print ty in
    Format.pp_print_string ppf "{" ;
    TyVarMap.iter iterator e ;
    Format.pp_print_string ppf "}"

  let precede_to_tyvarsubst e (TyVarSubst.S tyvarmap) =
    let adder tyvar (ty, _) sofar =
      TyVarMap.add tyvar (apply_to_ty e ty) sofar in
    let tyvarmap = TyVarMap.fold adder e tyvarmap in
    TyVarSubst.from_tyvarmap tyvarmap

  let to_tyvarsubst e =
    let f _tyvar (ty, _) = apply_to_ty e ty in
    TyVarSubst.from_tyvarmap (TyVarMap.mapi f e)

end
