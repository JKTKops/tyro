(*
A layer of compiler-libs Env module which allows us to utilize its scoping
information, but fall back to our own model of ocaml types
(which contains globally identified type variables).   
*)

(** A global mapping from value uids to their type schemes.
    This structure is persistent, but the Env that we are passing
    around acts as scope management. *)
let global_uid_env : Location.t Ztype.Scheme.t Types.Uid.Tbl.t
   (* Obviously we're putting a lot more than 16 things in this table
      but this is the number that compiler-libs Env uses so... ok. *)
   = Types.Uid.Tbl.create 16

(** Extract all the type schemes generated during constraint generation. *)
let get_all_schemes ()
   = List.map snd @@ Types.Uid.Tbl.to_list global_uid_env

(** A mapping from bindings in scope to Ztype.Scheme.t. The unique
    associated with the binding is also tracked. *)
type t =
  (* The Env.t from compiler-libs, which we use to maintain scoping
     information. An alternative approach would be to do a renaming pass
     before running our constraint generator, but compiler-libs do not
     provide such a thing, nor do they provide an AST structure that can
     support a renamed identifier type, so we'd have to write our own.
     That said, it might be a good idea to do that if compiler-libs' AST
     turns out to be annoying to work with.
     
     The only guarantees we make about types in this environment is
     that the ones from the initial environment are correct. We fill in
     dummy types as we generate constraints so that we can keep scoping
     information. However, those dummy types maintain accurate levels,
     which we use when generalizing types to schemes. *)
  Env.t

let empty : t = Env.empty

(** Perform an action within the bounds of a new level.
    Prefer this to manual {begin/end}_def calls as they are easy to forget. *)
let with_new_level act =
   Ctype.begin_def ();
   let r = act () in
   Ctype.end_def ();
   r

let add_value name scheme env =
   let uid = Types.Uid.mk ~current_unit:(Env.get_unit_name ()) in
   let (_id, new_env) = Env.enter_value name Types.{
      (* We don't plan on actually using this particular var with code
         from compiler libs. However, we use the same generalization algorithm
         as ocamlc, described here: https://okmij.org/ftp/ML/generalization.html.
         Maintaining levels is a critical piece of this algorithm.
         Ctype.newvar assigns the current level to val_type. *)
      val_type = Ctype.newvar ();
      (* Kind doesn't matter, we're not actually compiling the code. *)
      val_kind = Val_reg;
      (* The loc doesn't actually matter; it's in the scheme anyway. *)
      val_loc  = Ztype.Scheme.loc_of scheme;
      (* Attributes don't matter; we're not actually compiling the code. *)
      val_attributes = [];
      val_uid = uid
   } env in
   Types.Uid.Tbl.add global_uid_env uid scheme;
   new_env

(* When looking up the type of a name, if we can't find it in the typing_env,
we should try falling back to the common_env before reporting that it is
unbound. If we find a binding in the common_env, then it came from the standard
library or possibly from a module that we haven't touched yet.
Plot (I will use the verb "plot" to mean "to make into a scheme") the type
given by common_env and store that into the typing_env, then return it. *)
let lookup_value_by_lident lid env =
   let (_path, descr) = Env.find_value_by_name lid env in
   let opt_scheme = Types.Uid.Tbl.find_opt global_uid_env descr.val_uid in
   match opt_scheme with
   | None -> failwith "TODO: see comment above"
   | Some scm -> scm

let lookup_value name = lookup_value_by_lident (Longident.Lident name)

(** Generalize the given type in the given environment, at the given spot,
    with respect to the given constraints.
    For simplicity, this is currently wrong; it ignores
    the environment and over-generalizes the type. *)
let generalize ?(name="scheme")
               (_env : t)
               (loc : Location.t)
               (cs : Location.t Ztype.Constraint.t list)
               (t : Ztype.ztype) =
   (* create string sets to track seen tyvars *)
   let open Set.Make(String) in
   let open Ztype in
   let rec find_tyvars = function
      | Tvar s -> singleton s
      | Tarrow (t1, t2) -> union (find_tyvars t1) (find_tyvars t2)
      | Ttuple ts -> find_tyvars_list ts
      | Tconstr (_n, ts) -> find_tyvars_list ts
   and find_tyvars_list ts =
      List.fold_left (fun s t -> union s (find_tyvars t)) empty ts in
   Scheme.Scheme (gensym ~name ()
                 ,Scheme.Forall (elements @@ find_tyvars t)
                 ,t ,cs ,loc)

