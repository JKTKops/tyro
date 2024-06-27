(*
Constraint generation for the core language.   
*)

(* Ideally, we'd use an Ast_iterator or other similar structure that makes
it easier to port to different versions of ocamlc.
   
Lucky us, compiler-libs don't provide one that takes an arbitrary input! /s
So that means we'd either need to handle or environment scoping with some
mutable global state (ewwww). It works for recording constraints because those
have neatly delimited regions where we want to `listen`. It doesn't work so well
for scopes.

So we have to write our own generators. Yay?
*)

open Parsetree
open Ztype

module StringMap = Map.Make(String)

(* In the style of THIH. *)
type ('e,'t) infer = Zenv.t -> 'e -> 't

(* delete this when impl is done *)
let pass _ = ()

let type_for_const c =
  match c with
  | Pconst_integer _ -> Ztype.Tconstr (Predef.path_int, [])
  | Pconst_char    _ -> Ztype.Tconstr (Predef.path_char, [])
  | Pconst_string  _ -> Ztype.Tconstr (Predef.path_string, [])
  | Pconst_float   _ -> Ztype.Tconstr (Predef.path_float, [])

let gen_const loc c =
  let tv = Ztype.newvar ~name:"c" () in
  let ct = type_for_const c in
  Generator.emit @@ Constraint.Equal (loc, tv, ct);
  tv

let rec gen_pat : pattern -> ztype * ztype StringMap.t
  = fun ({ppat_desc; ppat_loc; _}) ->
  match ppat_desc with
  | Ppat_constant c -> (gen_const ppat_loc c, StringMap.empty)
  | Ppat_var {txt=varname; _} ->
    let tv = Ztype.newvar ~name:"v" () in
    (tv, StringMap.singleton varname tv)
  | _ -> failwith "gen_pat: TODO"

and (gen_expr : (expression, ztype) infer)
  = fun env ({pexp_desc; pexp_loc; _}) ->
  match pexp_desc with
  | Pexp_constant c -> gen_const pexp_loc c
  | Pexp_ident {txt=lid; loc=pexp_loc} ->
    let scm = Zenv.lookup_value_by_lident lid env in
    let (ty, c) = Ztype.Scheme.instantiate pexp_loc scm in
    Generator.emit c;
    ty
  | _ -> pass env; failwith "gen_expr: TODO"

and (gen_structure_item : (structure_item, Zenv.t) infer)
  = fun env ({pstr_desc; pstr_loc}) ->
  match pstr_desc with
  | Pstr_value (rf, vbs) -> gen_value_bindings env (rf, vbs)
  | _ -> pass pstr_loc; failwith "gen_structure_item: TODO"

and (gen_value_bindings : ( (Asttypes.rec_flag * value_binding list)
                          , Zenv.t) infer)
  = fun env (rec_flag, vbs) ->
  match rec_flag with
  | Asttypes.Nonrecursive -> gen_value_bindings_nonrec env vbs
  | Asttypes.Recursive -> gen_value_bindings_rec env vbs

and (gen_value_bindings_nonrec : (value_binding list, Zenv.t) infer)
  = fun env vbs ->
  List.fold_left (fun env_sofar vb ->
    (* For this value_binding, capture the constraints emitted. 
       Each value_binding might bind many names... *)
    let (bindings, cs) = Generator.listen (fun _ -> 
      let (pat_ty, binding_map) = gen_pat vb.pvb_pat in
      (* Note that we are typechecking in env, not env_sofar; different
         bindings in the group cannot see each other! *)
      let exp_ty = gen_expr env vb.pvb_expr in
      Generator.emit (Constraint.Equal (vb.pvb_loc, pat_ty, exp_ty));
      binding_map) in
    (* Which can be generalized independently... *)
    let add_binding e (n,t) =
      Zenv.add_value n
        (Zenv.generalize ~name:n e vb.pvb_loc cs t)
        e in
    (* And each tracked in the env independently. *)
    let env_sofar' = List.fold_left add_binding env_sofar
                                    (StringMap.bindings bindings) in
    (* Now we have to emit one use of the constraints, in case the names
       are never used. We don't have to quantify and instantiate the
       constraints here; all other references to those same names will
       be inside the quanitified scheme (if there is one) which shadows them. *)
    (* Here, we simply emit the constraints directly, and this is simplest.
       But in fact, if there _were_ any schemes created by the patterns, that is,
       not every term of the patterns was constant, we could instead emit a
       Scheme constraint using one of them. See if that's faster in the future! *)
    Generator.emit_many cs;
    env_sofar') env vbs

and (gen_value_bindings_rec : (value_binding list, Zenv.t) infer)
  = fun _env _vbs -> failwith "TODO: recursive bindings"

;;
