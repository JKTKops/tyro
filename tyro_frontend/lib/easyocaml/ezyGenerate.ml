
open EzyUtils
open EzyUtils.Infix
open EzyOcamlmodules

open EzyAsttypes
open EzyAst
open EzyEnrichedAst

open EzyTypingCoreTypes
open EzyConstraints

module EzyPredef = EzyEnv.EzyPredef

let logger = new Logger.logger "generate"

(******************************************************************************
                                     Stuff
 ************************************************************************ {{{ *)

let ty_for_constant label c =
  match c with
    | Const_int _n -> EzyPredef.int_type label
    | Const_char _c -> EzyPredef.char_type label
    | Const_string _s -> EzyPredef.string_type label
    | Const_float _f -> EzyPredef.float_type label



(************************************************************************ }}} *
                                    Pattern
 ************************************************************************ {{{ *)

(* A problem to build the generated pattern: Variables can be declared in
 * several places at the same time and all these variables need the same
 * identifier.  So, I hide the mapping of known variables to identifiers 
 * in a monad:
 *)

type bound_vars = Ident.t StringMap.t
module BoundVarsMonad : sig
  include Monad.S
  val lookup: string -> Ident.t monad
  val run: 'a monad -> 'a * bound_vars
end = struct
  module Basis = struct
    type 'a t = M of (bound_vars -> 'a * bound_vars)
    let bind (M m) f =
      M (fun bound_vars ->
           let x, bound_vars = m bound_vars in
           let M k = f x in
           k bound_vars)
    let return x =
      M (fun bound_vars ->
           x, bound_vars)
  end

  include Monad.Make (Basis)

  let lookup name =
    Basis.M (
      fun bound_vars ->
         try
           StringMap.find name bound_vars, bound_vars
         with Not_found ->
           let ident = Ident.create_local name in
           ident, StringMap.add name ident bound_vars
    )

  let run (Basis.M m) =
    m StringMap.empty
end

open BoundVarsMonad.Monad_infix

(* This isn't used. ~AbelianGrape
let maybe_a_tuple label = function
  | [] -> invalid_arg "maybe_a_tuple"
  | [ty] -> ty
  | tys -> Ty.Tuple (label, tys)
*)

let env_for_ct env lid : EzyOcamlmodules.Path.t * EzyTypingCoreTypes.Ty.t list = 
  let path, ct = EzyEnv.lookup_type lid env in
  path, ct.EzyEnv.type_params

let env_for_ct_unloc env lid = env_for_ct env lid.txt

let ty_of_pat pat = pat.ppat_data.pa_ty

type pat_bindings = (Ty.t * Location.t) StringMap.t

(** A value of type [TypeAnnotation.t], i.e. a pair of types [ty1, ty2], states
  * that [ty1] has to be a subtype of [ty2].
  *)
module TypeAnnotation = struct

  type t = {
    general: Ty.t;
    loc: Location.t;
    special: Parsetree.core_type;
  }

  let create general loc special =
    { general = general; loc = loc; special = special }

  let compare ta1 ta2 =
    let to_triple ta = ta.loc, ta.general, ta.special in
    lexical3 Location.compare Ty.compare Stdlib.compare (to_triple ta1) (to_triple ta2)

  type printable = t
  let print ppf ta =
    Format.fprintf ppf "%a >= %a" Ty.print ta.general EzyAst.print_core_type ta.special

  let valid env s ta =

    let general =
      let general = TyVarSubst.apply_to_ty s ta.general in
      EzyEnv.full_expand_type env general in

    let special =
      let _, special = EzyEnrichedAst.import_core_type true (env_for_ct_unloc env) StringMap.empty ta.special in
      EzyEnv.full_expand_type env special in

    logger#trace "Test validation %a >= %a (was %a >= %a)" 
      Ty.print general Ty.print special
      Ty.print ta.general EzyAst.print_core_type ta.special ;

    if Ty.valid_instantiation general special then
      EzyErrors.ErrorSet.empty
    else begin
      logger#debug "No validation for %a >= %a" Ty.print general Ty.print special ;
      EzyErrors.ErrorSet.singleton (ta.loc, EzyErrors.No_subtype (general, ta.special))
    end
end

module PostProcess = struct

  module TypeAnnotations = struct
    include Set.Make (TypeAnnotation)
    let valid env s tas =
      let aux ta errs =
        EzyErrors.ErrorSet.union (TypeAnnotation.valid env s ta) errs in
      fold aux tas EzyErrors.ErrorSet.empty
  end

  open EzyErrors

  type t =
      {
        heavies: HeavyErrorSet.t ;
        errors: ErrorSet.t ;
        type_annotations: TypeAnnotations.t ;
      }

  let empty = {
    heavies = HeavyErrorSet.empty ;
    errors = ErrorSet.empty ;
    type_annotations = TypeAnnotations.empty ;
  }

  let type_annotations li =
    { empty with type_annotations = TypeAnnotations.from_list li }

  let error loc err =
    { empty with errors = ErrorSet.singleton (loc, err) }

  let errors loc_errs =
    { empty with errors = ErrorSet.from_list loc_errs }

  let heavies loc_herrs =
    { empty with heavies = HeavyErrorSet.from_list loc_herrs }

  let has_heavies pp =
    not (HeavyErrorSet.is_empty pp.heavies)

  let union pp1 pp2 =
    {
      type_annotations = TypeAnnotations.union pp1.type_annotations pp2.type_annotations ;
      errors = ErrorSet.union pp1.errors pp2.errors ;
      heavies = HeavyErrorSet.union pp1.heavies pp2.heavies ;
    }
  let big_union pps =
    List.fold_left union empty pps
end

let split4 ls =
  let rec aux acc1 acc2 acc3 acc4 = function
    | [] ->
        List.rev acc1, List.rev acc2, List.rev acc3, List.rev acc4
    | (x1, x2, x3, x4) :: rem ->
        aux (x1 :: acc1) (x2 :: acc2) (x3 :: acc3) (x4 :: acc4) rem in
  aux [] [] [] [] ls

let null_pat = {
  EzyAst.ppat_desc = Ppat_any ;
  ppat_loc = Location.none ;
  ppat_data = { pa_ty = Ty.Var TyVar.none ; pa_ident = EzyEnv.no_ident; pa_env = EzyEnv.empty } ;
}

(* Monadic implementation of contraint generation for patterns *)
let rec m_for_pattern: imported_pattern -> EzyEnv.t -> (generated_pattern * AtConstrSet.t * pat_bindings * PostProcess.t) monad =
  fun pat env ->
    let module M = BoundVarsMonad in
    (* Unfortunatly, every generated patterns needs an ident. For all but Ppat_var I choose Ident.none *)
    let annotation ?(ident=EzyEnv.no_ident) ty = { pa_ty = ty; pa_ident = ident; pa_env = env } in
    let loc = pat.ppat_loc in
    let eloc = ExtLocation.Source loc in
    let pairwise_disjoint_heavies loc bs =
      let severals =
        let collect x y sofar = StringSet.union (StringSet.inter x y) sofar in
        List.fold_pairwise collect StringSet.empty (List.map StringMap.keys (bs:pat_bindings list)) in
      if not (StringSet.is_empty severals) then
        let ls = StringSet.elements severals in
        PostProcess.heavies [loc, EzyErrors.Several_bindings ls]
      else
        PostProcess.empty in
    match pat.ppat_desc with

      | Ppat_dots _ ->  raise (InternalDotsError "m_for_pattern: there is no constraint generation for dots")

      | Ppat_any ->
          let a = Ty.fresh_var () in
          let pat' = {
            ppat_data = annotation a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_any ;
          } in
          M.return (pat', AtConstrSet.empty, StringMap.empty, PostProcess.empty)

      | Ppat_var name ->
          let a = Ty.fresh_var () in
          M.lookup name.nm_name >>= fun ident ->
          let pat' = {
            ppat_data = annotation ~ident a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_var { nm_name = name.nm_name; nm_loc = name.nm_loc; nm_data = ident } ;
          } in
          let b : pat_bindings = StringMap.singleton name.nm_name (a, loc) in
          M.return (pat', AtConstrSet.empty, b, PostProcess.empty)

      | Ppat_constant c ->
          let a = Ty.fresh_var () in
          let pat' = {
            ppat_data = annotation a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_constant c ;
          } in
          let cs = AtConstrSet.singleton (ty_for_constant eloc c) eloc a in
          M.return (pat', cs, StringMap.empty, PostProcess.empty)

      | Ppat_or (p1, p2) ->
          m_for_pattern p1 env >>= fun (enr_p1, cs1, b1, pp1) ->
          m_for_pattern p2 env >>= fun (enr_p2, cs2, b2, pp2) ->
          let a = Ty.fresh_var () in
          let pat' = {
            ppat_data = annotation a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_or (enr_p1, enr_p2) ;
          } in
          if StringSet.compare (StringMap.keys b1) (StringMap.keys b2) = 0 then
            let f v (b, cs1', cs2') =
              let a_id = Ty.fresh_var () in
              let b' : pat_bindings = StringMap.add v (a_id, loc) b in (*
                FIXME loc is not exact enough. It should be
                [snd (StringMap.find v b1) + snd (StringMap.find v b2)].  *)
              let cs1' =
                let ty, l' = StringMap.find v b1 in
                AtConstrSet.add cs1' (AtConstr.create a_id (ExtLocation.Source l') ty) in
              let cs2' =
                let ty, l' = StringMap.find v b2 in
                AtConstrSet.add cs2' (AtConstr.create a_id (ExtLocation.Source l') ty) in
              b', cs1', cs2' in
            let (b:pat_bindings), cs1', cs2' = StringSet.fold f (StringMap.keys b1) (StringMap.empty, cs1, cs2) in
            let cs0 = AtConstrSet.from_list [
              AtConstr.create a eloc enr_p1.ppat_data.pa_ty ;
              AtConstr.create a eloc enr_p2.ppat_data.pa_ty
            ] in
            let cs = List.reduce AtConstrSet.union [cs0; cs1'; cs2'] in
            let pp = PostProcess.union pp1 pp2 in
            M.return (pat', cs, b, pp)
          else
            let left_bs = StringMap.keys b1 in
            let right_bs = StringMap.keys b2 in
            let only_left = StringSet.elements (StringSet.diff left_bs right_bs) in
            let only_right = StringSet.elements (StringSet.diff right_bs left_bs) in
            let pp = PostProcess.heavies [loc, EzyErrors.Different_bindings (only_left, only_right)] in
            M.return (pat', AtConstrSet.empty, StringMap.empty, pp)

      | Ppat_alias (pat, name) ->
          m_for_pattern pat env >>= fun (enr_pat, cs, b, pp) ->
          M.lookup name.nm_name >>= fun ident ->
          let a = Ty.fresh_var () in
          let name = {
            nm_name = name.nm_name ;
            nm_loc = name.nm_loc ;
            nm_data = ident ;
          } in
          let b' = StringMap.add name.nm_name (ty_of_pat enr_pat, loc) b in
          let pat' = {
            ppat_data = annotation a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_alias (enr_pat, name) ;
          } in
          let cs' = AtConstrSet.add cs (AtConstr.create a eloc (ty_of_pat enr_pat)) in
          M.return (pat', cs', b', pp)

      | Ppat_tuple pats ->
          M.accumulate (List.map (m_for_pattern // env) pats) >>| split4 >>=
          fun (enr_pats, css, bs, pps) ->
          let pp0 = pairwise_disjoint_heavies loc bs in

          let a = Ty.fresh_var () in
          let cs0 = 
            let ty_tuple = Ty.Tuple (eloc, List.map (fun pat -> pat.ppat_data.pa_ty) enr_pats) in
            AtConstrSet.singleton a eloc ty_tuple in
          let pat' = {
            ppat_data = annotation a;
            ppat_loc = loc;
            ppat_desc = Ppat_tuple enr_pats
          } in
          let cs = List.fold_left AtConstrSet.union cs0 css in
          let b : pat_bindings = List.fold_left StringMap.update StringMap.empty bs in
          let pp = List.reduce PostProcess.union (pp0 :: pps) in
          M.return (pat', cs, b, pp)

      | Ppat_construct (ctor, opt_pat, explicit_arity) ->
          let a = Ty.fresh_var () in
          begin try
            let _, cd = EzyEnv.lookup_ctor ctor.lid_name env in
            let expected_arg_count = List.length cd.EzyEnv.ctor_args in
            let pats, flag =
              match opt_pat with
                | None ->
                    [], false
                | Some {ppat_desc = Ppat_tuple spl;_} when explicit_arity ->
                    spl, true
                | Some {ppat_desc = Ppat_tuple spl;_} when expected_arg_count > 1 ->
                    spl, true
                | Some({ppat_desc = Ppat_any;_} as sp) when expected_arg_count > 1 ->
                    List.init (fun _ -> sp) expected_arg_count, true
                | Some sp ->
                    [sp], false in
            M.accumulate (List.map (m_for_pattern // env) pats) >>| split4 >>=
            fun (enr_pats, css, bs, pps) ->
              let pp0 = pairwise_disjoint_heavies loc bs in
              begin try
                let tyvarmap, ty'_r = T2.map2 ~f:(Ty.set_label // eloc) (Ty.fresh_variant cd.EzyEnv.ctor_result) in
                let _tyvarmap, tys' = Ty.fresh_variants ~tyvarmap cd.EzyEnv.ctor_args in
                let cs0 =
                  let aux ty' enr_pat =
                    AtConstr.create ty' eloc (ty_of_pat enr_pat) in
                  AtConstrSet.from_list (
                    AtConstr.create a eloc ty'_r ::
                    List.map2 aux tys' enr_pats
                  ) in
                let ctor' = { lid_name = ctor.lid_name; lid_data = EzyEnv.path_of_tag cd.EzyEnv.ctor_tag } in
                let desc' =
                  if flag then 
                    let pa = { pa_ty = Ty.Tuple (ExtLocation.none, List.map ty_of_pat enr_pats); pa_env = env; pa_ident = EzyEnv.no_ident } in
                    let tuple = { ppat_desc = Ppat_tuple enr_pats; ppat_loc = Location.none; ppat_data = pa } in
                    Ppat_construct (ctor', Some tuple, flag) ;
                  else
                    match enr_pats, flag with
                      | [], _ -> Ppat_construct (ctor', None, flag)
                      | [pat], false -> Ppat_construct (ctor', Some pat, flag)
                      | _ -> assert false  in
                let pat' = {
                  ppat_data = annotation a ;
                  ppat_loc = loc ;
                  ppat_desc = desc' ;
                } in
                let b = List.fold_left StringMap.update StringMap.empty bs in
                let pp = PostProcess.big_union (pp0 :: pps) in
                M.return (pat', AtConstrSet.big_union (cs0 :: css), b, pp)
              with Invalid_argument _ -> (* invalid argument to List.map2 *)
                let pp = PostProcess.heavies [loc, EzyErrors.Invalid_variant_construction (ctor.lid_name, expected_arg_count, List.length pats)] in
                let b = List.fold_left StringMap.update StringMap.empty bs in
                M.return (null_pat, AtConstrSet.big_union css, b, PostProcess.big_union (pp :: pps))
              end
          with Not_found -> 
            let pp0 = PostProcess.heavies [loc, EzyErrors.Unknown_variant ctor.lid_name] in
            match opt_pat with
              | None ->
                  M.return (null_pat, AtConstrSet.empty, StringMap.empty, pp0)
              | Some pat ->
                  m_for_pattern pat env >>=
                  fun (_, cs, b, pp) ->
                  M.return (null_pat, cs, b, PostProcess.union pp0 pp)
          end

      (* FIXME: AbelianGrape:
         We really want this to work for the purpose of being practical and being able to 
         run the code on all student submissions (esp. those to HW5, where use of record
         patterns by students was not uncommon). However, the existing minerrloc artifact
         doesn't support this case either, so for purposes where we just want to compare
         against them... supporting this would be wasted effort. I'd guess something
         in the existing commented-out implementation doesn't work, but I haven't checked. *)
      | Ppat_record _fs -> not_implemented "EzyGenerate.for_pattern Ppat_record" (*

          let apply_to_field tyvarmap (f, pat) =
            m_for_pattern pat env >>= fun (epat, cs, b, pp) ->
            let fd = EzyEnv.lookup_field f.lid_name env in
            let f' = { lid_name = f.lid_name; lid_data = fd.EzyEnv.fld_path } in
            M.return ((f', epat), cs, b, pp) in

          M.accumulate (snd $ List.foldmap apply_to_field TyVarMap.empty fs) >>| split4 >>=
          fun (field_enr_pats, css, bs, pps) ->
          let pp0 = pairwise_disjoint_heavies loc bs in

          let a = Ty.fresh_var () in

          let cs0 =
            let aux (f, { ppat_data = { pa_ty = ty } }) =
              let fd = EzyEnv.lookup_field f.lid_name env in
              AtConstrSet.from_list [
                AtConstr.create a eloc (Ty.set_label fd.EzyEnv.fld_result eloc) ;
                AtConstr.create ty eloc fd.EzyEnv.fld_arg ;
              ] in
            let cs' = List.map aux field_enr_pats in
            List.fold_left AtConstrSet.union AtConstrSet.empty cs' in
          let pat' = {
            ppat_data = annotation a ;
            ppat_loc = loc ;
            ppat_desc = Ppat_record field_enr_pats ;
          } in
          let cs = List.fold_left AtConstrSet.union cs0 css in
          let b = List.fold_left StringMap.update StringMap.empty bs in
          let pp = List.reduce PostProcess.union (pp0 :: pps) in
          M.return (pat', cs, b, pp)
                                                                                 *)

      | Ppat_constraint (p, ct) ->
          m_for_pattern p env >>= fun (enr_pat, cs0, b, pp0) ->
          begin try
            (* AbelianGrape: simplified greatly in exchange for not distinguishing the overall
              pattern location from the location of the constraint type.
              Also, pattern constraints are made hard, because Wies et. al. did that. *)
            (* let eloc' = ExtLocation.Source ct.Parsetree.ptyp_loc in *)
            let ty = ty_of_pat enr_pat in
            let _, ty' = EzyEnrichedAst.import_core_type true (env_for_ct_unloc env) StringMap.empty ct in
            let cs1 = AtConstrSet.from_list [
              AtConstr.create ty eloc ty' ;
              (* All of these are redundant. ~AbelianGrape *)
              (* AtConstr.create a2 eloc ty ;
              AtConstr.create a3 eloc' ty' ;
              AtConstr.create a1 eloc a3 ; *)
            ] in
            let pp1 = PostProcess.type_annotations [TypeAnnotation.create ty loc ct] in
            let pat' = {
              ppat_data = annotation ty ;
              ppat_loc = loc ;
              ppat_desc = Ppat_constraint (enr_pat, ct) ;
            } in
            make_loc_hard eloc;
            M.return (pat', AtConstrSet.union cs0 cs1, b, PostProcess.union pp0 pp1)
          with
            | EzyEnrichedAst.Invalid_type_constructor (lid, n, m) ->
                M.return (null_pat, AtConstrSet.empty, b, PostProcess.heavies [loc, EzyErrors.Invalid_type_constructor (lid, n, m)])
            | EzyEnrichedAst.Unbound_type_constructor lid ->
                M.return (null_pat, AtConstrSet.empty, b, PostProcess.heavies [loc, EzyErrors.Unbound_type_constructor lid])
          end
         

type pattern_binding = (Ty.t * Ident.t * Location.t) StringMap.t

let for_pattern pat env: EzyEnrichedAst.generated_pattern * EzyConstraints.AtConstrSet.t * PostProcess.t * pattern_binding =
  (* type pat_bindings = (Ty.t * Location.t) StringMap.t *)
  (* m_for_pattern: imported_pattern -> EzyEnv.t -> (generated_pattern * AtConstrSet.t * pat_bindings * PostProcess.t) monad *)
  let (enr_pat, cs, b, pp), bvs = BoundVarsMonad.run (m_for_pattern pat env) in
  let print_binding ppf (ty, _loc) = Ty.print ppf ty in
  let combine_patbind_boundvar name (ty, loc) sofar =
    let entry = ty, StringMap.find name bvs, loc in
    StringMap.add name entry sofar in
  let resulting_binding =
    StringMap.fold combine_patbind_boundvar b StringMap.empty in
  logger#debug "for pattern at %a@ %a@ @[<1>(bound: %a,@ ty:@ %a,@ cs: %a@])"
    Location.print pat.ppat_loc
    (EzyAst.print_pat ()) enr_pat
    (StringMap.print print_binding) b
    Ty.print enr_pat.ppat_data.pa_ty
    AtConstrSet.print cs ;
  enr_pat, cs, pp, resulting_binding

(************************************************************************ }}} *
                                  Expressions
 ************************************************************************ {{{ *)

(* Some auxilaries for expressions {{{ *)

let ty_of_expr (expr: generated_expression) = expr.pexp_data.ea_ty

let rec binding_for_exp exp =
  let check_list li =
    let is_poly exp = binding_for_exp exp = EzyEnv.Poly in
    if List.for_all is_poly li
    then EzyEnv.Poly
    else EzyEnv.Mono in
  (* Check a group of rules, associated with the expression they are
     being matched again. Like check_list but discovers what the subexpressions
     that need to be inspected are. ~AbelianGrape *)
  let check_rules exp rs =
    let subexps r =
      match r.rule_guard with
      | None -> [r.rule_exp]
      | Some g -> [g; r.rule_exp] in
    check_list @@ exp :: List.concat_map subexps rs
  in
  match exp.pexp_desc with
    | Pexp_function _
    | Pexp_ident _
    | Pexp_constant _
    | Pexp_construct (_, None, _)
    | Pexp_assertfalse 
      -> EzyEnv.Poly

    | Pexp_record (fs, opt) ->
        let exps = List.map snd fs in
        begin match opt with
          | Some exp -> 
              check_list (exp :: exps)
          | None ->
              check_list exps
        end

    | Pexp_tuple exps ->
        check_list exps

    | Pexp_construct (_, Some exp, _)
    | Pexp_let (_, exp)
    | Pexp_letrec (_, exp)
    | Pexp_assert exp
    | Pexp_constraint (exp, _)
    | Pexp_field (exp, _)
    | Pexp_ifthenelse (_, exp, None)
    | Pexp_sequence (_, exp) ->
        binding_for_exp exp
    | Pexp_ifthenelse (_, exp1, Some exp2) ->
        check_list [exp1; exp2]
    | Pexp_try (exp1, exp2) ->
        check_rules exp1 exp2

    | Pexp_apply _
    | Pexp_match _
    | Pexp_setfield _
    | Pexp_while _
    | Pexp_for _
      -> EzyEnv.Mono
    | Pexp_dots _ -> raise (InternalDotsError "binding_for_exp: not implemented for dots")

(* This isn't used (i'm not even sure what it's supposed to do). ~AbelianGrape
let rec arrow_of_list ~result = function
  | [], [] -> result
  | loc :: locs, ty :: tys ->
      let label = ExtLocation.Source loc in
      Ty.Arrow (label, ty, arrow_of_list ~result (locs, tys))
  | _ -> invalid_arg "arrow_of_list"
*)

(* loc here is the location of the let ... and ... and ... (in) which caused this. *)
let extend_env_by_bvs env b binding loc cs =
  let loc = ExtLocation.Source loc in
  let f name (ty, ident, bv_loc) (out_cs,env) =
    let bv_loc = ExtLocation.Source bv_loc in
    let cs', s = match binding with
      | EzyEnv.Poly -> (* logger#trace "poly"; *)AtConstrSet.plot ~name ty loc cs
      | EzyEnv.Mono -> (* logger#trace "mono"; *)cs, Scheme.mono name loc ty
    in
    (* logger#trace "extending: %a" AtConstrSet.print cs'; *)
    let vd = EzyEnv.{
      val_kind = Types.Val_reg ;
      val_binding = binding ; 
      val_scheme = s ;
      val_loc = bv_loc ;
    } in
    (AtConstrSet.union cs' out_cs, EzyEnv.add_value ident vd env) in
  StringMap.fold f b (AtConstrSet.empty, env)

(* }}} *)           

(* For_expr {{{ *)

let null_exp = {
  pexp_desc = Pexp_construct ({ lid_data = Path.Pident EzyEnv.no_ident; lid_name = Longident.Lident ""}, None, false) ;
  pexp_loc = Location.none ;
  pexp_data = { ea_ty = Ty.Var TyVar.none; ea_env = EzyEnv.empty } ;
}

(* Auxiliary to collect the bindings in a `let ... and ... and ... (in)' expression *)
let rec collect_bindings env loc bindings =
  let aux (cs_sofar, pp_sofar, vars_sofar, env_sofar) (pat, expr) =
    let enr_pat, cs0, pp0, b = for_pattern pat env in
    let b_keys = StringMap.keys b in
    let b_key_inter = StringSet.inter b_keys vars_sofar in
    let enr_expr, cs1, pp1 = for_expr expr env in
    let pp2 =
      if StringSet.is_empty b_key_inter then
        PostProcess.empty
      else
        let heavy = EzyErrors.Several_bindings (StringSet.elements b_key_inter) in
        PostProcess.heavies [loc, heavy] in
    let csx = AtConstrSet.singleton (ty_of_pat enr_pat) (ExtLocation.Source loc) (ty_of_expr enr_expr) in
    let cs = List.reduce AtConstrSet.union [csx; cs0; cs1] in
    (* Plots here include the ty(pat) ~ ty(expr) constraint ~AbelianGrape *)
    (* Afterwards, 'cs' contains only the (scheme) constraints and schemes created
       by plotting over the previous 'cs' for each binding in the pattern. *)
    let cs, env' = extend_env_by_bvs env_sofar b (binding_for_exp expr) loc cs in
    let sofar =
      List.reduce AtConstrSet.union [cs; cs_sofar],
      List.reduce PostProcess.union [pp0; pp1; pp2; pp_sofar],
      StringSet.union vars_sofar b_keys,
      env' in
    sofar, (enr_pat, enr_expr) in
  let (cs, pp, _, env), rules = List.foldmap aux (AtConstrSet.empty, PostProcess.empty, StringSet.empty, env) bindings in
  (cs, pp, env), rules

(* Auxiliary to collect the bindings in a `let rec ... and ... and ... (in)' expression *)
and collect_rec_bindings env loc bindings =
  let eloc = ExtLocation.Source loc in
  (* bind [var] in [env] to a fresh, monomorphic type variable *)
  let add_mono_binding env (var, expr) =
    let ty = (* use annotated type if present *)
      match expr.pexp_desc with
        | Pexp_constraint(_, ct) ->
            snd (EzyEnrichedAst.import_core_type true (env_for_ct_unloc env) StringMap.empty ct)
        | _ -> Ty.fresh_var () in
    let vd = EzyEnv.{
      val_kind = Types.Val_reg ;
      val_binding = EzyEnv.Mono ;
      val_scheme = Scheme.mono var.nm_name eloc ty;
      val_loc = ExtLocation.Source var.nm_loc ;
    } in
    let ident, env = EzyEnv.enter_value var.nm_name vd env in
    env, (var, ident, ty, expr) in
  let env', bindings' =
    List.foldmap add_mono_binding env bindings in
  let process_binding (cs_sofar, pp_sofar, vars_sofar, env_sofar) (var, ident, ty, expr) =
    let enr_expr, cs, pp = for_expr expr env' in
    let cs = AtConstrSet.add cs (AtConstr.create ty eloc (ty_of_expr enr_expr)) in
    let binding = binding_for_exp expr in
    let cs,scm = match binding with
      | EzyEnv.Mono -> cs, Scheme.mono var.nm_name eloc ty
      | EzyEnv.Poly -> AtConstrSet.plot ~name:var.nm_name ty eloc cs in
    let vd = EzyEnv.{
      val_kind = Types.Val_reg ;
      val_binding = binding ;
      val_scheme = scm ;
      val_loc = ExtLocation.Source var.nm_loc ;
    } in
    let pp' =
      if StringSet.mem var.nm_name vars_sofar then
        PostProcess.heavies [loc, EzyErrors.Several_bindings [var.nm_name]]
      else
        PostProcess.empty in
    let sofar =
      AtConstrSet.union cs cs_sofar,
      List.reduce PostProcess.union [pp; pp'; pp_sofar],
      StringSet.add var.nm_name vars_sofar,
      EzyEnv.add_value ident vd env_sofar in
    sofar, ({ nm_name = var.nm_name; nm_loc = var.nm_loc; nm_data = ident}, enr_expr) in
  let (cs, pp, _, env'), enr_bindings = 
    List.foldmap process_binding (AtConstrSet.empty, PostProcess.empty, StringSet.empty, env) bindings' in
  (cs, pp, env'), enr_bindings


and for_expr: imported_expression -> EzyEnv.t -> generated_expression * AtConstrSet.t * PostProcess.t =
  fun expr env ->

    let loc = expr.pexp_loc in
    let eloc = ExtLocation.Source loc in

    let build_exp ty ?(env=env) expr =
      { pexp_loc = loc; pexp_desc = expr; pexp_data = { ea_ty = ty; ea_env = env } } in

    let enr_expr, cs, us = match expr.pexp_desc with

      | Pexp_dots _ ->  raise (InternalDotsError "for_expr: not implemented for dots")

      | Pexp_ident x ->
          begin try
            let path, vd = EzyEnv.lookup_value x.lid_name env in
            let val_scm =
              match vd.EzyEnv.val_loc with
                | ExtLocation.Source _ ->
                    vd.EzyEnv.val_scheme
                | ExtLocation.Interface _ -> 
                    let scm = vd.EzyEnv.val_scheme in
                    let ty = Ty.set_label scm.ty eloc in
                    {scm with ty} in
            let x' = { lid_name = x.lid_name; lid_data = path } in
            match vd.EzyEnv.val_binding with
              | EzyEnv.Poly ->
                  (* All this stuff changes with Schemes... ~AbelianGrape
                  let a = Ty.fresh_var () in
                  let ax = Ty.fresh_var () in
                  let tyvarmap, ty' = Ty.fresh_variant val_ty in
                  let _tyvarmap, cs' = AtConstrSet.fresh_variant ~tyvarmap vd.EzyEnv.val_constraints in
                  let cs'' = AtConstrSet.from_list [
                    AtConstr.create ax eloc a ;
                    AtConstr.create ty' vd.EzyEnv.val_loc ax ;
                  ] in
                  let cs = AtConstrSet.union cs' cs'' in
                  logger#trace "Polymorph: %a, %a -> %a, %a"
                    Ty.print val_ty AtConstrSet.print vd.EzyEnv.val_constraints
                    Ty.print ty'  AtConstrSet.print cs' ;
                  build_exp a (Pexp_ident x'), cs, PostProcess.empty
                  *)
                  let a = Ty.fresh_var () in
                  let ty,constr = Scheme.instantiate eloc val_scm in
                  let () = logger#trace "Instantiate: %a ::\n%a -> %a, %a"
                    Ty.print val_scm.ty Scheme.print val_scm
                    Ty.print ty (Option.print SchemeConstr.print) constr in
                  let cs0 = match constr with
                    | None -> AtConstrSet.empty
                    | Some c -> AtConstrSet.from_single (AtConstr.from_scheme c) in
                  let cs1 = AtConstrSet.singleton a eloc ty in
                  build_exp a (Pexp_ident x'), AtConstrSet.union cs0 cs1, PostProcess.empty
              | EzyEnv.Mono ->
                  let a = Ty.fresh_var () in
                  let ty = val_scm.ty in
                  (* Creating two constraints here seems redundant, but maybe
                     I'm missing something about the one @val_loc? ~AbelianGrape
                  let cs = AtConstrSet.from_list [
                    AtConstr.create a eloc ax ;
                    AtConstr.create ax vd.EzyEnv.val_loc val_ty ;
                  ] in
                  *)
                  let cs = AtConstrSet.singleton a eloc ty in
                  build_exp a (Pexp_ident x'), cs, PostProcess.empty
          with Not_found ->
            let a = Ty.fresh_var () in
            let new_ident = Pexp_ident { lid_name = x.lid_name; lid_data = Path.Pident EzyEnv.no_ident } in
            let pp = PostProcess.error loc (EzyErrors.Unbound_variable x.lid_name) in
            build_exp a new_ident, AtConstrSet.empty, pp
          end

      | Pexp_constant c ->
          let a = Ty.fresh_var () in
          let desc = Pexp_constant c in
          let cs = AtConstrSet.singleton (ty_for_constant eloc c) eloc a in
          build_exp a desc, cs, PostProcess.empty

      | Pexp_function rules ->
          let a = Ty.fresh_var () in
          let enr_rules, ty_p, ty_e, cs0, pp = for_rules eloc rules env in
          let cs1 = AtConstrSet.singleton a eloc (Ty.Arrow (eloc, ty_p, ty_e)) in
          let cs = AtConstrSet.union cs0 cs1 in
          build_exp a (Pexp_function enr_rules), cs, pp

      | Pexp_apply (exp1, exp2) ->
        (* Eliminated redundant type variables (match the paper) ~AbelianGrape
          let a = Ty.fresh_var () in
          let a1 = Ty.fresh_var () in
          let a2 = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp1) eloc (Ty.Arrow (eloc, a1, a2)) ;
            AtConstr.create (ty_of_expr enr_exp2) eloc a1 ;
            AtConstr.create a eloc a2 ;
          ] in
          *)
          (* Make partial application locations hard. So if the exp1 is also an apply, it's a partial application.*)
          (* Wies et.al. do this because "programmers would not find reports at these ranges useful." *)
          begin match exp1.pexp_desc with
          | Pexp_apply (_, _) -> make_loc_hard (ExtLocation.Source exp1.pexp_loc)
          | _ -> ()
          end;
          let g = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          let a,b = ty_of_expr enr_exp1, ty_of_expr enr_exp2 in
          let cs0 = AtConstrSet.singleton a eloc (Ty.Arrow (eloc, b, g)) in
          build_exp g (Pexp_apply (enr_exp1, enr_exp2)), AtConstrSet.big_union [cs0; cs1; cs2], PostProcess.union pp1 pp2

      | Pexp_let (bindings, body) ->
          let a = Ty.fresh_var () in (* This is gamma in the paper. ~AbelianGrape *)
          (* collect_bindings creates all necessary plots etc, and the resulting
             'cs' usually contains only one constraint+scheme or less per binding,
             and nothing else. *)
          let (cs, pp, env'), enr_bindings = collect_bindings env loc bindings in
          let enr_body, csm, ppm = for_expr body env' in
          let csx = AtConstrSet.singleton a eloc (ty_of_expr enr_body) in
          build_exp a (Pexp_let (enr_bindings, enr_body)), List.reduce AtConstrSet.union [cs; csx; csm], PostProcess.union pp ppm

      | Pexp_letrec (bindings, body) ->
          let a = Ty.fresh_var () in (* See the comments on Pexp_let. ~AbelianGrape *)
          let (cs, pp, env'), enr_bindings = collect_rec_bindings env loc bindings in
          let enr_body, csm, ppm = for_expr body env' in
          let csx = AtConstrSet.singleton a eloc (ty_of_expr enr_body) in
          build_exp a (Pexp_letrec (enr_bindings, enr_body)), List.reduce AtConstrSet.union [cs; csm; csx], PostProcess.union pp ppm

      | Pexp_match (exp, rules) ->
          let enr_exp, cs1, us1 = for_expr exp env in
          let enr_rules, ty_p, ty_e, cs2, us2 = for_rules eloc rules env in
          let a = Ty.fresh_var () in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp) eloc ty_p ;
            AtConstr.create a eloc ty_e ;
          ] in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          let us = PostProcess.union us1 us2 in
          build_exp a (Pexp_match (enr_exp, enr_rules)), cs, us

      | Pexp_construct (ctor, sarg, explicit_arity) ->
          let a = Ty.fresh_var () in
          begin try
            let _, cd = EzyEnv.lookup_ctor ctor.lid_name env in
            let expected_arg_count = List.length cd.EzyEnv.ctor_args in
            let sargs, flag =
              match sarg with
                | None -> [], false
                | Some {pexp_desc = Pexp_tuple sel;_} when explicit_arity -> sel, true
                | Some {pexp_desc = Pexp_tuple sel;_} when expected_arg_count > 1 -> sel, true
                | Some se -> [se], false in
            let enr_exps, css, uss = List.split3 (List.map (for_expr // env) sargs) in
            if List.length sargs = expected_arg_count then
              let tyvarmap, ty'_r = Ty.fresh_variant cd.EzyEnv.ctor_result in
              let _tyvarmap, tys' = Ty.fresh_variants ~tyvarmap cd.EzyEnv.ctor_args in
              let ty'_r = Ty.set_label ty'_r eloc in
              let tys' = List.map (Ty.set_label // eloc) tys' in
              let gen_constr ty' enr_exp =
                AtConstr.create ty' eloc (ty_of_expr enr_exp) in
              let cs0 = AtConstrSet.from_list (
                AtConstr.create a eloc ty'_r ::
                List.map2 gen_constr tys' enr_exps
              ) in
              let ctor' = { lid_name = ctor.lid_name; lid_data = EzyEnv.path_of_tag cd.EzyEnv.ctor_tag } in
              let cs = AtConstrSet.big_union (cs0 :: css) in
              let us = PostProcess.big_union uss in
              if flag then
                let ea = { ea_ty = Ty.Tuple (ExtLocation.none, List.map ty_of_expr enr_exps); ea_env = env } in
                let tuple = { pexp_desc = Pexp_tuple enr_exps; pexp_data = ea; pexp_loc = Location.none } in
                build_exp a (Pexp_construct (ctor', Some tuple, flag)), cs, us
              else
                let exp =
                  match enr_exps with
                    | [] -> None
                    | [exp] -> Some exp
                    | _ -> assert false in
                build_exp a (Pexp_construct (ctor', exp, flag)), cs, us
            else
              let pp = PostProcess.heavies [loc, EzyErrors.Invalid_variant_construction (ctor.lid_name, expected_arg_count, List.length sargs)] in
              null_exp, AtConstrSet.empty, PostProcess.big_union (pp :: uss)
          with Not_found ->
            let pp0 = PostProcess.heavies [loc, EzyErrors.Unknown_variant ctor.lid_name] in
            let _cs, pp = (* get pp for errors, I assume, but ignore cs. ~AbelianGrape *)
              match sarg with
                | None -> AtConstrSet.empty, PostProcess.empty
                | Some expr -> T3.beside1 (for_expr expr env) in
            null_exp, AtConstrSet.empty, PostProcess.union pp0 pp
          end

      | Pexp_tuple exps ->
          let a = Ty.fresh_var () in
          let enr_exps, css, uss = List.split3 (List.map (for_expr // env) exps) in
          let cs0 = AtConstrSet.singleton a eloc (Ty.Tuple (eloc, List.map ty_of_expr enr_exps)) in
          let cs = List.fold_left AtConstrSet.union cs0 css in
          let us = List.fold_left PostProcess.union PostProcess.empty uss in
          build_exp a (Pexp_tuple enr_exps), cs, us

      | Pexp_ifthenelse (lexp1, lexp2, Some lexp3) ->
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, us1 = for_expr lexp1 env in
          let enr_exp2, cs2, us2 = for_expr lexp2 env in
          let enr_exp3, cs3, us3 = for_expr lexp3 env in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp1) eloc (EzyPredef.bool_type eloc) ;
            AtConstr.create (ty_of_expr enr_exp2) eloc a ;
            AtConstr.create (ty_of_expr enr_exp3) eloc a ;
          ] in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2; cs3] in
          let us = List.reduce PostProcess.union [us1; us2; us3] in
          build_exp a (Pexp_ifthenelse (enr_exp1, enr_exp2, Some enr_exp3)), cs, us

      | Pexp_ifthenelse (lexp1, lexp2, None) ->
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, us1 = for_expr lexp1 env in
          let enr_exp2, cs2, us2 = for_expr lexp2 env in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp1) eloc (EzyPredef.bool_type eloc) ;
            AtConstr.create (ty_of_expr enr_exp2) eloc (EzyPredef.unit_type eloc);
            AtConstr.create a eloc (EzyPredef.unit_type eloc) ;
          ] in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          let us = PostProcess.union us1 us2 in
          build_exp a (Pexp_ifthenelse (enr_exp1, enr_exp2, None)), cs, us

      | Pexp_constraint (exp, ct) ->
          let a1 = Ty.fresh_var () in
          let a2 = Ty.fresh_var () in
          let a3 = Ty.fresh_var () in
          let enr_exp, cs0, pp0 = for_expr exp env in
          begin try
            let eloc' = ExtLocation.Source ct.Parsetree.ptyp_loc in
            let ty = ty_of_expr enr_exp in
            let _, ty' = EzyEnrichedAst.import_core_type true (env_for_ct_unloc env) StringMap.empty ct in
            let cs1 = AtConstrSet.from_list [
              AtConstr.create a2 eloc ty ;
              AtConstr.create a2 eloc' ty' ;
              AtConstr.create a3 eloc' ty' ;
              AtConstr.create a1 eloc a3 ;
            ] in
            let pp1 = PostProcess.type_annotations [TypeAnnotation.create ty loc ct] in
            build_exp a1 (Pexp_constraint (enr_exp, ct)), AtConstrSet.union cs0 cs1, PostProcess.union pp0 pp1
          with
            | EzyEnrichedAst.Invalid_type_constructor (lid, n, m) ->
                null_exp, AtConstrSet.empty, PostProcess.heavies [loc, EzyErrors.Invalid_type_constructor (lid, n, m)]
            | EzyEnrichedAst.Unbound_type_constructor lid ->
                null_exp, AtConstrSet.empty, PostProcess.heavies [loc, EzyErrors.Unbound_type_constructor lid]
          end

      | Pexp_assert exp ->
          let a = Ty.fresh_var () in
          let enr_exp, cs1, pp = for_expr exp env in
          let cs2 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp) eloc (EzyPredef.bool_type eloc) ;
            AtConstr.create a eloc (EzyPredef.unit_type eloc) ;
          ] in
          let desc = Pexp_assert enr_exp in
          build_exp a desc, AtConstrSet.union cs1 cs2, pp
      | Pexp_assertfalse ->
          let a = Ty.fresh_var () in
          build_exp a Pexp_assertfalse, AtConstrSet.empty, PostProcess.empty

      | Pexp_for (var, exp1, exp2, dir_flag, exp3) ->
          let ax = Ty.fresh_var () in
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          let ident, env' =
            let vd = EzyEnv.{
              val_kind = Types.Val_reg ;
              val_binding = EzyEnv.Mono ;
              val_scheme = begin
                let scm = Scheme.mono var.nm_name eloc ax in
                let set = AtConstrSet.SimpleAtConstrSet.singleton 
                  (AtConstr.from_eq
                    (AtConstr.create ax eloc (EzyPredef.int_type eloc))) in
                {scm with cstrs = ExtLocationMap.singleton eloc set}
              end;
              val_loc = ExtLocation.Source loc ;
            } in
            EzyEnv.enter_value var.nm_name vd env in
          let enr_exp3, cs3, pp3 = for_expr exp3 env' in
          let var' = { nm_name = var.nm_name; nm_loc = loc; nm_data = ident } in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create a eloc (EzyPredef.unit_type eloc) ;
            AtConstr.create (ty_of_expr enr_exp1) eloc (EzyPredef.int_type eloc) ;
            AtConstr.create (ty_of_expr enr_exp2) eloc (EzyPredef.int_type eloc) ;
          ] in
          let desc = Pexp_for (var', enr_exp1, enr_exp2, dir_flag, enr_exp3) in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2; cs3] in
          let pp = List.reduce PostProcess.union [pp1; pp2; pp3] in
          build_exp a desc, cs, pp

      | Pexp_while (exp1, exp2) ->
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create (ty_of_expr enr_exp1) eloc (EzyPredef.bool_type eloc) ;
            (* AtConstr.create (ty_of_expr enr_exp2) eloc (EzyPredef.unit eloc) ; *)
            AtConstr.create a eloc (EzyPredef.unit_type eloc) ;
          ] in
          let desc = Pexp_while (enr_exp1, enr_exp2) in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          let pp = PostProcess.union pp1 pp2 in
          build_exp a desc, cs, pp

      | Pexp_setfield (exp1, f, exp2) ->
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          begin try
            let _, fd = EzyEnv.lookup_field f.lid_name env in
            let pp0 =
              match fd.EzyEnv.fld_mutable with
                | Mutable ->
                    PostProcess.empty
                | Immutable ->
                    PostProcess.error loc (EzyErrors.Mutable_content f.lid_name) in
            let cs0 = AtConstrSet.from_list [
              AtConstr.create a eloc (EzyPredef.unit_type eloc) ;
              AtConstr.create fd.EzyEnv.fld_result eloc (ty_of_expr enr_exp1) ;
              AtConstr.create fd.EzyEnv.fld_arg eloc (ty_of_expr enr_exp2) ;
            ] in
            let f' = { lid_name = f.lid_name; lid_data = fd.EzyEnv.fld_path } in
            let desc = Pexp_setfield(enr_exp1, f', enr_exp2) in
            let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
            let pp = List.reduce PostProcess.union [pp0; pp1; pp2] in
            build_exp a desc, cs, pp
          with Not_found ->
            let pp0 = PostProcess.errors [loc, EzyErrors.Unknown_field f.lid_name] in
            let f' = { lid_name = f.lid_name; lid_data = Path.none } in
            let cs0 = AtConstrSet.singleton a eloc (EzyPredef.unit_type eloc) in
            let cs = AtConstrSet.big_union [cs0; cs1; cs2] in
            build_exp a (Pexp_setfield (enr_exp1, f', enr_exp2)), cs, (PostProcess.big_union [pp0; pp1; pp2])
          end

      | Pexp_field (exp, f) ->
          let a = Ty.fresh_var () in
          let enr_exp, cs1, pp = for_expr exp env in
          begin try
            logger#debug "Fields are %a"
              StringMap.KeySet.print (StringMap.keys env.EzyEnv.fields) ;
            let _, fd = EzyEnv.lookup_field f.lid_name env in
            let cs0 = AtConstrSet.from_list [
              AtConstr.create a eloc fd.EzyEnv.fld_arg ;
              AtConstr.create (ty_of_expr enr_exp) eloc fd.EzyEnv.fld_result ;
            ] in
            let f' = { lid_name = f.lid_name; lid_data = fd.EzyEnv.fld_path } in
            let desc = Pexp_field (enr_exp, f') in
            let cs = AtConstrSet.union cs0 cs1 in
            build_exp a desc, cs, pp
          with Not_found ->
            let pp0 = PostProcess.errors [loc, EzyErrors.Unknown_field f.lid_name] in
            let f' = { lid_name = f.lid_name; lid_data = Path.none } in
            build_exp a (Pexp_field (enr_exp, f')), cs1, (PostProcess.union pp pp0)
          end

      | Pexp_try (exp, rules) ->
          let a = Ty.fresh_var () in
          let enr_exp, cs1, pp1 = for_expr exp env in
          let enr_rules, ty_p, ty_e, cs2, pp2 = for_rules eloc rules env in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create ty_p eloc (EzyPredef.exn_type eloc) ;
            AtConstr.create a eloc (ty_of_expr enr_exp) ;
            AtConstr.create a eloc ty_e ;
          ] in
          let desc = Pexp_try (enr_exp, enr_rules) in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          let pp = PostProcess.union pp1 pp2 in
          build_exp a desc, cs, pp

      | Pexp_sequence (exp1, exp2) ->
          let a = Ty.fresh_var () in
          let enr_exp1, cs1, pp1 = for_expr exp1 env in
          let enr_exp2, cs2, pp2 = for_expr exp2 env in
          let cs0 = AtConstrSet.from_list [
            (* AtConstr.create EzyEPredef.unit eloc (ty_of_expr enr_exp1) ; *)
            AtConstr.create a eloc (ty_of_expr enr_exp2) ;
          ] in
          let desc = Pexp_sequence(enr_exp1, enr_exp2) in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          let pp = PostProcess.union pp1 pp2 in
          build_exp a desc, cs, pp

      | Pexp_record (fs, None) ->

          let inspect_type_constructor = function
            | Ty.Constr (_, p, tys) -> 
                let force_tyvar = function Ty.Var v -> v | _ -> invalid_arg "inspect_type_constructor" in
                p, List.map force_tyvar tys
            | _ -> invalid_arg "inspect_type_constructor" in

          let lident_of_ty = Path.to_lident << fst << inspect_type_constructor in
          
          (* Returns a triple of 1/ the list of unknown fields 2/ a list of more informative
           * fields, i.e. the field's long ident and its field description and 3/ the list
           * of enriched expressions, constraints etc for the field's expressions.
           *)
          let clean_fields fs =
            (* Returns a list of unknown fields and and a list fields with more type information *)
            let on_field (unknown_fields, fs', tyvarmap) (f, exp) =
              try
                let tyvarmap, fd = EzyEnv.lookup_field ~tyvarmap f.lid_name env in
                let enr_cs_pp = for_expr exp env in
                unknown_fields, ((f.lid_name, fd), enr_cs_pp) :: fs', tyvarmap
              with Not_found ->
                f.lid_name :: unknown_fields, fs', tyvarmap in
            let unknown_fields, li, _ = List.fold_left on_field ([], [], TyVarMap.empty) fs in
            let fs', enrs_css_pps = List.split (List.rev li) in
            List.rev unknown_fields, fs', enrs_css_pps in

          (* Returns either a list of heavy errors (No_Fields, Fields_bound_several_times,
           * Alien_fields) or a common result type *)
          let check_consistent_result_type fds =
            match fds with
              | [] ->
                  Result.Error [EzyErrors.No_fields]
              | (_, fd) :: fds ->
                let rec collect_aliens_n_severals known severals aliens = function
                  | [] -> (
                      let res_path, _ = inspect_type_constructor fd.EzyEnv.fld_result in
                      match List.rev aliens, List.rev severals with
                        | [], [] ->
                            Result.Ok (Ty.set_label fd.EzyEnv.fld_result eloc)
                        | [], severals ->
                            Result.Error [EzyErrors.Fields_bound_several_times severals]
                        | aliens, [] ->
                            Result.Error [EzyErrors.Alien_fields (res_path, aliens)]
                        | aliens, severals ->
                            Result.Error [EzyErrors.Alien_fields (res_path, aliens); EzyErrors.Fields_bound_several_times severals]
                    )
                  | (f, fd') :: fds_rem ->
                      let known, severals =
                        if PathSet.mem fd'.EzyEnv.fld_path known then
                          known, f :: severals
                        else
                          PathSet.add fd'.EzyEnv.fld_path known, severals in
                      let aliens =
                        if snd (Ty.equal_modulo_tyvarmap fd'.EzyEnv.fld_result fd.EzyEnv.fld_result) then
                          aliens
                        else begin
                          let res_path, _ = inspect_type_constructor fd'.EzyEnv.fld_result in
                          (f, res_path) :: aliens
                        end in
                      collect_aliens_n_severals known severals aliens fds_rem in
                collect_aliens_n_severals PathSet.empty [] [] fds in

          let check_completeness res_fs fds =
            let aux name _ missings =
              if List.exists (fun fd -> Path.last fd.EzyEnv.fld_path = name) fds then
                missings
              else
                name :: missings in
            StringMap.fold aux res_fs [] in

          let fields_of_ty env ty =
            match ty with
              | Ty.Constr (_, p, _) ->
                  let td = EzyEnv.find_type p env in (
                  match td.EzyEnv.type_kind with
                    | EzyEnv.Record res_fs -> res_fs
                    | _ -> invalid_arg "fields_of_ty,1"
                  )
              | _ -> invalid_arg "fields_of_ty,2" in

          (* Returns either a list of heavy errors or a (possible) empty list of heavy errors
           * and errors and a common type. This is for the case without a base record. *)
          let check_just_fields fs =
            let unknown_fields, fs', enrs_css_pps = clean_fields fs in
            let unknown_fields_heavies = 
              if unknown_fields = [] then []
              else [EzyErrors.Unknown_fields unknown_fields] in
            match check_consistent_result_type fs' with
              | Result.Ok ty ->
                  if unknown_fields_heavies = [] then
                    let res_fs = fields_of_ty env ty in
                    let missings_error =
                      match check_completeness res_fs (List.map snd fs') with
                        | [] -> None
                        | missings -> Some (EzyErrors.Missing_fields (lident_of_ty ty, missings)) in
                    Result.Ok (ty, unknown_fields_heavies, missings_error, List.map snd fs', enrs_css_pps)
                  else
                    Result.Error unknown_fields_heavies
              | Result.Error heavies ->
                  Result.Error (List.append unknown_fields_heavies heavies) in

          begin match check_just_fields fs with
            | Result.Ok (ty_r, [], missing_error, fds, enrs_css_pps) ->
                let tyvarmap, ty_r' = Ty.fresh_variant ty_r in
                let _tyvarmap, ty_fs' = Ty.fresh_variants ~tyvarmap (List.map (fun fd -> fd.EzyEnv.fld_arg) fds) in
                let a = Ty.fresh_var () in
                let enr_exps, css, pps = List.split3 enrs_css_pps in
                let cs0 =
                  let aux ty_f' enr_exp =
                    AtConstr.create ty_f' eloc (ty_of_expr enr_exp) in
                  AtConstrSet.from_list (AtConstr.create a eloc ty_r' :: List.map2 aux ty_fs' enr_exps) in
                let cs = List.fold_left AtConstrSet.union cs0 css in
                let pp =
                  match missing_error with
                    | Some missing ->
                        let pp' = PostProcess.errors [loc, missing] in
                        List.reduce PostProcess.union (pp' :: pps)
                    | None -> PostProcess.big_union pps in
                let fs' =
                  let aux fd (f, _) = { lid_name = f.lid_name; lid_data = fd.EzyEnv.fld_path } in
                  let field_lids = List.map2 aux fds fs in
                  List.map2 T2.create field_lids enr_exps in
                build_exp a (Pexp_record (fs', None)), cs, pp
            | Result.Ok (_ty_r, heavies, missings, _fds, _enrs_css_pps) ->
                let pp_heavies = PostProcess.heavies [loc, EzyErrors.Invalid_record heavies] in
                let pp_errors = 
                  match missings with
                    | None -> PostProcess.empty
                    | Some m -> PostProcess.errors [loc, m] in
                null_exp, AtConstrSet.empty, PostProcess.union pp_heavies pp_errors
            | Result.Error heavies ->
                let pp = PostProcess.heavies [loc, EzyErrors.Invalid_record heavies] in
                null_exp, AtConstrSet.empty, pp
          end

      | Pexp_record (_fs, Some _) ->
          not_implemented "EzyGenerate.for_expr (_, Some _) -- {exp with ...}"
    in 
    logger#debug "for_expr at %a@ @[%a@]:@ %a -@ %a" Location.print expr.pexp_loc (EzyAst.print_expr ()) enr_expr Ty.print (ty_of_expr enr_expr) AtConstrSet.print cs ;
    enr_expr, cs, us

(* }}} *)

(* Rules {{{ *)                    

and for_rule:
    imported_rule -> EzyEnv.t -> 
    generated_rule * Ty.t * Ty.t * AtConstrSet.t * PostProcess.t =
  fun {rule_pat=pat; rule_guard=guard; rule_exp=exp} env ->
    let enr_pat, cs_p, pp1, b = for_pattern pat env in
    let env' = 
      let aux name env =
        let ty', _, loc = StringMap.find name b in
        let eloc = ExtLocation.Source loc in
        let vd = EzyEnv.{
          val_kind = Types.Val_reg ;
          val_binding  = EzyEnv.Mono ;
          val_scheme = Scheme.mono name eloc ty' ;
          val_loc = eloc ;
        } in
        snd (EzyEnv.enter_value name vd env) in
      StringSet.fold aux (StringMap.keys b) env in
    (* This added by AbelianGrape to support 'when exp ->' *)
    let enr_guard, cs_g, pp2 = match guard with
      | None -> None, AtConstrSet.empty, PostProcess.empty
      | Some g ->
        let eloc = ExtLocation.Source g.pexp_loc in
        let g, cs, pp = for_expr g env' in
        let c = AtConstr.create (ty_of_expr g) eloc (EzyPredef.bool_type eloc) in
        Some g, AtConstrSet.add cs c, pp
    in
    let enr_exp, cs_e, pp3 = for_expr exp env' in
    {rule_pat=enr_pat; rule_guard=enr_guard; rule_exp=enr_exp},
      enr_pat.ppat_data.pa_ty, ty_of_expr enr_exp,
      AtConstrSet.big_union [cs_p;cs_g;cs_e], PostProcess.big_union [pp1;pp2;pp3]

and for_rules:
    ExtLocation.t -> imported_rule list -> EzyEnv.t ->
    generated_rule list * Ty.t * Ty.t * AtConstrSet.t * PostProcess.t =
  fun eloc rules env ->
    match rules with
      | [] -> (* failwith "EzyGenerate.for_rules" *)
          [], Ty.fresh_var (), Ty.fresh_var (), AtConstrSet.empty, PostProcess.empty
      | rule :: rem_rules ->
          let enr_rule, ty_p1, ty_e1, cs1, pp1 = for_rule rule env in
          let enr_rules, ty_p2, ty_e2, cs2, pp2 = for_rules eloc rem_rules env in
          (* Redundant. ~AbelianGrape
          let a_p = Ty.fresh_var () in
          let a_e = Ty.fresh_var () in
          let cs0 = AtConstrSet.from_list [
            AtConstr.create a_p eloc ty_p1 ;
            AtConstr.create a_p eloc ty_p2 ;
            AtConstr.create a_e eloc ty_e1 ;
            AtConstr.create a_e eloc ty_e2 ;
          ] in
          *)
          let cs0 = AtConstrSet.from_list [
            AtConstr.create ty_p1 eloc ty_p2 ;
            AtConstr.create ty_e1 eloc ty_e2
          ] in
          let cs = List.reduce AtConstrSet.union [cs0; cs1; cs2] in
          enr_rule :: enr_rules, ty_p2, ty_e2, cs, PostProcess.union pp1 pp2
    

(* }}} *)

(* Structure {{{ *)

let null_strit _env =
  Pstr_eval null_exp

let for_structure_item env type_accu strit =

  let build_strit desc = {
    pstr_loc = strit.pstr_loc ;
    pstr_desc = desc ;
  } in

  match strit.pstr_desc with
    | Pstr_dots _ ->
        raise (InternalDotsError "for_structure_item: not implemented for dots")
    | Pstr_eval expr ->
        let enr_expr, cs, pp = for_expr expr env in
        build_strit (Pstr_eval enr_expr), env, cs, pp, type_accu
    | Pstr_value bindings ->
        let (cs, pp, env'), enr_bindings = collect_bindings env strit.pstr_loc bindings in  
        build_strit (Pstr_value enr_bindings), env', cs, pp, type_accu
    | Pstr_rec_value bindings ->
        let (cs, pp, env'), enr_bindings = collect_rec_bindings env strit.pstr_loc bindings in
        build_strit (Pstr_rec_value enr_bindings), env', cs, pp, type_accu
    | Pstr_type (tbindings: ('nm_data name * 'nm_data type_declaration) list) ->

        begin try
          let check_unique type_accu tbindings =
            (* [accus] is an assoc list from type names to their number of duplicates *)
            let rec accumulate accus = function
              | [] ->
                  let type_names = List.map fst accus in
                  begin match List.map fst (List.filter ((<>) 0 << snd) accus) with
                    | [] -> Result.Ok type_names
                    | multiple_type_names -> Result.Error (type_names, multiple_type_names)
                  end
              | h :: t ->
                  let rec sort = function
                    | [] -> [h, 0]
                    | (x, n) :: rem_li ->
                        if h = x then
                          (x, succ n) :: rem_li
                        else
                          (x, n) :: sort rem_li in
                  accumulate (sort accus) t in
            accumulate (List.map (fun nm -> nm, 0) type_accu) (List.map (fun (nm,_) -> nm.nm_name) tbindings)
          in

          (* [pre_binding] collects informations about a single type declaration which is
           * needed in the following step, i.e. extending [env] and building the enriched
           * bindings. *)
          let pre_binding (ty_name, td) =
            let enrich_param tyvarmap param_name =
              let param_name' = enrich_name param_name in
              let tyvar = TyVar.fresh () in
              StringMap.add param_name.nm_name tyvar tyvarmap, (param_name', Ty.Var tyvar) in
            let tyvarmap, ext_params =
              List.foldmap enrich_param StringMap.empty td.EzyAst.type_params in
            let ty_name' = enrich_name ty_name in
            let param_names, param_tys = List.split ext_params in
            ty_name.nm_name, (ty_name', tyvarmap, param_names, param_tys, td) in

          let binding_infs = List.map pre_binding tbindings in

          let ctor_lookup = function
            | Longident.Lident name when List.mem_assoc name binding_infs ->
                let name', _, _, param_tys, _ = List.assoc name binding_infs in
                Path.Pident name'.nm_data, param_tys
            | lid -> env_for_ct env lid in
          let ctor_lookup lid = ctor_lookup lid.txt in

          let enrich_binding env binding_inf =
            let _, (ty_name, tyvarmap, param_names, param_tys, td) = binding_inf in
            let ast_kind, env_kind =
              match td.EzyAst.type_kind with
                | EzyAst.Abstract ->
                    EzyAst.Abstract, EzyEnv.Abstract
                | EzyAst.Synonym ct ->
                    let _tyvarmap, ty = EzyEnrichedAst.import_core_type false ctor_lookup tyvarmap ct in
                    (* AbelianGrape: record type synonyms for nullary type constructors. *)
                    begin match param_names with
                      | [] -> Ty.add_type_synonym (Ident.name ty_name.nm_data) ty
                      | _  -> failwith "unsupported non-nullary type synonym"
                    end;
                    EzyAst.Synonym ct, EzyEnv.Synonym ty 
                | EzyAst.Variant vs ->
                    let env_vs =
                      let enrich_variant tyvarmap (k, cts, _loc) =
                        let tyvarmap, tys = EzyEnrichedAst.import_core_types false ctor_lookup tyvarmap cts in
                        tyvarmap, (k, tys) in
                      let _, vs' = List.foldmap enrich_variant tyvarmap vs in
                      StringMap.from_list vs' in
                    EzyAst.Variant vs, EzyEnv.Variant env_vs 
                | EzyAst.Record fs ->
                    let env_fs =
                      let enrich_field tyvarmap (f, m, ct, _loc) =
                        let tyvarmap, ty = EzyEnrichedAst.import_core_type false ctor_lookup tyvarmap ct in
                        tyvarmap, (f, (m, ty)) in
                      let _, fs' = List.foldmap enrich_field tyvarmap fs in
                      StringMap.from_list fs' in
                    EzyAst.Record fs, EzyEnv.Record env_fs in
            let ast_td = {
              EzyAst.type_params = param_names ;
              type_kind = ast_kind ;
            } in
            let env_td = {
              EzyEnv.type_params = param_tys ;
              type_kind = env_kind ;
              type_loc = ExtLocation.Source strit.pstr_loc ;
            } in
            EzyEnv.add_type ty_name.nm_data env_td env, (ty_name, ast_td) in

          begin match check_unique type_accu tbindings with
            | Result.Ok type_accu ->
                let env', enr_bindings = List.foldmap enrich_binding env binding_infs in
                build_strit (Pstr_type enr_bindings), env', AtConstrSet.empty, PostProcess.empty, type_accu
            | Result.Error (type_accu, multiple_types) ->
                let pp = PostProcess.heavies [strit.pstr_loc, EzyErrors.Type_names_not_unique multiple_types] in
                build_strit (null_strit env), env, AtConstrSet.empty, pp, type_accu
          end
        with 
          | EzyEnrichedAst.Invalid_type_constructor (lid, n, m) ->
              build_strit (null_strit env), env, AtConstrSet.empty, PostProcess.heavies [strit.pstr_loc, EzyErrors.Invalid_type_constructor (lid, n, m)], type_accu
          | EzyEnrichedAst.Unbound_type_constructor lid ->
              build_strit (null_strit env), env, AtConstrSet.empty, PostProcess.heavies [strit.pstr_loc, EzyErrors.Unbound_type_constructor lid], type_accu
        end

    | Pstr_exception (name, cts) ->
        let _tyvarmap, tys = EzyEnrichedAst.import_core_types true (env_for_ct_unloc env) StringMap.empty cts in
        let ident, env = EzyEnv.enter_exception name.nm_name tys env in
        let name' = enrich_name ~ident name in
        build_strit (Pstr_exception (name', cts)), env, AtConstrSet.empty, PostProcess.empty, type_accu
    | Pstr_open ({ lid_name = Longident.Lident name ; _ } as lid) ->
        begin try
          let ident, env = EzyEnv.open_module name env in
          let lid' = {
            lid_name = lid.lid_name ;
            lid_data = Path.Pident ident ;
          } in
          logger#trace "opened %s, env is now: %a" name (EzyEnv.print true) env ;
          build_strit (Pstr_open lid'), env, AtConstrSet.empty, PostProcess.empty, type_accu
        with Not_found ->
          EzyErrors.raise_fatal ~loc:strit.pstr_loc (EzyErrors.Module_not_found lid.lid_name)
        end
    | Pstr_open { lid_name = _lid ; _ } ->
        (* Raising a not supported constant error here is obviously wrong, but reconstructing the correct
           Parsetree.structure_item node for this open is very difficult as we discarded a lot of information
           when importing it. This is a result of the half-baked patch to 4.13 from 3.10.
           ~AbelianGrape. *)
        EzyErrors.raise_fatal ~loc:strit.pstr_loc (EzyErrors.Import_error (EzyErrors.Not_supported_constant, None))

let for_structure_item env types strit =
  between $for_structure_item env types $ strit $
    (fun (enr_strit, _, cs, _, _) ->
       logger#debug "for_structure_item at %a@ %a:@ %a" Location.print strit.pstr_loc (EzyAst.print_structure_item ()) enr_strit AtConstrSet.print cs)


let for_structure: imported_structure -> EzyEnv.t -> generated_structure * AtConstrSet.t * PostProcess.t * EzyEnv.t =
  fun str env ->

  let rec aux (str_its, cs, pp, env, type_accu) = function
    | [] ->
        List.rev str_its, cs, pp, env
    | str_it :: str_rem ->
        let enr_strit, env0, cs0, pp0, type_accu = for_structure_item env type_accu str_it in
        logger#debug "Generated for strit, resulting env:\n%a" (EzyEnv.print false) env0 ;
        aux (enr_strit :: str_its, AtConstrSet.union cs cs0, PostProcess.union pp pp0, env0, type_accu) str_rem in

  aux ([], AtConstrSet.empty, PostProcess.empty, env, []) str

(* }}} *)

(************************************************************************ }}} *)
