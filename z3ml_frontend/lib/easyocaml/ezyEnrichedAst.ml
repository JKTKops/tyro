open EzyAst
open EzyAsttypes
open EzyOcamlmodules
open EzyTypingCoreTypes
open EzyUtils



let logger = new Logger.logger "enr_ast"

type exp_data = 
    {
      ea_ty: Ty.t ;
      ea_env: EzyEnv.t ;
    }

type id_data = Path.t

type pat_data =
    {
      pa_ty: Ty.t ;
      pa_ident: Ident.t ;
      pa_env: EzyEnv.t ;
    }

type name_data = Ident.t

type generated_expression = (exp_data, id_data, name_data, pat_data) expression
type generated_structure_item = (exp_data, id_data, name_data, pat_data) EzyAst.structure_item
type generated_structure = (exp_data, id_data, name_data, pat_data) structure
type generated_pattern = (exp_data, id_data, name_data, pat_data) pattern
type generated_rule = (exp_data, id_data, name_data, pat_data) rule
type typed_structure = (Ty.t, Path.t, Ident.t, Ty.t) EzyAst.structure


(******************************************************************************)
(*                                  IMPORT                                    *)
(******************************************************************************)

open EzyUtils.Infix

let import_error loc ?reason err =
  EzyErrors.raise_fatal ~loc (EzyErrors.Import_error (err, reason))

let import_constant loc = function
  | Parsetree.Pconst_integer (text, None) ->
      Scanf.sscanf text "%d" (fun i -> Const_int i)

  | Parsetree.Pconst_char c ->
      Const_char c
  | Parsetree.Pconst_string (s, _, _) ->
      Const_string s
    (* TODO: what is the char here for? ofc docs don't say (: *)
  | Parsetree.Pconst_float (text, None) ->
      Const_float text
  | _ ->
      raise (import_error loc EzyErrors.Not_supported_constant)

exception TyVarNotFound of string
exception Invalid_type_constructor of (Longident.t * int * int)
exception Unbound_type_constructor of Longident.t

let rec import_core_type creative lookup_ctor tyvarmap ct =
  let label = ExtLocation.Source ct.Parsetree.ptyp_loc in
  match ct.Parsetree.ptyp_desc with
    | Parsetree.Ptyp_any ->
        tyvarmap, Ty.Var (TyVar.fresh ())
    | Parsetree.Ptyp_var var ->
        begin try
           tyvarmap, Ty.Var (StringMap.find var tyvarmap)
        with Not_found ->
          if creative then
            let tyvar = TyVar.fresh () in
            StringMap.add var tyvar tyvarmap, Ty.Var tyvar
          else 
            raise (TyVarNotFound var)
        end
    | Parsetree.Ptyp_tuple ctys ->
        let tyvarmap, tys' = import_core_types creative lookup_ctor tyvarmap ctys in
        tyvarmap, Ty.Tuple (label, tys')
    | Parsetree.Ptyp_arrow (Nolabel, tx, ty) ->
        let tyvarmap, tx' = import_core_type creative lookup_ctor tyvarmap tx in
        let tyvarmap, ty' = import_core_type creative lookup_ctor tyvarmap ty in
        tyvarmap, Ty.Arrow (label, tx', ty')
    | Parsetree.Ptyp_constr (lid, params) ->
        begin try
          let path, tparams = lookup_ctor lid in
          let expected_params, found_params = List.length tparams, List.length params in
          if expected_params = found_params then
            let tyvarmap, params' = import_core_types creative lookup_ctor tyvarmap params in
            tyvarmap, Ty.Constr (label, path, params')
          else
            raise (Invalid_type_constructor (lid.txt, expected_params, found_params))
        with Not_found ->
          raise (Unbound_type_constructor lid.txt)
        end
    | Parsetree.Ptyp_poly ([], ct) ->
        import_core_type creative lookup_ctor tyvarmap ct
    | Parsetree.Ptyp_arrow (_arg_label, _, _) ->
        logger#error "EzyAst.import_core_type Ptyp_arrow (arg_label, _, _)" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_object _ ->
        logger#error "EzyAst.import_core_type Ptyp_object _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_class _ ->
        logger#error "EzyAst.import_core_type Ptyp_class _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_poly _ ->
        logger#error "EzyAst.import_core_type Ptyp_poly (_::_, _)" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_variant _ ->
        logger#error "EzyAst.import_core_type Ptyp_variant _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_alias _ ->
        logger#error "EzyAst.import_core_type Ptyp_alias _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_package _ ->
        logger#error "EzyAst.import_core_type Ptyp_package _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type
    | Parsetree.Ptyp_extension _ ->
        logger#error "EzyAst.import_core_type Ptyp_extension _" ;
        import_error ct.Parsetree.ptyp_loc EzyErrors.Not_supported_core_type

and import_core_types creative lookup_ctor tyvarmap ctys =
  List.foldmap (import_core_type creative lookup_ctor) tyvarmap ctys
  
let rec import_pattern pf pat =
  let longident lid = { lid_name = lid; lid_data = () } in
  let pattern desc : imported_pattern = 
    { ppat_desc = desc; ppat_loc = pat.Parsetree.ppat_loc; ppat_data = () } in
  let pat_import_error reason =
    import_error pat.Parsetree.ppat_loc ~reason (EzyErrors.Not_supported_pattern pat.Parsetree.ppat_desc) in
  let module F = EzyFeatures in
  let sub_pf =
    if pf.F.p_nested then pf else
      let empty_pf = F.all_pattern_feats false in
      { empty_pf with F.p_wildcard = true; p_var = true } in
  match pat.Parsetree.ppat_desc with
    | Parsetree.Ppat_var var ->
        if pf.F.p_var then
          pattern (Ppat_var { nm_name = var.txt; nm_loc = pat.Parsetree.ppat_loc; nm_data = () })
        else
          pat_import_error "p_var"
    | Parsetree.Ppat_any ->
        if pf.F.p_wildcard then
          pattern Ppat_any
        else
          pat_import_error "p_wildcard"
    | Parsetree.Ppat_constant c ->
        if pf.F.p_constant then
          pattern (Ppat_constant (import_constant pat.Parsetree.ppat_loc c))
        else
          pat_import_error "p_constant"
    | Parsetree.Ppat_tuple ps ->
        if pf.F.p_tuple then
          pattern (Ppat_tuple (List.map (import_pattern sub_pf) ps))
        else
          pat_import_error "p_tuple"
    | Parsetree.Ppat_construct (k, opt_pat) ->
        if pf.F.p_constructor then
          let opt_pat' = match opt_pat with None -> None | Some pat -> Some (import_pattern sub_pf (snd pat)) in
          pattern (Ppat_construct (longident k.txt, opt_pat', false))
        else
          pat_import_error "p_constructor"
    | Parsetree.Ppat_record (fs, _cf) -> (* ezy doesn't care about closed/open, that's OK ~abeliangrape *)
        if pf.F.p_record then
          let fs' = List.map (fun (f, p) -> longident f.txt, import_pattern sub_pf p) fs in
          pattern (Ppat_record fs')
        else
          pat_import_error "p_record"
    | Parsetree.Ppat_or (p1, p2) ->
        if pf.F.p_or then
          pattern (Ppat_or (import_pattern sub_pf p1, import_pattern sub_pf p2))
        else
          pat_import_error "p_or"
    | Parsetree.Ppat_alias (p, nm) ->
        if pf.F.p_alias then
          pattern (Ppat_alias (import_pattern sub_pf p, { nm_name = nm.txt; nm_data = (); nm_loc = Location.none } ))
        else
          pat_import_error "p_alias"
    | Parsetree.Ppat_constraint (p, ct) ->
        if pf.F.p_type_annotation then
          pattern (Ppat_constraint (import_pattern sub_pf p, ct))
        else
          pat_import_error "p_type_annotation"
    | desc -> raise (import_error pat.Parsetree.ppat_loc (EzyErrors.Not_supported_pattern desc))

let rec import_var_binding ef loc vb =
  match Parsetree.(vb.pvb_pat.ppat_desc) with
    | Parsetree.Ppat_var var ->
        { nm_name = var.txt; nm_loc = loc; nm_data = () }, import_expression ef vb.Parsetree.pvb_expr
    | _ -> 
        EzyErrors.raise_fatal ~loc (EzyErrors.Import_error (EzyErrors.Not_supported_pattern Parsetree.(vb.pvb_pat.ppat_desc), None))

and import_value_binding pf ef vb =
  Parsetree.(import_pattern pf vb.pvb_pat, import_expression ef vb.pvb_expr)
and import_value_bindings pf ef vbs = List.map (import_value_binding pf ef) vbs

and import_option importer = function
  | None -> None
  | Some x -> Some (importer x)

and import_case pf ef c =
  Parsetree.({ rule_pat = import_pattern pf c.pc_lhs;
               rule_guard = import_option (import_expression ef) c.pc_guard;
               rule_exp = import_expression ef c.pc_rhs
             })

and import_cases pf ef cs = List.map (import_case pf ef) cs

and import_expression ef x =
  let loc = x.Parsetree.pexp_loc in
  let expr_import_error reason =
    import_error x.Parsetree.pexp_loc ~reason (EzyErrors.Not_supported_expression x.Parsetree.pexp_desc) in
  let name loc nm = { nm_name = nm; nm_loc = loc; nm_data = () } in 
  let longident lid = { lid_name = lid; lid_data = () } in
  let build_expr ?(loc=loc) desc = { pexp_loc = loc; pexp_desc = desc; pexp_data = () } in
  let module F = EzyFeatures in
  match x.Parsetree.pexp_desc with

    | Parsetree.Pexp_ident lident ->
        begin match lident.txt with
          | Longident.Lident id ->
              if id <> "raise" || ef.F.e_raise then
                if ef.F.e_simple_var then
                  build_expr (Pexp_ident (longident lident.txt))
                else
                  expr_import_error "e_simple_var"
              else
                expr_import_error "e_raise"
          | Longident.Ldot _ ->
              if ef.F.e_qualified_var then
                build_expr (Pexp_ident (longident lident.txt))
              else
                expr_import_error "e_qualified_var"
          | _ ->
              import_error loc (EzyErrors.Not_supported_expression x.Parsetree.pexp_desc)
        end

    | Parsetree.Pexp_constant c ->
        if ef.F.e_constant then
          build_expr (Pexp_constant (import_constant loc c))
        else
          expr_import_error "e_constant"

    | Parsetree.Pexp_let (Nonrecursive, bindings, body) ->
        begin match ef.F.e_let_in with
          | Some ({ F.l_pattern = pf ; _ } as lf) ->
              if lf.F.l_and || (match bindings with [_] -> true | _ -> false) then
                build_expr (Pexp_let (import_value_bindings pf ef bindings, import_expression ef body))
              else
                expr_import_error "l_and"
          | None ->
              expr_import_error "e_let_in"
        end

    | Parsetree.Pexp_let (Recursive, bindings, body) ->
        begin match ef.F.e_let_rec_in with
          | Some lrf ->
              if lrf.F.lr_and || (match bindings with [_] -> true | _ -> false) then
                build_expr (Pexp_letrec (List.map (import_var_binding ef x.Parsetree.pexp_loc) bindings, import_expression ef body))
              else
                expr_import_error "lr_and"
          | None ->
              expr_import_error "e_let_rec_in"
        end

    | Parsetree.Pexp_fun (Nolabel, None, pat, body) ->
      begin match ef.F.e_function with
        | Some { F.f_pattern = pf ; _ } ->
          let case = Parsetree.{ pc_lhs = pat; pc_guard = None; pc_rhs = body } in
          build_expr (Pexp_function (import_cases pf ef [case]))
        | None ->
            expr_import_error "e_fun"
      end

    | Parsetree.Pexp_function rules ->
        begin match ef.F.e_function with
          | Some { F.f_pattern = pf ; _ } ->
              build_expr (Pexp_function (import_cases pf ef rules))
          | None ->
              expr_import_error "e_function"
        end

    | Parsetree.Pexp_apply (head, args) ->
        if List.for_all ((=) Nolabel << fst) args then
          begin match args with
            | [] -> assert false
            | [_, arg] ->
                build_expr (Pexp_apply (import_expression ef head, import_expression ef arg))
            | args ->
                logger#info
                  "A different parser than Ocaml's default should be used to avoid inaccuracy for the location of multiple application (%a)."
                  Location.print loc ;
                (* Idea of how to guess: if the first arg is positioned before the head,
                   we have a binary operator application. OCaml doesn't have sections, 
                   so there must be at least two arguments. The first two should therefore
                   report the span between them as their location (for both); everything else
                   should report the span from the first one.
                   Otherwise, everything should report the span from the head to itself. *)
                let setup_operator args = match args with
                  | [] | [_] -> failwith "impossible"
                  | (_,one) :: (_,two) :: rest ->
                    if head.Parsetree.pexp_loc < one.Parsetree.pexp_loc (* head is textually first; normal *)
                    then import_expression ef head, args
                    else
                      let loc = Location.span one.Parsetree.pexp_loc two.Parsetree.pexp_loc in
                      let step1 = build_expr ~loc (Pexp_apply (import_expression ef head, import_expression ef one)) in
                      let step2 = build_expr ~loc (Pexp_apply (step1, import_expression ef two)) in
                      step2, rest
                in
                let rec go start sofar = function
                  | [] -> sofar
                  | (_, arg) :: rem_args ->
                      let loc = Location.span start.EzyAst.pexp_loc arg.Parsetree.pexp_loc in
                      let app = build_expr ~loc (Pexp_apply (sofar, import_expression ef arg)) in
                      go start app rem_args in
                let (start, args) = setup_operator args in
                go start start args
          end
        else
          import_error x.Parsetree.pexp_loc (EzyErrors.Not_supported_expression x.Parsetree.pexp_desc)

     | Parsetree.Pexp_match (exp, rules) ->
         begin match ef.F.e_match with
           | Some pf ->
               build_expr (Pexp_match (import_expression ef exp, import_cases pf ef rules))
           | None ->
               expr_import_error "e_match"
         end

     | Parsetree.Pexp_try (exp, rules) ->
         begin match ef.F.e_try with
           | Some pf ->
               build_expr (Pexp_try (import_expression ef exp, import_cases pf ef rules))
           | None ->
               expr_import_error "e_try"
         end

     | Parsetree.Pexp_tuple exps ->
         if ef.F.e_tuple then
           build_expr (Pexp_tuple (List.map (import_expression ef) exps))
         else
           expr_import_error "e_tuple"

     | Parsetree.Pexp_construct (lid, opt_exp) ->
         if ef.F.e_constructor then
           build_expr (Pexp_construct (longident lid.txt, Option.map ~f:(import_expression ef) opt_exp, false))
         else
           expr_import_error "e_constructor"

     | Parsetree.Pexp_record (fs, opt_exp) ->
         let f (f, exp) = longident f.txt, import_expression ef exp in
         begin match opt_exp with
           | Some orig ->
               if ef.F.e_record_functional_update then
                 build_expr (Pexp_record (List.map f fs, Some (import_expression ef orig)))
               else
                 expr_import_error "e_record_functional_update"
           | None ->
               if ef.F.e_record_construction then
                 build_expr (Pexp_record (List.map f fs, None))
               else
                 expr_import_error "e_record_construction"
         end

     | Parsetree.Pexp_field (exp, lid) ->
         if ef.F.e_record_field_access then
           build_expr (Pexp_field (import_expression ef exp, longident lid.txt))
         else
           expr_import_error "e_record_field_access"

     | Parsetree.Pexp_setfield (exp1, lid, exp2) ->
         if ef.F.e_record_field_update then
           build_expr (Pexp_setfield (import_expression ef exp1, longident lid.txt, import_expression ef exp2))
         else
           expr_import_error "e_record_field_update"

     | Parsetree.Pexp_ifthenelse (exp1, exp2, opt_exp3) ->
         begin match opt_exp3 with
           | Some exp3 ->
               if ef.F.e_if_then_else then
                 build_expr (Pexp_ifthenelse (import_expression ef exp1, import_expression ef exp2, Some (import_expression ef exp3)))
               else
                 expr_import_error "e_if_then_else"
           | None ->
               if ef.F.e_if_then then
                 build_expr (Pexp_ifthenelse (import_expression ef exp1, import_expression ef exp2, None))
               else
                 expr_import_error "e_if_then"
         end

     | Parsetree.Pexp_sequence (exp1, exp2) ->
         if ef.F.e_sequence then
           build_expr (Pexp_sequence (import_expression ef exp1, import_expression ef exp2))
         else
           expr_import_error "e_sequence"

     | Parsetree.Pexp_while (exp1, exp2) ->
         if ef.F.e_while then
           build_expr (Pexp_while (import_expression ef exp1, import_expression ef exp2))
         else
           expr_import_error "e_while"

     | Parsetree.Pexp_for (idx, exp1, exp2, direction_flag, exp3) ->
         
         let varname = match idx.ppat_desc with
          | Parsetree.Ppat_var n -> name loc n.txt
          | Parsetree.Ppat_any   -> name loc "_" (* not sure what else to do here but anything should work *)
          | _ -> raise (Typecore.Error_forward (Typecore.report_error ~loc:idx.ppat_loc Env.empty Typecore.Invalid_for_loop_index))
         in
         if ef.F.e_for then
           build_expr (Pexp_for (varname, import_expression ef exp1, import_expression ef exp2, direction_flag, import_expression ef exp3))
         else
           expr_import_error "e_for"

     | Parsetree.Pexp_assert exp ->
         if ef.F.e_assert then
           build_expr (Pexp_assert (import_expression ef exp))
         else
           expr_import_error "e_assert"

     | Parsetree.Pexp_constraint (exp, ty) ->
         if ef.F.e_type_annotation then
           build_expr (Pexp_constraint (import_expression ef exp, ty))
         else
           expr_import_error "e_type_annotation"

     | desc ->

        raise (import_error loc (EzyErrors.Not_supported_expression desc))

let import_strit prf strit =
  let loc = strit.Parsetree.pstr_loc in
  let strit_import_error reason =
    import_error loc ~reason (EzyErrors.Not_supported_structure_item strit.Parsetree.pstr_desc) in
  let build_strit desc = {
    pstr_loc = loc ;
    pstr_desc = desc ;
  } in
  let module F = EzyFeatures in
  let explicitly_typed vb = match Parsetree.(vb.pvb_pat, vb.pvb_expr) with
      (_, {Parsetree.pexp_desc = Parsetree.Pexp_constraint _;_}) -> true
    | _ -> false in
  match strit.Parsetree.pstr_desc with

    | Parsetree.Pstr_eval (e, _attrs) ->
        if prf.F.pr_struct_feats.F.s_eval_expr then
          build_strit (Pstr_eval (import_expression prf.F.pr_expr_feats e))
        else
          strit_import_error "s_eval_expr"

    | Parsetree.Pstr_value (Asttypes.Nonrecursive, bindings) ->
        begin match prf.F.pr_struct_feats.F.s_let with
          | Some lf ->
              if prf.F.pr_struct_feats.F.s_annot_optional || List.for_all explicitly_typed bindings then
                if lf.F.l_and || (match bindings with [_] -> true | _ -> false) then
                  build_strit (Pstr_value (import_value_bindings lf.F.l_pattern prf.F.pr_expr_feats bindings))
                else
                  strit_import_error "s_let.l_and"
              else
                strit_import_error "s_annot_optional"
          | None ->
              strit_import_error "s_let"
        end

    | Parsetree.Pstr_value (Asttypes.Recursive, bindings) ->
        begin match prf.F.pr_struct_feats.F.s_let_rec with
          | Some lrf ->
              if prf.F.pr_struct_feats.F.s_annot_optional || List.for_all explicitly_typed bindings then
                if lrf.F.lr_and || (match bindings with [_] -> true | _ -> false) then
                  build_strit (Pstr_rec_value (List.map (import_var_binding prf.F.pr_expr_feats loc) bindings))
                else
                  strit_import_error "s_let_rec.l_and"
              else
                strit_import_error "s_annot_optional"
          | None ->
              strit_import_error "s_let_rec"
        end

    | Parsetree.Pstr_type (_rec_flag, tbindings) ->
        begin match prf.F.pr_struct_feats.F.s_type with
          | Some tf ->
              if tf.F.t_and || (match tbindings with [_] -> true | _ -> false) then
                let build_tbinding td =
                  begin match td.Parsetree.ptype_params, prf.F.pr_struct_feats.F.s_type with
                    | _ :: _, Some { F.t_polymorphic = false ; _ } ->
                      raise (import_error loc (EzyErrors.Not_supported_type_declaration td))
                    | _ ->
                      let kind =
                        match td.Parsetree.ptype_kind, td.Parsetree.ptype_manifest, tf  with
                          | Parsetree.Ptype_abstract, Some td, { F.t_synonym = true ; _ } ->
                              Synonym td
                          | Parsetree.Ptype_variant ctors, None, { F.t_variant = true ; _ } ->
                              (* abeliangrape: the shape of Ptype_kind has changed quite a bit since
                                 3.11. In particular, OCaml now allows records under variant constructors
                                 (type t = T of { ... }) and GADTs (type 'a t = T : int -> int t).
                                 Without adding new things to the languagelevels and EzyAst, we don't want
                                 to support either of these. So we detect them and raise an error,
                                 otherwise we lower the Parsetree to the old shape that Ezy uses. *)
                              let process_ctor = function
                                | Parsetree.{ pcd_args = Pcstr_record _ ; _ } | Parsetree.{ pcd_res = Some _ ; _ } ->
                                  raise (import_error loc (EzyErrors.Not_supported_type_declaration td))
                                | Parsetree.{ pcd_name ; pcd_args = Pcstr_tuple tys ; pcd_loc ; _ } ->
                                  (pcd_name.txt, tys, pcd_loc)
                              in
                              Variant (List.map process_ctor ctors)
                          | Parsetree.Ptype_record fls, None, { F.t_record = Some mutable_allowed ; _ } ->
                              if mutable_allowed || List.for_all (fun lbl -> lbl.Parsetree.pld_mutable = Asttypes.Mutable) fls then
                                Record (List.map Parsetree.(fun ld -> ld.pld_name.txt, ld.pld_mutable, ld.pld_type, ld.pld_loc) fls)
                              else
                                strit_import_error "t_record mutability"
                          | _ ->
                              raise (import_error td.Parsetree.ptype_loc (EzyErrors.Not_supported_type_declaration td)) in
                      let name' = { nm_name = td.Parsetree.ptype_name.txt; nm_loc = Location.none; nm_data = ()} in
                            (* abeliangrape: users are now allowed to write _ in the type_params, so they use a core_type
                               (why they use a core_type instead of an option, I have no clue. Might be missing something?)
                               At any rate, we don't need to support that, or variance annotations, or injectivity annotations.
                               We therefore feel free to simply delete them and lower to the old shape. *)
                      let params' = List.map (fun (ct, (_variance, _injectivity)) -> match ct.Parsetree.ptyp_desc with
                        | Ptyp_var str -> { nm_name = str; nm_loc = Location.none; nm_data = () }
                        | _ -> raise (import_error td.Parsetree.ptype_loc (EzyErrors.Not_supported_type_declaration td))
                        ) td.Parsetree.ptype_params in
                      let td' = { type_params = params'; type_kind = kind } in
                      name', td'
                  end in
                build_strit (Pstr_type (List.map build_tbinding tbindings))
              else
                strit_import_error "t_and"
          | None ->
              strit_import_error "s_type"
        end

      (* The shape of the exn ... AST nodes has changed a lot since OCaml 3.11.
         This is because exception constructors can use GADT syntax
         (but must have res=Some 'exn'), however we aren't going to allow that.
         We will also reject extension constructors with record constructor
         arguments as an import error, even though it's more properly a
         syntax error according to the comment in parsetree.mli. ~abeliangrape *)
    | Parsetree.Pstr_exception {ptyexn_constructor; ptyexn_loc; _} ->
        if prf.F.pr_struct_feats.F.s_exception then
          let (name, ct) = match ptyexn_constructor with
            | Parsetree.{pext_name ; pext_kind = Pext_decl (Pcstr_tuple args, None) ; _} ->
              (pext_name.txt, args)
            | _ -> raise (import_error ptyexn_loc (EzyErrors.Not_supported_structure_item strit.pstr_desc))
            in 
          let name' = {
            nm_name = name ;
            nm_loc = Location.none ;
            nm_data = () ;
          } in
          build_strit (Pstr_exception (name', ct))
        else
          strit_import_error "s_exception"
    | Parsetree.Pstr_open open_decl ->
        if prf.F.pr_struct_feats.F.s_open then
          let lid' = {
            lid_name = begin match open_decl.popen_expr.pmod_desc with
              | Parsetree.Pmod_ident lid -> lid.txt
              | _ -> raise (import_error open_decl.popen_loc (EzyErrors.Not_supported_structure_item strit.pstr_desc))
              end ;
            lid_data = () ;
          } in
          build_strit (Pstr_open lid')
        else
          strit_import_error "s_open"
    | desc -> raise (import_error loc (EzyErrors.Not_supported_structure_item desc))

let import_structure prf str =
  logger#debug "Ocaml ast: %a"
    Printast.implementation str ;
  List.map (import_strit prf) str


(*
let eap ppf ea = Ty.print ppf ea.ea_ty
let pap ppf pa = Ty.print ppf pa.pa_ty
*)


(******************************************************************************)
(*                                COMPARISION                                 *)
(******************************************************************************)

module Equality = struct

  open EzyUtils
  open EzyOcamlmodules
  module Tt = Typedtree

  let logger = new Logger.logger "ast_comp"

  module Conf = struct
    type t = {
      identtbl: Ident.t Ident.tbl ;
      tyvarmap: int TyVarMap.t
    }
    let null = { identtbl = Ident.empty ; tyvarmap = TyVarMap.empty }
  end

  module Error = struct
    type t = string
    let set_context context msg =
      context ^ ": " ^ msg
  end

  module M = struct
    include StateErrorMonadBasis (Conf) (Error)
    let failf ?loc fmt =
      let opt_loc_print ppf = function Some loc -> Format.fprintf ppf "%a: " Location.print loc | _ -> () in
      Format.kfprintf (fun _ -> fail (Format.flush_str_formatter ())) Format.str_formatter ("%a" ^^ fmt) opt_loc_print loc
  end
  module StateErrorMonad = Monad.Make (M)
  open StateErrorMonad.Monad_infix

  let (>>) m n = m >>= fun () -> n

  let rec on_list ?loc f xs ys err =
    match xs, ys with
      | [], [] -> M.ok
      | x :: rem, y :: ren ->
          f x y >>
          on_list ?loc f rem ren err
      | _ -> M.failf ?loc err

  let on_opt ?loc f opt_x opt_y err =
    match opt_x, opt_y with
      | Some x, Some y ->
          f x y
      | None, None ->
          M.ok
      | _ ->
          M.failf ?loc err

  let eq_ident ?loc (id1:Ident.t) (id2:Ident.t) =
    M.inspect >>= fun conf ->
    begin try
      if Ident.find_same id1 conf.Conf.identtbl = id2
      then M.ok
      else
        M.failf ?loc "ident clash: %s vs. %s" (Ident.name id1) (Ident.name id2)
    with Not_found ->
      M.inject $ fun conf ->
      { conf with Conf.identtbl = Ident.add id1 id2 conf.Conf.identtbl }
    end

  let rec eq_path ?loc p p' msg = 
    match p, p' with
      | Path.Pident id, Path.Pident id' ->
          eq_ident ?loc id id'
      | Path.Pdot (q, str), Path.Pdot (q', str') -> 
          if str = str' then
            eq_path ?loc q q' msg
          else
            M.failf ?loc "%s: %s vs. %s" msg (Path.name p) (Path.name p')
      | Path.Papply (q1, q2), Path.Papply (q1', q2') ->
          eq_path ?loc q1 q1' msg >>
          eq_path ?loc q2 q2' msg
      | _ -> M.failf ?loc "%s: path clash (%s vs. %s)" msg (Path.name p) (Path.name p')

  let rec eq_type ?loc env oenv ety ty =
    let ety = EzyEnv.expand_type env ety in
    let ty = Ctype.full_expand ~may_forget_scope:false oenv ty in (* FIXME expand with Ctype.expand_abbrev *)
                                                                  (* abeliangrape: that's gone. *)
    match ety, ty.Types.desc with
      | _, Types.Tlink ty ->
          eq_type ?loc env oenv ety ty
      | Ty.Var tyv, Types.Tvar _ ->
          M.inspect >>= fun conf ->
          begin try
            if (TyVarMap.find tyv conf.Conf.tyvarmap = ty.Types.id)
            then M.ok
            else M.failf ?loc "variable mismatch: %a" TyVar.print tyv
          with Not_found ->
            let f conf = { conf with Conf.tyvarmap = TyVarMap.add tyv ty.Types.id conf.Conf.tyvarmap } in
            M.inject f
          end
      | Ty.Constr (_label, k, tys), Types.Tconstr (k', tys', _ ) ->
(*           let loc = match label with ExtLocation.Source loc -> Some loc | _ -> None in *)
          let rec for_all = function
            | [], [] ->
                M.ok
            | h1 :: t1, h2 :: t2 ->
                eq_type ?loc env oenv h1 h2 >>
                for_all (t1, t2)
            | l1, l2 ->
                M.failf ?loc "type %a vs %a: constructor parameter count: %d vs %d" Path.print k Path.print k' (List.length l1) (List.length l2) in
          let msg = format_str "Constructor (%a) %s vs (%a) %s"
                      (List.print Ty.print ", ") tys (Path.name k)
                      (List.print Types.print ", ") tys' (Path.name k') in
          eq_path ?loc k k' msg >>
          for_all (tys, tys')
      | Ty.Arrow (label, ety1, ety2), Types.Tarrow (Nolabel, ty1, ty2, _) -> 
          let loc = match label with ExtLocation.Source loc -> Some loc | _ -> None in 
          eq_type ?loc env oenv ety1 ty1 >>
          eq_type ?loc env oenv ety2 ty2 
      | Ty.Tuple (_, tys), Types.Ttuple tys' -> 
          on_list ?loc (eq_type ?loc env oenv) tys tys' "tuple"
      | _ -> M.failf ?loc "type: unknown %a vs. %a" Ty.print ety Types.print ty

  (* let eq_type eenv oenv ?(context="") tx ty =
    let tx = EzyEnv.full_expand_type eenv tx in
    M.between (eq_type ~context oenv tx ty)
      (fun _ _ -> logger#debug "Type equal %a vs. %a" Ty.print tx Types.print ty)
      (fun _ _ -> logger#debug "Types not equal %a vs. %a" Ty.print tx Types.print ty) *)

  let eq_constant _c _c' = M.ok
    (* let equality x x' msg =
      if x = x'
      then M.ok
      else M.fail (format_str msg x x') in
    match c, c' with
      | Const_int n, Asttypes.Const_int n' ->
          equality n n' "wrong number (%d vs %d)"
      | Const_char c, Asttypes.Const_char c' ->
          equality c c' "wrong characters (%c vs %c)"
      | Const_string s, Asttypes.Const_string s' ->
          equality s s' "wrong strings (%s vs %s)"
      | Const_float f, Asttypes.Const_float f' ->
          equality f f' "wrong floats (%s vs %s)"
      | _, _  -> M.fail "constant" *)

  let rec eq_pattern s epat opat =
    let loc = epat.ppat_loc in
    eq_type ~loc epat.ppat_data.pa_env opat.Tt.pat_env (TyVarSubst.apply_to_ty s epat.ppat_data.pa_ty) opat.Tt.pat_type >>
    match epat.ppat_desc, opat.Tt.pat_desc with
      | Ppat_any, Tt.Tpat_any ->
          M.ok
      | Ppat_var var, Tt.Tpat_var (ident, _nm) ->
          eq_ident ~loc var.nm_data ident
      | Ppat_constant c, Tt.Tpat_constant c' ->
          eq_constant c c' 
      | Ppat_tuple pats, Tt.Tpat_tuple pats' ->
          on_list ~loc (eq_pattern s) pats pats' "pattern tuple"
      | Ppat_construct (_lid, opt_pat, flag), Tt.Tpat_construct (_lid', _, pats', None) ->
          begin match opt_pat, flag, pats' with
            | Some {ppat_desc = Ppat_tuple pats;_}, true, _ ->
                on_list ~loc (eq_pattern s) pats pats' "constructor arguments"
            | Some pat, _, [pat'] ->
                eq_pattern s pat pat'
            | None, _, [] -> M.ok
            | _ -> M.failf ~loc:epat.ppat_loc "constructor arguments mismatch"
          end
      | Ppat_record fs, Tt.Tpat_record (fs', _cf) ->
          on_list ~loc 
            (eq_pattern s)
            (List.map snd fs)
            (List.map (fun (_,_,y) -> y) fs') "pattern record"
      | Ppat_or (pat1, pat2), Tt.Tpat_or (pat1', pat2', _) ->
          eq_pattern s pat1 pat1' >>
          eq_pattern s pat2 pat2'
      | Ppat_constraint (epat, _), _ ->
          eq_pattern s epat opat
      | Ppat_alias (pat, name), Tt.Tpat_alias (pat', id, _) ->
          eq_ident ~loc:name.nm_loc name.nm_data id >>
          eq_pattern s pat pat'
      | _ -> M.failf ~loc "pattern: %a vs %a" (print_pat ()) epat Tt.print_pat opat

  let eq_pattern s epat opat =
    M.between (eq_pattern s epat opat)
      (fun st ->
         logger#trace "Comparing pattern %a: %s"
           (print_pat ()) epat
           (match st with Result.Ok _ -> "ok" | Result.Error _ -> "failed"))

  let rec eq_binding s (var, expr) = function
    | Tt.{vb_pat={pat_desc=Tpat_var (var',_) ; _}; vb_expr=expr' ; _} ->
        eq_ident ~loc:var.nm_loc var.nm_data var' >>
        m_eq_expression s expr expr'
    | _ -> M.failf ~loc:(Location.span var.nm_loc expr.pexp_loc) "eq_binding"

  and m_eq_expression s eexpr oexpr =
    logger#trace "m_eq_expression %a" (print_expr ()) eexpr ;
    let loc = eexpr.pexp_loc in
    eq_type ~loc eexpr.pexp_data.ea_env oexpr.Tt.exp_env (TyVarSubst.apply_to_ty s eexpr.pexp_data.ea_ty) oexpr.Tt.exp_type >>
    match eexpr.pexp_desc, oexpr.Tt.exp_desc with
      | Pexp_ident { lid_data = path1 ; _ }, Tt.Texp_ident (path2, _, _) ->
          eq_path ~loc path1 path2 (format_str "Identifier %s" (Path.name path1))
      | Pexp_ident _, _ ->
          M.failf ~loc "ident otre"
      | Pexp_constant c, Tt.Texp_constant c' ->
          eq_constant c c'
      | Pexp_constant _, _ ->
          M.failf ~loc "constant otre"
      | Pexp_let (rules, body), Tt.Texp_let (Nonrecursive, rules', body') ->
          let aux (pat, expr) (pat', expr') =
            eq_pattern s pat pat' >>
            m_eq_expression s expr expr' in
          on_list ~loc aux rules 
            (List.map (fun r -> (r.Tt.vb_pat, r.Tt.vb_expr)) rules')
             "m_eq_expression let rules" >>
          m_eq_expression s body body'
      | Pexp_letrec (bindings, body), Tt.Texp_let (Recursive, bindings', body') ->
          on_list ~loc (eq_binding s) bindings bindings' "m_eq_expression letrec bindings" >>
          m_eq_expression s body body'
      | Pexp_function rules, Tt.Texp_function {cases=rules';_} ->
          eq_rules s rules rules'
      | Pexp_apply _ , Tt.Texp_apply (head, args) ->
          let rec aux exp rev_args =
            match exp, rev_args with
              | { pexp_desc = Pexp_apply (exp1, exp2) ; _}, (Nolabel, Some arg) :: rem_args ->
                  m_eq_expression s exp2 arg >>
                  aux exp1 rem_args
              | _, [] ->
                  m_eq_expression s exp head
              | _ -> M.failf ~loc "m_eq_expression Pexp_apply (_, args)" in
          aux eexpr (List.rev args)
      | Pexp_match (exp, _rules), Tt.Texp_match (exp', _rules', _) ->
          (* I don't understand what this function is doing and we don't need
             it anyway. The rules being skipped here are for 'computation patterns',
             which are separated from 'value patterns' by a GADT that couldn't
             have existed when Ezy was written. ~abeliangrape *)
          m_eq_expression s exp exp'
      | Pexp_try (exp, rules), Tt.Texp_try (exp', rules') ->
          m_eq_expression s exp exp' >>
          eq_rules s rules rules'
      | Pexp_tuple exps, Tt.Texp_tuple exps' ->
          on_list ~loc (m_eq_expression s) exps exps' "m_eq_expression Tuple _"
      | Pexp_construct ({ lid_data = path ; _}, opt_exp, flag), Tt.Texp_construct (_ , _, opt_exp') ->
          begin match opt_exp, flag, opt_exp' with
            | None, _, [] -> M.ok
            | None, _, _ -> M.failf ~loc "construct %s, None vs %d" (Path.name path) (List.length opt_exp')
            | Some { pexp_desc = Pexp_tuple exps ; _}, true, exps' ->
                on_list ~loc (m_eq_expression s) exps exps' "construct args"
            | Some exp, false, [exp'] ->
                m_eq_expression s exp exp'
            | _ -> M.failf ~loc ("construct")
          end
      | Pexp_record (fs, opt_exp), Tt.Texp_record {fields=fs'; extended_expression=opt_exp';_} ->
          let _, exps = List.split fs in
          let _, exps' = List.split (Array.to_list fs') in
          let overridden_exp = function
            | Tt.Kept _ -> None
            | Tt.Overridden (_, exp) -> Some exp in
          let exps' = List.filter_map ~f:overridden_exp exps' in
          on_list ~loc (m_eq_expression s) exps exps' "Pexp_record field exps" >>
          on_opt ~loc (m_eq_expression s) opt_exp opt_exp' "Pexp_record optional expression"
      | Pexp_field (exp, _f), Tt.Texp_field (exp', _f', _) ->
          m_eq_expression s exp exp'
      | Pexp_setfield (exp0, _f, exp1), Tt.Texp_setfield (exp0', _f', _, exp1') ->
          m_eq_expression s exp0 exp0' >>
          m_eq_expression s exp1 exp1'
      | Pexp_ifthenelse (exp0, exp1, exp2), Tt.Texp_ifthenelse (exp0', exp1', exp2') ->
          m_eq_expression s exp0 exp0' >>
          m_eq_expression s exp1 exp1' >>
          on_opt ~loc (m_eq_expression s) exp2 exp2' "Pexp_ifthenelse (_, _, option)"
      | Pexp_ifthenelse _, _ ->
          M.failf ~loc "ifthenelse otre"
      | Pexp_sequence (exp0, exp1), Tt.Texp_sequence (exp0', exp1')
      | Pexp_while (exp0, exp1), Tt.Texp_while (exp0', exp1') ->
          m_eq_expression s exp0 exp0' >>
          m_eq_expression s exp1 exp1'
      | Pexp_for (var, exp0, exp1, _, exp2), Tt.Texp_for (id, _, exp0', exp1', _, exp2') ->
          eq_ident ~loc:var.nm_loc var.nm_data id >>
          m_eq_expression s exp0 exp0' >>
          m_eq_expression s exp1 exp1' >>
          m_eq_expression s exp2 exp2'
      | Pexp_assert exp, Tt.Texp_assert exp' ->
          m_eq_expression s exp exp'
      | Pexp_constraint (exp, _), _ ->
          m_eq_expression s exp oexpr
      | _ -> M.failf ~loc "no match %a vs %a" (print_expr ()) eexpr Tt.print_expr oexpr

  and eq_rule s {rule_pat;rule_guard;rule_exp} Tt.{c_lhs;c_guard;c_rhs} =
    eq_pattern s rule_pat c_lhs >>
    on_opt (m_eq_expression s) rule_guard c_guard "guard" >>
    m_eq_expression s rule_exp c_rhs
  and eq_rules s rs rs' =
    on_list (eq_rule s) rs rs' "rules"

  (* let eq_rule s ((pat, expr) as erule) orule =
    M.between (eq_rule s erule orule)
      (fun _ _ -> logger#debug "Comparing rule %a -> %a: ok" (print_pat ()) pat (print_expr ()) expr)
      (fun _ _ -> logger#debug "Comparing rule %a -> %a: failed" (print_pat ()) pat (print_expr ()) expr) *)

  (* let m_eq_expression s eexpr oexpr =
    M.between (m_eq_expression s eexpr oexpr)
      (fun _ _ -> logger#debug "Comparing expression %a: ok" (print_expr ()) eexpr)
      (fun _ _ -> logger#debug "Comparing expression %a: failed" (print_expr ()) eexpr) *)

  let rec m_eq_structure_item s estrit strit =
    let loc = estrit.pstr_loc in
    match estrit, strit with
      | { pstr_desc = Pstr_eval exp ; _ }, Tt.Tstr_eval (exp', _) ->
          m_eq_expression s exp exp' >>
          M.return true
      | { pstr_desc = Pstr_value bindings ; _ }, Tt.Tstr_value (_, bindings') ->
          on_list ~loc (eq_rule s) bindings bindings' "m_eq_structure Pstr_value _" >>
          M.return true
      | { pstr_desc = Pstr_rec_value bindings ; _ }, Tt.Tstr_value (_, bindings') ->
          on_list ~loc (eq_binding s) bindings bindings' "m_eq_structure Pstr_rec_value _" >>
          M.return true
      | { pstr_desc = Pstr_open _ ; _ }, _ ->
          M.return false
      | { pstr_desc = Pstr_type _ ; _ }, Tt.Tstr_type _
      | { pstr_desc = Pstr_exception _ ; _ }, Tt.Tstr_exception _  ->
          M.return true
      | _ -> M.failf ~loc:estrit.pstr_loc "eq_structure"

  and eq_rule s (pat, exp) Tt.{vb_pat ; vb_expr ; _} =
    eq_pattern s pat vb_pat >>
    m_eq_expression s exp vb_expr
  
  let m_eq_structure_item s estrit strit =
    let short ppf strit =
      match strit.pstr_desc with
        | Pstr_eval expr -> Format.fprintf ppf "@[Pstr_eval (%a):@ %a@]" Location.print strit.pstr_loc (EzyAst.print_expr ()) expr
        | Pstr_value bs ->
            let aux ppf (p, _) = EzyAst.print_pat () ppf p in
            Format.fprintf ppf "@[Pstr_value (%a):@ @[%a@]@]"
              Location.print strit.pstr_loc
              (List.print aux ",@ ") bs
        | Pstr_rec_value bs ->
            let aux ppf (n, _) = Format.pp_print_string ppf n.nm_name in
            Format.fprintf ppf "@[Pstr_rec_value (%a):@ @[%a@]@]"
              Location.print strit.pstr_loc
              (List.print aux ",@ ") bs
        | _ -> Format.pp_print_string ppf "<not interesting>" in
    M.between (m_eq_structure_item s estrit strit)
      (fun st ->
         logger#debug "@[%s for: @ %a@]"
           (match st with Result.Ok _ -> "Succeeded" | Result.Error _ -> "Failed")
           short estrit)

  let m_eq_structure (s : TyVarSubst.t) estr ostr =
    let rec aux = function
      | [], [] -> M.ok
      | estrit :: erem, ostrit :: orem ->
          m_eq_structure_item s estrit ostrit >>= fun b ->
          if b then aux (erem, orem) else aux (erem, ostrit :: orem)
      | [], x :: _ -> M.failf "Equality.structure [] %a" Typedtree.print_rough_strit x
      | x :: _, [] -> M.failf "Equality.structure %a []" (EzyAst.print_structure_item ()) x in
    M.between
      (aux (estr, ostr))
      (fun st ->
         logger#info "@[%s comparing ecaml/ocaml typing"
           (match st with Result.Ok _ -> "Success" | Result.Error _ -> "Failed"))

  (*
  let expression s eexpr expr =
    M.perform Conf.null (m_eq_expression eexpr expr s)
      (fun () _st -> None)
      (fun msg _st -> Some msg)
  *)

  let structure (s: TyVarSubst.t) estr str = 
    M.perform Conf.null (m_eq_structure s estr (List.map (fun str' -> str'.Tt.str_desc) str))
      (fun () _st -> None)
      (fun msg _st -> Some msg)
end
let eq_structure = Equality.structure

let apply_substitution s =
  List.map 
    (map_structure_item
      (fun exp_data -> Ty.type_substitute exp_data.ea_ty s )
      (fun pat_data -> Ty.type_substitute pat_data.pa_ty s ))
