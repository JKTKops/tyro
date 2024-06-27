open EzyOcamlmodules
open EzyTypingCoreTypes
open EzyConstraints
open EzyUtils.Infix
open EzyUtils

(*
Ident.create_local has generically replaced Ident.create.
See the diff between ocaml/blob/3.11/Typing/Ident.ml and
ocaml/blob/4.13/Typing/Ident.ml.
~abeliangrape   
*)

let logger = new Logger.logger "env"

module EzyPredef = struct
  open Ty
  let bool_type label = Constr (label, Predef.path_bool, [])
  let unit_type label = Constr (label, Predef.path_unit, [])
  let int_type label = Constr (label, Predef.path_int, [])
  let char_type label = Constr (label, Predef.path_char, [])
  let string_type label = Constr (label, Predef.path_string, [])
  let float_type label = Constr (label, Predef.path_float, [])
  let exn_type label = Constr (label, Predef.path_exn, [])
  let array_type label ty = Constr (label, Predef.path_array, [ty])
end

(* Ezy originally hacked this definition directly into the Ident module.
   ~abeliangrape *)
let no_ident = Ident.create_local ""

type binding = Mono | Poly

type value_desc = {
  val_kind: Types.value_kind ;
  val_binding : binding ;
  val_scheme : Scheme.t ;
  val_loc: ExtLocation.t ;
}

type type_kind =
  | Abstract
  | Synonym of Ty.t
  | Variant of Ty.t list StringMap.t
  | Record of (EzyAsttypes.mutable_flag * Ty.t) StringMap.t

type type_decl = {
  type_params: Ty.t list ;
  type_kind: type_kind ;
  type_loc: ExtLocation.t ;
}

type ctor_tag =
  | Ctor_regular of Path.t
  | Ctor_exception of Path.t

let path_of_tag = function
  | Ctor_regular path | Ctor_exception path -> path

type ctor_desc = {
  ctor_result: Ty.t ;
  ctor_args: Ty.t list ;
  ctor_tag: ctor_tag ;
}

type field_desc = {
  fld_result: Ty.t ;
  fld_arg: Ty.t ;
  fld_mutable: EzyAsttypes.mutable_flag ;
  fld_path: Path.t ;
}

type t = {
  values: (Path.t * value_desc) Ident.tbl ;
  types: (Path.t * type_decl) Ident.tbl ;
  modules: (Path.t * t) Ident.tbl ;
  ctors: ctor_desc StringMap.t ;
  fields: field_desc StringMap.t ;
}

let fresh_ctor_desc ?tyvarmap cd = 
  let tyvarmap, result = Ty.fresh_variant ?tyvarmap cd.ctor_result in
  let tyvarmap, args = Ty.fresh_variants ~tyvarmap cd.ctor_args in
  tyvarmap, { ctor_result = result; ctor_args = args; ctor_tag = cd.ctor_tag }

let fresh_field_desc ?tyvarmap fd =
  let tyvarmap, result = Ty.fresh_variant ?tyvarmap fd.fld_result in
  let tyvarmap, arg = Ty.fresh_variant ~tyvarmap fd.fld_arg in
  tyvarmap, { fd with fld_result = result ; fld_arg = arg }

let persistent_structures =
  (* extra 'ref' indirection breaks recursion on modules with members
     who refer to that module by name. This requires us to lookup the module
     that we are currently trying to import. *)
  (Hashtbl.create 17 : (string, Ident.t * t ref) Hashtbl.t)

let allowed_module_names = ref None
let forbidden_module_names = ref []

let allow_modules l = allowed_module_names := Some l
let forbid_modules l = forbidden_module_names := l

  

let empty = {
  values = Ident.empty ;
  types = Ident.empty ;
  modules = Ident.empty ;
  ctors = StringMap.empty ;
  fields = StringMap.empty ;
}

let import_signature' = (* break recursion *)
  ref ((fun _ _ -> assert false) : Path.t -> Types.signature -> t)

let import_value_desc val_lid vd =
  let name = Longident.last val_lid in
  let eloc = ExtLocation.Interface val_lid in
  let _tyvarmap, ty = Ty.import true eloc vd.Types.val_type in
  {
    val_kind = vd.Types.val_kind ;
    val_binding = Poly ;
    val_scheme = Scheme.poly name ty ExtLocationMap.empty eloc ;
    val_loc = eloc ;
  }

let store_value id path vd env =
  { env with values = Ident.add id (path, vd) env.values }

let loc_for_path path = ExtLocation.Interface (Path.to_lident path)

let store_type id path td env =
  let ctors_of_kind = function
    | Variant vs -> StringMap.to_list vs
    | _ -> [] in
  let fields_of_kind = function
    | Record fs -> StringMap.to_list fs
    | _ -> [] in
  let path_aux name = function
    | Path.Pident _ ->
        Path.Pident (Ident.create_local name)
    | Path.Pdot (path', _) ->
        Path.Pdot (path', name)
    | _ -> failwith "store_type:add_ctor" in
  let result = Ty.Constr (loc_for_path path, path, td.type_params) in
  let add_ctor ctors (k, tys) =
    let cd = {
      ctor_result = result ;
      ctor_args = tys ;
      ctor_tag = Ctor_regular (path_aux k path) ;
    } in
    StringMap.add k cd ctors in
  let add_field fields (f, (m, ty)) =
    let fd = {
      fld_mutable = m ;
      fld_result = result ;
      fld_arg = ty ;
      fld_path = path_aux f path ;
    } in
    logger#debug "Adding field %s" f ;
    StringMap.add f fd fields in
  { env with
    types = Ident.add id (path, td) env.types ;
    ctors = List.fold_left add_ctor env.ctors (ctors_of_kind td.type_kind) ;
    fields = List.fold_left add_field env.fields (fields_of_kind td.type_kind) }
let store_module id path md env =
  { env with modules = Ident.add id (path, md) env.modules }
let store_exception id path tys env =
  let td = {
    ctor_args = tys ;
    ctor_result = EzyPredef.exn_type (loc_for_path path) ;
    ctor_tag = Ctor_exception path
  } in
  { env with ctors = StringMap.add (Ident.name id) td env.ctors }

(* Returns 'None' if we aren't able to import something. In a situation where
   the import was _required_, this should result in an error; however, sometimes,
   in our context, we're happy to throw things away, because students can't use
   them. Open types fall under this bucket. ~AbelianGrape. *)
let import_type_decl type_lid td =
  let tyvarmap, params = Ty.import_list true (ExtLocation.Interface type_lid) td.Types.type_params in
  let kind =
    match td.Types.type_kind, td.Types.type_manifest with
      | Types.Type_abstract, None ->
          Some Abstract
      | _, Some ty -> (* No matter what's on the left, if we have a manifest, declare a synonym.
                         This isn't exactly correct but.... yeah, whatever. *)
          let _tyvarmap, ty' = Ty.import false (ExtLocation.Interface type_lid) ~tyvarmap ty in
          Some (Synonym ty')
      | Types.Type_variant (vs, _), None ->
          let f tyvarmap cdecl =
            let tys = match cdecl.Types.cd_args with
              | Types.Cstr_tuple tys -> tys
              | _ -> failwith "can't import constructor with record args. Internal error?"
              in
            let k = Ident.name cdecl.Types.cd_id in
            let tyvarmap, tys' = Ty.import_list false (ExtLocation.Interface type_lid) ~tyvarmap tys in
            tyvarmap, (k, tys') in
          let vs' = snd (List.foldmap f tyvarmap vs) in
          Some (Variant (StringMap.from_list vs'))
      | Types.Type_record (fs, _), None ->
          let f tyvarmap ld =
            let f = Ident.name ld.Types.ld_id
            and m = ld.Types.ld_mutable
            and ty = ld.Types.ld_type in
            let tyvarmap, ty' = Ty.import false (ExtLocation.Interface type_lid) ~tyvarmap ty in
            tyvarmap, (f, (m, ty')) in
          let fs' = snd (List.foldmap f tyvarmap fs) in
          Some (Record (StringMap.from_list fs'))
      | Types.Type_open, None -> (* type ... = [> ... | ... ]*)
          None
  in match kind with
    | Some kind -> 
      Some { type_params = params ;
             type_kind = kind ;
             type_loc = ExtLocation.Interface type_lid }
    | None -> None

let import_ctor_desc path cd =
  let loc = loc_for_path path in
  let _tyvarmap, result = Ty.import false loc cd.Types.cstr_res in
  let _tyvarmap, args = Ty.import_list false loc cd.Types.cstr_args in
  {
    ctor_result = result ;
    ctor_args = args ;
    ctor_tag = Ctor_exception path ;
  }

let check_module_validity name =
  let allowed =
    match !allowed_module_names with
      | None -> true
      | Some l -> List.mem name l in
  let forbidden =
    List.mem name !forbidden_module_names in
  if not allowed || forbidden then
    EzyErrors.raise_fatal (EzyErrors.Module_not_found (Longident.Lident name))

let rec add_oenv env oenv =

  let wrapper env f x =
    try f x with Cannot_import _ -> env in

  let add_value env path = wrapper env @@ fun vd ->
    let ident = Ident.create_local (Path.last path) in (* I think this is right? ~abeliangrape *)
    let vd' = import_value_desc (Path.to_lident path) vd in
    store_value ident path vd' env in

  let add_type env path = wrapper env @@ fun td ->
    let ident = Ident.create_local (Path.last path) in (* same as above. *)
    let td' = import_type_decl (Path.to_lident path) td in
    match td' with
    | None -> env (* couldn't import; just ignore it. Otherwise, we break on Stdlib. *)
    | Some td' -> store_type ident path td' env
  in

  let add_exception env = wrapper env @@ fun cd ->
    let name = cd.Types.cstr_name in
    match cd.Types.cstr_tag with
      | Types.Cstr_extension (path, _) ->
          let cd' = import_ctor_desc path cd in
          { env with ctors = StringMap.add name cd' env.ctors }
      | _ -> env in

    (* Very incomplete - we only store actual modules, we ignore functors,
       etc. Just enough to make things like List.map work out of the box.
       ~AbelianGrape. *)
  let add_module env path md =
    let ident = Ident.create_local (Path.last path) in (* same as value and type? *)
    match md.Types.md_type with
      | Types.Mty_ident _ -> env (* abstract - do nothing *)
      | Types.Mty_alias p ->
        let md = find_module p env in
        store_module ident path md env
      | Types.Mty_functor _ -> env (* functor - ignore *)
      | Types.Mty_signature sg ->
        let md = !import_signature' path sg in
        store_module ident path md env
    in

  let env = Env.fold_values (fun _ path vd env -> add_value env path vd) None oenv env in
  let env = Env.fold_types (fun _ path td env -> add_type env path td) None oenv env in
  let env = Env.fold_constructors (fun cd env -> add_exception env cd) None oenv env in
  let env = Env.fold_modules (fun _ path md env -> add_module env path md) None oenv env in
  env

and find_pers_struct ident =
  let name = Ident.name ident in
  check_module_validity name ;
  try
    (* is something there? *)
    let r = snd (Hashtbl.find persistent_structures name) in
    (* If yes, return a lazy that will look up the proper thing when we're done. *)
    fun () -> !r
  with Not_found ->
    let oenv = Env.open_pers_signature name Env.empty in
    let oenv = match oenv with
      | Ok oenv -> oenv
      | Error `Not_found -> raise Not_found
    in
    let r = ref empty in
    Hashtbl.add persistent_structures name (ident, r);
    let env = add_oenv empty oenv in
    r := env;
    fun () -> env

and seek_module name env =
  check_module_validity name ;
  let (ident, (_path, md)) = Ident.find_name name env.modules in
  ident, md

and find_module path env =
  match path with
    | Path.Pident ident ->
      begin try
        find_pers_struct ident ()
      with Not_found -> (* not persistent, check env *)
        (* re-raises Not_found if it's not there! *)
        snd (Ident.find_same ident env.modules)
      end
    | Path.Pdot (path, name) ->
      let md_env = find_module path env in
      snd (seek_module name md_env)
    | Path.Papply _ ->
        invalid_arg "EzyEnv.find_module"

(* add an ezyEnv to our existing ezyEnv. *)
let add_env env env' =
  let add store id (path, x) env = store id path x env in
  let add_all proj store env =
    Ident.fold_all (add store) (proj env') env in
  let env = add_all (fun e -> e.values) store_value env in
  let env = add_all (fun e -> e.types) store_type env in
  let env = add_all (fun e -> e.modules) store_module env in
  let right_bias _ _ y = Some y in
  let env = { env with
              ctors = StringMap.union right_bias env.ctors env'.ctors;
              fields = StringMap.union right_bias env.fields env'.fields } in
  env

let open_module name env = 
  check_module_validity name ;
  let oenv = Env.open_pers_signature name Env.empty in
  match oenv with
    | Ok oenv -> Ident.create_persistent name, add_oenv env oenv
    | Error `Not_found -> (* search the env modules instead *)
      let (ident, (_path, md)) = Ident.find_name name env.modules in
      ident, add_env env md

let find_pers_struct ident = find_pers_struct ident ()

let lookup_pers_struct name =
  try
    let (i, r) = Hashtbl.find persistent_structures name in
    i, !r
  with Not_found ->
    let ident = Ident.create_local name in
    ident, find_pers_struct ident


let lookup_module lid _env =
  match lid with
    | Longident.Lident name ->
        let ident, md = lookup_pers_struct name in
        Path.Pident ident, md
    | Longident.Ldot _ ->
        not_implemented "EzyEnv.lookup_module"
    | Longident.Lapply _ ->
        invalid_arg "EzyEnv.lookup_module"

let add_value id vd env =
  store_value id (Path.Pident id) vd env
let add_module id md env =
  store_module id (Path.Pident id) md env
let add_type id td env =
  store_type id (Path.Pident id) td env


let enter store_func name data env =
  let id = Ident.create_local name in
  id, store_func id (Path.Pident id) data env

let enter_value name vd env =
  enter store_value name vd env
let enter_type name td env =
  enter store_type name td env
let enter_exception name tys env =
  enter store_exception name tys env

let find proj path env =
  match path with
    | Path.Pident ident ->
        snd (Ident.find_same ident (proj env))
    | Path.Pdot (path, name) ->
        let md = find_module path env in
        snd (snd (Ident.find_name name (proj md)))
    | Path.Papply _ ->
        invalid_arg "EzyEnv.find"

let find_value =
  find (fun env -> env.values)
let find_type =
  find (fun env -> env.types)

let lookup proj lid (env:t) =
  match lid with
    | Longident.Lident name ->
        let id, x = Ident.find_name name (proj env) in
        Path.Pident id, x
    | Longident.Ldot (lid, name) ->
        begin try
          let path, md_env = lookup_module lid env in
          let _, x = Ident.find_name name (proj md_env) in
          Path.Pdot (path, name), x
        with
        | Not_found ->
          (* try locally opening the module in case it's persistent.
             This is absolutely a hack, and the right thing to do is
             probably to fix lookup_module. ~AbelianGrape *)
          let rec open_chain env = function
            | Longident.Lident n -> snd @@ open_module n env
            | Longident.Ldot (lid, n) ->
              snd @@ open_module n @@ open_chain env lid
            | Longident.Lapply _ -> invalid_arg "EzyEnv.lookup"
          in
          let id, x = Ident.find_name name (proj (open_chain env lid)) in
          (* THIS IS THE WRONG PATH! We just don't need the right one, and constructing
             it given the hack above seems very hard. ~AbelianGrape *)
          Path.Pident id, x
        end

    | Longident.Lapply _ ->
        invalid_arg "EzyEnv.lookup"

(* We used to have Ident.keys but it's either gone or was an Ezy hack
   (I've run into a couple other Ezy hacks already). This is not a satisfactory
   definition of this function but it should do the job. *)
let get_keys tbl =
  let key_list = ref [] in
  Ident.fold_all (fun id _ () -> key_list := id :: !key_list) tbl ();
  !key_list (* we could reverse this but seems fine not to *)

let lookup proj lid env =
  try snd (lookup proj lid env)
  with Not_found as exn ->
    logger#debug "Could not find %a in %a" Longident.print lid (List.print Ident.print ", ") (get_keys (proj env));
    raise exn

let lookup_value = lookup (fun env -> env.values)
let lookup_type = lookup (fun env -> env.types)

let lookup_shortcut proj lid env =
  let aux name env =
    StringMap.find name (proj env) in
  match lid with
    | Longident.Lident name ->
        aux name env
    | Longident.Ldot (lid, name) ->
        aux name (snd (lookup_module lid env))
    | Longident.Lapply _ ->
        invalid_arg "EzyEnv.lookup_shortcut"

let lookup_ctor ?tyvarmap lid env =
  fresh_ctor_desc ?tyvarmap (lookup_shortcut (fun env -> env.ctors) lid env)
let lookup_field ?tyvarmap lid env =
  fresh_field_desc ?tyvarmap (lookup_shortcut (fun env -> env.fields) lid env )

let () = import_signature' := fun path sg ->
  let lid = Path.to_lident path in
  let f env = function
    | Types.Sig_value (ident, vd, _) ->
        add_value ident (import_value_desc (Longident.Ldot (lid, Ident.name ident)) vd) env
    | Types.Sig_type (ident, td, _, _) ->
        begin match import_type_decl (Longident.Ldot (lid, Ident.name ident)) td with
        | None -> env
        | Some td' -> add_type ident td' env
        end
    | Types.Sig_typext (ident, ed, _, _) ->
        let _tyvarmap, tys = Ty.import_list false (ExtLocation.Interface lid) ed.ext_type_params in
        snd (enter_exception (Ident.name ident) tys env)
    | Types.Sig_module (ident, _, Types.{md_type = Mty_signature sg ; _}, _, _) ->
        let path = Path.Pdot (path, Ident.name ident) in
        let sg_env = !import_signature' path sg in
        store_module ident path sg_env env
    | _ -> env in
  List.fold_left f empty sg

let import_signature = !import_signature' 

(** Imports all top level values, types and exceptions of an Env.t.
  *)
let import oenv =
  add_oenv empty oenv

(* Not currently used ~abeliangrape
exception Cannot_expand
*)

(* Not currently used. Under assert false was commented. ~abeliangrape
let find_type_expansion _env _path =
  assert false
  let td = find_type env path in
  match td.type_kind with
    | Synonym body -> td.type_params, body
    | _ -> raise Not_found
 *)

(* Not currently used. Under assert false was commented. ~abeliangrape
let expand_abbrev _env _ty =
  assert false
  match ty.Ty.desc with
    | Ty.Constr (path, args) ->
        let params, body = 
          let td = find_type env path in
          match td.type_kind with
            | Synonym body -> td.type_params, body
            | _ -> raise Cannot_expand in
        let extract_tyvar = function { Ty.desc = Ty.Var tyvar } -> tyvar | _ -> assert false in
        let tyvars = List.map extract_tyvar params in
        let s = TyVarSubst.from_list (List.combin tyvars args) in
        TyVarSubst.apply_to_ty s body
    | Ty.Tuple tys ->
 *)

let expand_constr env label path args k =
  begin try
    let td = find_type path env in
    begin match td.type_kind with
      | Synonym tx ->
          let extract_tyvar = function Ty.Var tyvar -> tyvar | _ -> assert false in
          let tyvars = List.map extract_tyvar td.type_params in
          let s = TyVarSubst.from_list (List.combine tyvars args) in
          k env (TyVarSubst.apply_to_ty s tx)
      | _ ->
          Ty.Constr (label, path, args)
    end
  with Not_found as exn ->
    logger#error "Could not find %s to expand." (Path.name path) ;
    raise exn
  end

let expand_type env = function
  | Ty.Var _ | Ty.Tuple _ | Ty.Arrow _ as ty -> ty
  | Ty.Constr (label, path, args) ->
      expand_constr env label path args (const id)

let rec full_expand_type env = function
  | Ty.Var _ as ty ->
      ty
  | Ty.Tuple (label, tys) ->
      Ty.Tuple (label, List.map (full_expand_type env) tys)
  | Ty.Arrow (label, tx1, tx2) ->
      Ty.Arrow (label, full_expand_type env tx1, full_expand_type env tx2) 
  | Ty.Constr (label, path, args) ->
      expand_constr env label path args full_expand_type

let full_expand_type env ty =
  between $ full_expand_type env $ ty $
    fun ty' ->
      logger#trace "full_expanded_type %a -> %a" Ty.print ty Ty.print ty'

let cyclic_abbrev _env _ty =
  assert false
(*   let  *)

let print ?(s=TyVarSubst.empty) everything ppf env =
  let print_value ppf ident =
    let vd = find_value (Path.Pident ident) env in
     match vd.val_loc with (* only print locally defined values *) 
       | ExtLocation.Interface _ when not everything -> () 
       | _ ->
          Format.fprintf ppf "@[%s: %s%a;@]@ "
            (Ident.name ident)
            (match vd.val_binding with Mono -> "MONO " | Poly -> "")
            Ty.print (TyVarSubst.apply_to_ty s vd.val_scheme.ty)
  in
  let print_kind ppf = function
    | Abstract -> Format.pp_print_string ppf "<abstr>"
    | Synonym ty -> Ty.print ppf ty
    | Variant vs ->
        let aux k = function
          | [] -> Format.fprintf ppf "| %s " k
          | tys -> Format.fprintf ppf "| %s of %a " k (List.print Ty.print " * ") tys in
        StringMap.iter aux vs
    | Record fs ->
        let p ppf (m, ty) =
          (* I think Ezy was hacking into Printast to expose this...
             I don't know why it's not exposed, but it's a short function anyway. *)
          let fmt_mutable_flag f = function
            | EzyAsttypes.Immutable -> Format.fprintf f "Immutable"
            | EzyAsttypes.Mutable   -> Format.fprintf f "Mutable"
          in
          Format.fprintf ppf "%a%a"
            fmt_mutable_flag m
            Ty.print ty in
        StringMap.print p ppf fs in
  let print_type ppf ident =
    let td = find_type (Path.Pident ident) env in
    match td.type_loc with (* only print locally defined values *) 
      | ExtLocation.Interface _ when not everything -> ()
      | _ ->
          Format.fprintf ppf "@[type (%a) %s = %a;@]@ "
            (List.print Ty.print ", ") td.type_params
            (Ident.name ident)
            print_kind td.type_kind
  in
  Format.fprintf ppf
    "@[Values: %a@]@ @[Types: %a@]@]"(*"@[Ctors:@ %a@]@ @[Fields:@ %a@]"*)
    (List.print print_value "") (get_keys env.values)
    (List.print print_type "") (get_keys env.types)
(*
    StringMap.KeySet.print (StringMap.keys env.ctors)
    StringMap.KeySet.print (StringMap.keys env.fields)
 *)
(*
  Format.fprintf ppf
    "Values: %a\nTypes: %a\nCtors: %a\nFields: %a"
    (List.print print_value "") (Ident.keys env.values)
    (List.print print_type "") (Ident.keys env.types)
    StringMap.KeySet.print (StringMap.keys env.ctors)
    StringMap.KeySet.print (StringMap.keys env.fields)
 *)

let () =
  forbid_modules ["Format"; "Printf"; "Scanf"] ;
