
(** The types in this module resemble the data types used in Haack & Wells,
  * 2004. *)

(******************************************************************************)
(*                                   Intro                                    *)
(************************************************************************ {{{ *)
open EzyUtils
open EzyUtils.Infix
open EzyOcamlmodules

let logger = new Logger.logger "coretys"


(* }}} ************************************************************************)
(*                                   TyVar                                    *)
(************************************************************************ {{{ *)
module TyVar : sig
  type tyvar
  include PrintableOrderedType with type t = tyvar
  val fresh: unit -> t
  val id: t -> int
  val none: t
end = struct
  type tyvar = int
  type t = tyvar
  let counter = ref 0
  let fresh () = incr counter; !counter
  let compare (tyv:t) (tyw:t) = tyw - tyv
  let id x = x
  let none = 0

  type printable = t
  let print =
    let a = 97 in
    let num = 25 in
    fun ppf tyv ->
      let postfix = match tyv / num with 0 -> "" | n -> string_of_int n in
      Format.fprintf ppf "'%c%s" (Char.chr (a + tyv mod num)) postfix
end

module TyVarSet = Set.Make(TyVar)
module TyVarMap = Map.Make(TyVar)
      

(* }}} ************************************************************************)
(*                                    Ty                                      *)
(************************************************************************ {{{ *)

(* This cannot be in Ty: "Cannot safely evaluate the definition of the recursively-defined module Ty" *)
module TyImportVarmap =
  Map.Make(struct
             type t = int
             let compare = (-)
             type printable = t
             let print = Format.pp_print_int
           end)

exception Cannot_import of string

module rec Ty: sig
  type t = 
    | Var of TyVar.t 
    | Tuple of ExtLocation.t * t list
    | Constr of ExtLocation.t * Path.t * t list
    | Arrow of ExtLocation.t * t * t 
  type printable = t

  val print: Format.formatter -> t -> unit
  val fresh_var: unit -> t

  val add_type_synonym : string -> t -> unit 
  val lookup_type_synonym : Path.t -> t option

  val set_label : t -> ExtLocation.t -> t
  val get_label : t -> ExtLocation.t

  val fresh_variant: ?create:bool -> ?tyvarmap:TyVar.t TyVarMap.t -> Ty.t -> TyVar.t TyVarMap.t * Ty.t
  val fresh_variants: ?create:bool -> ?tyvarmap:TyVar.t TyVarMap.t -> Ty.t list -> TyVar.t TyVarMap.t * Ty.t list

  val free_vars: t -> TyVarSet.t

  val import: ?tyvarmap:(t TyImportVarmap.t) -> bool -> ExtLocation.t -> Types.type_expr -> t TyImportVarmap.t * t
  val import_list: ?tyvarmap:(t TyImportVarmap.t) -> bool -> ExtLocation.t -> Types.type_expr list -> t TyImportVarmap.t * t list
  val export: t -> Types.type_desc TyVarMap.t ->
    Types.type_expr * Types.type_desc TyVarMap.t

  val valid_instantiation: Ty.t -> Ty.t -> bool

  val tyvars: t -> TyVarSet.t
  val type_substitute: t -> TyVarSubst.t -> t
  val compare: t -> t -> int
  val equal_modulo_tyvarmap : ?tyvarmap:TyVar.t TyVarMap.t -> t -> t -> TyVar.t TyVarMap.t * bool
end = struct

  type t = 
    | Var of TyVar.t 
    | Tuple of ExtLocation.t * t list
    | Constr of ExtLocation.t * Path.t * t list
    | Arrow of ExtLocation.t * t * t 
  type printable = t

  let fresh_var () =
    Var (TyVar.fresh ())

  let rec set_label ty label =
    match ty with
      | Var _ -> ty
      | Tuple (_, tys) -> Tuple (label, List.map (set_label // label) tys)
      | Constr (_, k, tys) -> Constr (label, k, List.map (set_label // label) tys)
      | Arrow (_, tx, ty) -> Arrow (label, set_label tx label, set_label ty label)
  let get_label = function
    | Tuple (label, _) | Constr (label, _, _) | Arrow (label, _, _) -> label
    | _ -> invalid_arg "get_label"

  let rec fresh_variant ?(create=true) ?(tyvarmap=TyVarMap.empty) = function
    | Var tyvar ->
        begin try
          tyvarmap, Ty.Var (TyVarMap.find tyvar tyvarmap)
        with Not_found as exc ->
          if create then
            let ty' = TyVar.fresh () in
            TyVarMap.add tyvar ty' tyvarmap, Ty.Var ty'
          else
            raise exc
        end
    | Tuple (label, tys) ->
        let tyvarmap, tys' = fresh_variants ~create ~tyvarmap tys in
        tyvarmap, Tuple (label, tys')
    | Constr (label, k, tys) ->
        let tyvarmap, tys' = fresh_variants ~create ~tyvarmap tys in
        tyvarmap, Constr (label, k, tys')
    | Arrow (label, tx1, tx2) ->
        let tyvarmap, tx1' = fresh_variant ~create ~tyvarmap tx1 in
        let tyvarmap, tx2' = fresh_variant ~create ~tyvarmap tx2 in
        tyvarmap, Arrow (label, tx1', tx2')

  and fresh_variants ?(create=true) ?(tyvarmap=TyVarMap.empty) tys =
    let aux tyvarmap ty = fresh_variant ~create ~tyvarmap ty in
    List.foldmap aux tyvarmap tys

  let valid_instantiation tx ty =
    logger#debug "Check %a <= %a" Ty.print tx Ty.print ty ;
    let rec aux tyvarmap tx ty =
      match tx, ty with
        | Ty.Var var, _ ->
            begin try
              if compare (TyVarSubst.find tyvarmap var) ty = 0 then
                Some tyvarmap
              else begin
                logger#debug "No match with tyvar %a/%a" Ty.print tx Ty.print ty ;
                None
              end
            with Not_found ->
              Some (TyVarSubst.add tyvarmap var ty)
            end
        | Ty.Tuple (_, txs), Ty.Tuple (_, tys) ->
            aux_list tyvarmap txs tys
        | Ty.Constr (_, p, txs), Ty.Constr (_, q, tys) ->
            if Path.same p q then
              aux_list tyvarmap txs tys
            else begin
              logger#debug "valid_instantiation: no match on type ctors: %s vs %s" (Path.name p) (Path.name q) ;
              None
            end
        | Ty.Arrow (_, tx1, ty1), Ty.Arrow (_, tx2, ty2) ->
            begin match aux tyvarmap tx1 tx2 with
              | Some tyvarmap ->
                  aux tyvarmap ty1 ty2
              | None -> None
            end
        | _ -> None
    and aux_list tyvarmap li1 li2 =
      let f = function
        | None -> (fun _ _ -> None)
        | Some tyvarmap -> (fun tx ty -> aux tyvarmap tx ty) in
      List.fold_left2 f (Some tyvarmap) li1 li2 in
    let _, ty' = fresh_variant ty in
    Option.is_some (aux TyVarSubst.empty tx ty')

  let rec free_vars = function
    | Var tyvar ->
        TyVarSet.singleton tyvar 
    | Tuple (_, tys)
    | Constr (_, _, tys) ->
        List.fold_left TyVarSet.union TyVarSet.empty (List.map free_vars tys)
    | Arrow (_, tx, ty) ->
        TyVarSet.union (free_vars tx) (free_vars ty)

  let rec compare ty1 ty2 =
    let f = function Var _ -> 1 | Tuple _ -> 2 | Constr _ -> 3 | Arrow _ -> 4 in
    match ty1, ty2 with
      | Tuple (l1, tys1), Tuple (l2, tys2) ->
          lexical2 ExtLocation.compare (lexical_list compare) (l1, tys1) (l2, tys2)
      | Constr (l1, k1, tys1), Constr (l2, k2, tys2) ->
          lexical3 ExtLocation.compare Path.compare (lexical_list compare) (l1, k1, tys1) (l2, k2, tys2)
      | Arrow (l1, tx1, ty1), Arrow (l2, tx2, ty2) ->
          lexical3 ExtLocation.compare compare compare (l1, tx1, ty1) (l2, tx2, ty2)
      | Var v, Var w -> TyVar.compare v w
      | _ -> f ty2 - f ty1

  let rec equal_modulo_tyvarmap ?(tyvarmap=TyVarMap.empty) ty1 ty2 =
    match ty1, ty2 with
      | Var v, Var w ->
          begin try
            tyvarmap, TyVarMap.find v tyvarmap = w
          with Not_found ->
            TyVarMap.add v w tyvarmap, true
          end
      | Tuple (_, tys1), Tuple (_, tys2) ->
          equal_modulo_tyvarmap_list ~tyvarmap tys1 tys2
      | Constr (_, p1, tys1), Constr (_, p2, tys2) ->
          if Path.same p1 p2 then
            equal_modulo_tyvarmap_list ~tyvarmap tys1 tys2
          else
            tyvarmap, false
      | Arrow (_, tx1, ty1), Arrow (_, tx2, ty2) ->
          equal_modulo_tyvarmap_list ~tyvarmap [tx1; ty1] [tx2; ty2]
      | _ -> tyvarmap, false

  and equal_modulo_tyvarmap_list ?(tyvarmap=TyVarMap.empty) txs tys =
    match txs, tys with
      | [], [] -> tyvarmap, true
      | tx :: rem1, ty :: rem2 ->
          let tyvarmap, res = equal_modulo_tyvarmap ~tyvarmap tx ty in
          if res then
            equal_modulo_tyvarmap_list ~tyvarmap rem1 rem2 
          else tyvarmap, false
      | _ -> tyvarmap, false

  let rec tyvars = function
    | Var tyvar ->
        TyVarSet.singleton tyvar
    | Tuple (_, tys) ->
        TyVarSet.big_union (List.map tyvars tys)
    | Constr (_, _, tys) ->
        TyVarSet.big_union (List.map tyvars tys)
    | Arrow (_, tx, ty) ->
        TyVarSet.union (tyvars tx) (tyvars ty)

  let rec type_substitute ty s = 
    match ty with
      | Var v ->
          TyVarSubst.apply s v
      | Tuple (l, tys) ->
          Tuple (l, List.map (type_substitute // s) tys)
      | Constr (l, lid, tys) -> 
          Constr (l, lid, List.map (type_substitute // s) tys)
      | Arrow (l, tx, ty) ->
          Arrow (l, type_substitute tx s, type_substitute ty s)

  (*******************************************************************
     [Type Synonym Hack]
  ***********************************************~AbelianGrape *)

  (* Table for recording all (nullary) type synonyms; this is a hack that
     we use to expand type synonyms while emitting constraints.
     ~AbelianGrape *)
  let type_synonyms : (string, Ty.t) Hashtbl.t = Hashtbl.create 10
  let add_type_synonym (str : string) (t : Ty.t) : unit =
    Hashtbl.add type_synonyms str t
  let lookup_type_synonym (p : Path.t) = Hashtbl.find_opt type_synonyms (Path.name p)

  let rec print ppf = function
    | Var tyv ->
        TyVar.print ppf tyv
    |  Constr (_, lid, tys) -> (
        match tys with
          | [] ->
            (* Expand type synonyms. ~AbelianGrape *)
            begin match lookup_type_synonym lid with
              | Some t -> print ppf t
              | None   -> Format.fprintf ppf "%s" (Path.name lid)
            end
          (* Extra parentheses to simplify z3ml. ~AbelianGrape *)
          | _ -> Format.fprintf ppf "((%a) %s)" (List.print print ", ") tys (Path.name lid)
      )
    | Tuple (_, tys) ->
        Format.fprintf ppf "(%a)" (List.print print " * ") tys
    | Arrow _ as ty ->
        print_arrow ppf ty

  and print_arrow ppf = function
    | Arrow (_loc, x, y) ->
        Format.fprintf ppf "(%a -> %a)" print_arrow x print_arrow y
    | ty -> print ppf ty

  let rec import ?(tyvarmap=TyImportVarmap.empty) creative loc oty =
    match oty with
    | { Types.desc = Types.Tarrow (Nolabel, tx, ty, _) ; _} -> 
        let tyvarmap, tx' = import ~tyvarmap creative loc tx in
        let tyvarmap, ty' = import ~tyvarmap creative loc ty in
        tyvarmap, Ty.Arrow (loc, tx', ty')
    | { Types.desc = Types.Tarrow (_label, tx, ty, c) ; _ } -> 
        (* drop the labels to support loading stdlib ~AbelianGrape
        invalid_arg "Ty.import: no support for labelled args" *)
        Types.(Private_type_expr.set_desc oty (Tarrow (Nolabel, tx, ty, c)));
        import ~tyvarmap creative loc oty
    | { Types.desc = Types.Tconstr (path, tys, { contents = Types.Mnil }) ; _ } ->
        let tyvarmap, tys' = import_list ~tyvarmap creative loc tys in
        tyvarmap, Ty.Constr (loc, path, tys')
    | { Types.desc = Types.Tvar _ ; Types.id = id ; _ } ->
        begin try
          tyvarmap, TyImportVarmap.find id tyvarmap
        with Not_found as exn ->
          if creative then
            let ty = fresh_var () in
            TyImportVarmap.add id ty tyvarmap, ty
          else
            raise exn
        end
    | { Types.desc = Types.Ttuple tys ; _ } ->
        let tyvarmap, tys' = import_list ~tyvarmap creative loc tys in
        tyvarmap, Ty.Tuple (loc, tys')
    | { Types.desc = Types.Tlink ty ; _ } ->
        import ~tyvarmap creative loc ty
    | ty ->
        logger#warn "Ty.import %a" Types.print ty ;
        raise (Cannot_import "Ty.import")

  and import_list ?(tyvarmap=TyImportVarmap.empty) creative loc tys =
    let rec aux tyvarmap sofar = function
      | [] -> tyvarmap, List.rev sofar
      | ty :: rem_tys ->
          let tyvarmap, ty' = import ~tyvarmap creative loc ty in
          aux tyvarmap (ty' :: sofar) rem_tys in
    aux tyvarmap [] tys

  let rec export : t -> Types.type_desc TyVarMap.t -> Types.type_expr * Types.type_desc TyVarMap.t
        = fun ty ty_var_map ->
    match ty with
      | Ty.Var tyvar -> 
          begin try
            Btype.newgenty (TyVarMap.find tyvar ty_var_map), ty_var_map
          with Not_found ->
            let e_ty = Btype.newgenvar () in
              e_ty, TyVarMap.add tyvar e_ty.Types.desc ty_var_map
          end
      | Ty.Tuple (_, tys) ->
          let ty_var_map, tys' = export_list ty_var_map tys in
          Btype.newgenty (Types.Ttuple tys'), ty_var_map
      | Ty.Constr (_, lid, tys) ->
          let ty_var_map, tys' = export_list ty_var_map tys in
          Btype.newgenty (Types.Tconstr (lid, tys', ref Types.Mnil)), ty_var_map
      | Ty.Arrow (_, tx, ty) ->
          let e_tx, ty_var_map' = export tx ty_var_map in
          let e_ty, ty_var_map'' = export ty ty_var_map' in
          Btype.newgenty (Types.Tarrow (Nolabel, e_tx, e_ty, Types.Cok)), ty_var_map''
  and export_list ty_var_map tys =
    let f ty (ty_var_map, tys') =
      let ty', ty_var_map = export ty ty_var_map in
      ty_var_map, ty' :: tys' in
    List.fold_right f tys (ty_var_map, [])
end


(* }}} ************************************************************************)
(*                                TyVarSubst                                  *)
(************************************************************************ {{{ *)

and TyVarSubst : sig
  type t = private S of Ty.t TyVarMap.t
  type substitution = Ty.t -> Ty.t
  type printable = t
  val print: Format.formatter -> t -> unit

  val empty: t
  val from_tyvarmap: Ty.t TyVarMap.t -> t
  val from_list: (TyVar.t * Ty.t) list -> t
  val add: t -> TyVar.t -> Ty.t -> t

  (** [find s tyv] returns the value of tyv, if any and raises Not_found else
    *)
  val find: t -> TyVar.t -> Ty.t

  (** [apply s tyv] applies [s] to [tyv]. It returns [Ty.Var tyv] for undefined [tyv]s.
    *)
  val apply: t -> TyVar.t -> Ty.t
  val apply_to_ty: t -> substitution

  val compose: t -> t -> t

  val domain: t -> TyVarSet.t
end = struct

  type t = S of Ty.t TyVarMap.t
  type substitution = Ty.t -> Ty.t
  type printable = t

  let find (S s) tyv = TyVarMap.find tyv s

  let apply (S s) tyv =
    try
      TyVarMap.find tyv s
    with Not_found ->
      Ty.Var tyv

  let apply_to_ty (S s) ty =
    let rec aux = function
      | Ty.Var tyv ->
          apply (S s) tyv
      | Ty.Constr (l, lid, tys) ->
          Ty.Constr (l, lid, List.map aux tys)
      | Ty.Arrow (l, tx1, tx2) ->
          Ty.Arrow (l, aux tx1, aux tx2)
      | Ty.Tuple (l, tys) ->
          Ty.Tuple (l, List.map aux tys) in
    aux ty

  let domain (S s) =
    TyVarMap.fold (fun tyv _ sofar -> TyVarSet.add tyv sofar) s TyVarSet.empty

  let from_tyvarmap s =
    let dom = domain (S s) in
    let value_tyvars =
      TyVarMap.fold (fun _ -> TyVarSet.union << Ty.free_vars) s TyVarSet.empty in
    assert (TyVarSet.is_empty (TyVarSet.inter dom value_tyvars)) ;
    S s

  let from_list = from_tyvarmap << TyVarMap.from_list

  let empty = from_tyvarmap TyVarMap.empty

  let compose (S s) (S t) =
    let f tyvar ty (* from t *) sofar =
      TyVarMap.add tyvar (apply_to_ty (S s) ty) sofar in
    from_tyvarmap (TyVarMap.fold f t s)

  let add (S s) tyv ty =
    from_tyvarmap (TyVarMap.add tyv (apply_to_ty (S s) ty) s)

  let print ppf (S s) =
    let iterator tyvar ty =
      Format.fprintf ppf "%a: %a; " TyVar.print tyvar Ty.print ty in
    TyVarMap.iter iterator s
end

(* }}} ************************************************************************)
(*                               TyVarContainer                               *)
(************************************************************************ {{{ *)

module type TyVarContainer = sig
  type tyvar_container
  val tyvars: tyvar_container -> TyVarSet.t
  val type_substitute: tyvar_container -> TyVarSubst.t -> tyvar_container
end


(******************************************************************************)
(*                                  IntTy                                     *)
(******************************************************************************)
module IntTy = struct

  module TySet = Set.Make(Ty)

  type t = TySet.t
  type printable = t
  type tyvar_container = t

  let empty = TySet.empty

  let add intty ty =
    TySet.add ty intty

  let is_empty = TySet.is_empty

  let list_of_types = TySet.elements

  let size = TySet.cardinal

  let mem intty ty = TySet.mem ty intty

  let combine = TySet.union 

  let map_to_list intty f =
    TySet.fold (fun ty sofar -> f ty :: sofar) intty []

  let tyvars intty =
    let folder ty sofar = TyVarSet.union (Ty.tyvars ty) sofar in
    TySet.fold folder intty TyVarSet.empty

  let fold intty f init =
    TySet.fold f intty init

  let type_substitute intty s =
    TySet.map (Ty.type_substitute // s) intty

  let print ppf intty =
    Format.fprintf ppf "I%a@?" TySet.print intty

end


(* }}} ************************************************************************)
(*                                  TyEnv                                     *)
(************************************************************************ {{{ *)
module TyEnv = struct (* maps String.t to IntTy.t *)

  type t = IntTy.t StringMap.t
  type tyvar_container = t
  type printable = t

  let empty = StringMap.empty
  let is_empty = StringMap.is_empty

  let substitute env var intty = StringMap.add var intty env

  let forget env var = StringMap.remove var env

  let combine env1 env2 =
    let folder var intty sofar =
      let new_intty =
        if StringMap.mem var sofar then
          IntTy.combine intty (StringMap.find var sofar)
        else
          intty in
      StringMap.add var new_intty sofar in
    StringMap.fold folder env1 env2 

  let lookup env var =
    if StringMap.mem var env then
      StringMap.find var env
    else
      IntTy.empty

  let tyvars env =
    let folder _ intty sofar = TyVarSet.union sofar (IntTy.tyvars intty) in
    StringMap.fold folder env TyVarSet.empty

  let domain env =
    let adder var _ = StringSet.add var in
    StringMap.fold adder env StringSet.empty

  let type_substitute env s =
    StringMap.map (IntTy.type_substitute // s) env

  let print ppf env =
    Format.fprintf ppf "{" ;
    StringMap.iter (
      fun var intty ->
        Format.fprintf ppf "%a: %a; " String.print var IntTy.print intty
    ) env ;
    Format.fprintf ppf "}@?"

  let to_list env =
    let folder var intty sofar = (var, intty) :: sofar in
    StringMap.fold folder env []

end
(* }}} *)
