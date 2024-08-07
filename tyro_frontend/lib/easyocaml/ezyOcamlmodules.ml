open EzyUtils

(* from Camp4/Printers/OCaml.ml *)
let infix_lidents = ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"]
let is_infix =
  let first_chars = [':'; '='; '<'; '>'; '|'; '&'; '$'; '@'; '^'; '+'; '-'; '*'; '/'; '%'; '\\']
  and infixes =
    List.fold_right StringSet.add infix_lidents StringSet.empty
  in fun s -> (StringSet.mem s infixes
               || (s <> "" && List.mem s.[0] first_chars))

module Location = struct
  module Original = Location
  type location = Location.t = {
    loc_start: Lexing.position;
    loc_end: Lexing.position;
    loc_ghost: bool;
  }
  include Location
  type printable = t
  let print ppf loc =
    (* Format.fprintf ppf "%d-%d" loc.loc_start.Lexing.pos_cnum loc.loc_end.Lexing.pos_cnum *)
    let col pos = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
    if loc.loc_start.Lexing.pos_lnum = loc.loc_end.Lexing.pos_lnum then
      Format.fprintf ppf "%d;%d-%d"
        loc.loc_start.Lexing.pos_lnum
        (col loc.loc_start)
        (col loc.loc_end)
    else
      Format.fprintf ppf "%d;%d-%d;%d"
        loc.loc_start.Lexing.pos_lnum
        (col loc.loc_start)
        loc.loc_end.Lexing.pos_lnum
        (col loc.loc_end)

  let compare l1 l2 =
    let compare_position p1 p2 =
      p1.Lexing.pos_cnum - p2.Lexing.pos_cnum in
    match lexical compare_position (l1.loc_start, l1.loc_end) (l2.loc_start, l2.loc_end) with
      | 0 -> Stdlib.compare l1 l2
      | n -> n

  let span l1 l2 =
    { loc_start = l1.loc_start ;
      loc_end = l2.loc_end ;
      loc_ghost = l1.loc_ghost || l2.loc_ghost }
end

module Longident = struct
  module Original = Longident
  include Longident
  let rec compare li1 li2 =
    match li1, li2 with
      | Lident n1, Lident n2 -> String.compare n1 n2
      | Ldot (li1, n1), Ldot (li2, n2) ->
          lexical2 compare String.compare (li1, n1) (li2, n2)
      | Lapply _, Lapply _ -> invalid_arg "Longident.compare"
      | li1, li2 ->
          let f = function Lident _ -> 1 | Ldot _ -> 2 | Lapply _ -> 3 in
            f li2 - f li1
  type printable = t
  let none = Lident ""
  let rec tail = function
    | Lident nm | Ldot (_, nm) -> nm
    | Lapply (_, lid) -> tail lid
  let rec print =
    let print_tail ppf nm =
      if is_infix nm then
        Format.fprintf ppf "(%s)" nm
      else Format.pp_print_string ppf nm in
    fun ppf -> function
      | Lident nm ->
          print_tail ppf nm
      | Ldot (lid, nm) ->
          Format.fprintf ppf "%s.%a" (String.concat "." (flatten lid)) print_tail nm
      | Lapply (lid1, lid2) ->
          Format.fprintf ppf "(%a) %a" print lid1 print lid2
end

module LongidentMap = Map.Make(Longident)

module Path = struct
  module Original = Path
  include Path
  type printable = t
  let none = Pident (Ident.create_predef "<none>")
  let rec print ppf = function
    | Pident id ->
        Format.pp_print_string ppf (Ident.unique_name id)
    | Pdot (p, n) ->
        Format.fprintf ppf "%a.%s" print p n
    | Papply (p1, p2) ->
        Format.fprintf ppf "%a (%a)" print p1 print p2
  let rec compare p1 p2 =
    match p1, p2 with
      | Pident id1, Pident id2 ->
          Stdlib.compare id1 id2
      | Pdot (p1, n1), Pdot (p2, n2) ->
          lexical2 compare String.compare (p1, n1) (p2, n2)
      | Papply _, Papply _ -> invalid_arg "Path.compare"
      | p1, p2 ->
          let f = function Pident _ -> 1 | Pdot _ -> 2 | Papply _ -> 3 in
            f p2 - f p1
  let last = function
    | Pident id -> Ident.name id
    | Pdot (_, name) -> name
    | Papply _ -> invalid_arg "Path.last"
  let rec to_lident = function
    | Pident id ->
        Longident.Lident (Ident.name id)
    | Pdot (p, str) ->
        Longident.Ldot (to_lident p, str)
    | Papply (p1, p2) ->
        Longident.Lapply (to_lident p1, to_lident p2)
end

module PathSet = Set.Make(Path)

module LocationSet = Set.Make(Location)

module ExtLocation = struct
  type t = 
    | Interface of Longident.t
    | Source of Location.t
  type printable = t

  let compare loc1 loc2 =
    match loc1, loc2 with
      | Interface li1, Interface li2 ->
          Longident.compare li1 li2
      | Interface _, Source _ -> -1
      | Source _, Interface _ -> 1
      | Source loc1, Source loc2 -> 
          Location.compare loc1 loc2

  let print ppf = function
    | Interface p -> 
        Longident.print ppf p
    | Source loc ->
        Location.print ppf loc

  let none = Source Location.none
end

module Types = struct
  include Types
  let rec print ppf texp =
    match texp.desc with
      | Tvar _ -> Format.fprintf ppf "'%d" texp.id
      | Tarrow (_, tx, ty, _) -> Format.fprintf ppf "(%a -> %a)" print tx print ty
      | Tconstr (p, [], _) ->
          Format.fprintf ppf "%s" (Path.name p)
      | Tconstr (p, tys, _) ->
          Format.fprintf ppf "(%a) %s" (fun ppf -> List.iter (print ppf)) tys (Path.name p)
      | Tnil -> Format.pp_print_string ppf "N"
      | Tlink ty -> Format.fprintf ppf "-%a" print ty
      | Tpoly (ty, tys) -> (* ~AbelianGrape *)
          List.print print " " ppf tys;
          Format.pp_print_string ppf ". ";
          print ppf ty
      | Ttuple tys ->
          Format.pp_print_string ppf "(" ;
          List.print print " * " ppf tys ;
          Format.pp_print_string ppf ")"
      | Tvariant _ -> (* AbelianGrape *)
          Format.fprintf ppf "[<row variant>]"
      | Tsubst _ -> failwith "Types.print Tsubst _ not implemented"
      | Tfield (name, Fpresent, t, _) -> (* ~AbelianGrape *)
          Format.fprintf ppf "<...; %s : %a; ...>" name print t
      | Tfield _ -> failwith "Types.print Tfield (_, not Fpresent, _) not implemented"
      | Tobject (t, {contents=None}) -> (* ~AbelianGrape *)
          let rec collect_fields acc t = match t.desc with
            | Tfield (name, _, t, more) -> collect_fields ((name,t) :: acc) more
            | Tnil -> List.rev acc
            | _ -> List.rev (("_", t) :: acc)
          in let collect_fields = collect_fields [] in
          let print_field ppf (name,t) = Format.fprintf ppf "%s : %a" name print t in
          Format.pp_print_string ppf "< ";
          List.print print_field "; " ppf (collect_fields t);
          Format.pp_print_string ppf " >"
      | Tobject (_, {contents=Some (path, tys)}) -> (* ~AbelianGrape *)
          Format.fprintf ppf "(%a) %a" (List.print print ", ") tys Path.print path
      | Tunivar None -> Format.pp_print_string ppf "_"
      | Tunivar (Some name) -> Format.pp_print_string ppf name
      | Tpackage (_, _) -> failwith "Types.print Tpackage not implemented"
end

module Typedtree = struct
  include Typedtree
  let print_expr ppf tt =
    Format.pp_print_string ppf begin
      match tt.exp_desc with
        | Texp_ident _ -> "Ident"
        | Texp_constant _ -> "Constant"
        | Texp_let _ -> "Let"
        | Texp_function _ -> "Function"
        | Texp_apply _ -> "Apply"
        | Texp_match _ -> "Match"
        | Texp_try _ -> "Try"
        | Texp_tuple _ -> "Tuple"
        | Texp_construct _ -> "Construct"
        | Texp_variant _ -> "Variant"
        | Texp_record _ -> "Record"
        | Texp_field _ -> "Field"
        | Texp_setfield _ -> "Setfield"
        | Texp_array _ -> "Array"
        | Texp_ifthenelse _ -> "Conditional"
        | Texp_sequence _ -> "Sequence"
        | Texp_while _ -> "While"
        | Texp_for _ -> "For"
        | Texp_assert _ -> "Assert"
        | _ -> "<unknown>"
    end
  let rec print_pat ppf tp =
    match tp.pat_desc with
      | Tpat_any -> Format.pp_print_string ppf "Any"
      | Tpat_var _ -> Format.pp_print_string ppf "Var"
      | Tpat_alias (p,v,_) -> Format.fprintf ppf "%a as %a" print_pat p Ident.print v
      | Tpat_constant _ -> Format.pp_print_string ppf "Constant"
      | Tpat_tuple _ -> Format.pp_print_string ppf "Tuple"
      | Tpat_construct _ -> Format.pp_print_string ppf "Construct"
      | Tpat_variant _ -> Format.pp_print_string ppf "Variant"
      | Tpat_record _ -> Format.pp_print_string ppf "Record"
      | Tpat_lazy _ -> Format.pp_print_string ppf "Lazy"
      | Tpat_array _ -> Format.pp_print_string ppf "Array"
      | Tpat_or _ -> Format.pp_print_string ppf "or"
  let print_rough_strit ppf strit =
    Format.pp_print_string ppf begin match strit with
      | Tstr_attribute _ -> "Tstr_attribute"
      | Tstr_eval _ -> "Tstr_eval"
      | Tstr_value _ -> "Tstr_value"
      | Tstr_primitive _ -> "Tstr_primitive"
      | Tstr_type _ -> "Tstr_type"
      | Tstr_typext _ -> "Tstr_typext"
      | Tstr_exception _ -> "Tstr_exception"
      | Tstr_module _ -> "Tstr_module"
      | Tstr_recmodule _ -> "Tstr_recmodule"
      | Tstr_modtype _ -> "Tstr_modtype"
      | Tstr_open _ -> "Tstr_open"
      | Tstr_class _ -> "Tstr_class"
      | Tstr_class_type _ -> "Tstr_class_type"
      | Tstr_include _ -> "Tstr_include"
    end
end

module ExtLocationSet = struct 
  include Set.Make(ExtLocation)
  let filterSourceLocations : t -> LocationSet.t = fun t -> 
    fold (fun e t -> 
            match e with
              | ExtLocation.Source l -> LocationSet.add l t
              | _ -> t 
         ) 
      t 
      LocationSet.empty    
end 
module ExtLocationSetSet = Set.Make(ExtLocationSet)
module ExtLocationMap = Map.Make(ExtLocation)

