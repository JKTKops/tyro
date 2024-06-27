(* Read some code into a parsetree, generate for it, and then output the
   resulting constraint set and formatted output.
   Intended primarily for use in utop; bin/main.ml has a variant which
   drives the executable. *)

let go ?filename code =
  let ptree = match filename with
    | Some filename -> Read.parsetree_of_string ~filename code
    | None          -> Read.parsetree_of_string code
  in
  try
    let etree = Read.import_for_ezy ptree in
    let env = Ezy.EzyEnv.import Env.initial_safe_string in
    (* The first time we try to open Stdlib, we'll run into an issue where one of the modules
      that we're trying to load into the persistent_structures table refers to another one.
      This will result in a `Not_found` error while we've left an `empty` env in the table.
      So, simply ensure that that happens once with try, then do it again, which should work. *)
    let (_, env) =
      try
        Ezy.EzyEnv.open_module "Stdlib" env 
      with Not_found ->
        Ezy.EzyEnv.open_module "Stdlib" env
    in
    (* let () = Ezy.EzyEnv.print true Format.std_formatter env in *)
    let (_, acs, _, _) = Ezy.EzyGenerate.for_structure etree env in
    let fmt = Format.std_formatter in
    Format.fprintf fmt "Resulting AtConstrSet:@\n%a@\n" Ezy.EzyConstraints.AtConstrSet.print acs;
    Format.fprintf fmt "Formatted output:@\n";
    Output.do_output ~fmt acs
  with
    | Ezy.EzyErrors.PreFatal (f, loc) ->
      let loc = match loc with | None -> Location.none | Some loc -> loc in
      Ezy.EzyErrors.print_fatal () ~program:(lazy code) loc Format.std_formatter f
