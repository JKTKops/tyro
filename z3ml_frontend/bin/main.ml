
let input_file = ref stdin
let input_filename = ref "stdin"
let output_file = ref ""

let anon_arg fname =
  if !input_file <> stdin
    then failwith "can only process one input file"
    else input_file := open_in fname; input_filename := fname

let speclist =
  [ ("-o", Arg.Set_string output_file, "Set output file name (default stdout)") 
  ]

let usage = "zgen <file> [-o <outfile>]"

let () = Arg.parse speclist anon_arg usage;;

let input = !input_file
and output = match !output_file with
  | "" -> stdout
  | fn -> open_out fn;;

(* TODO: initialize environment *)
let ast = Zgen.Read.parsetree_of_chan ~filename:!input_filename input;;

let () = Compmisc.init_path ()

let () =
  try
    let etree = Zgen.Read.import_for_ezy ast in
    let env = Ezy.EzyEnv.import Env.initial_safe_string in
    let (_, env) =
      try Ezy.EzyEnv.open_module "Stdlib" env with
      | Not_found -> Ezy.EzyEnv.open_module "Stdlib" env
    in
    (* let env = Compmisc.initial_env () in
    let env = Ezy.EzyEnv.import env in *)
    (* ^^^ the Not_found happens at import here... need to try twice? *)
    (* TODO: If there are PostProcess errors, don't output. *)
    let (_, acs, _, _pp) = Ezy.EzyGenerate.for_structure etree env in
    let fmt = Format.formatter_of_out_channel output in
    Zgen.Output.do_output ~fmt acs
  with
  | Ezy.EzyErrors.PreFatal (f, loc) ->
    let loc = match loc with | None -> Location.none | Some loc -> loc in
    Ezy.EzyErrors.print_fatal ()
      ~program:(lazy "<can't retrieve program>")
      loc
      Format.err_formatter
      f
