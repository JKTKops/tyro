let parsetree_of_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  Location.init lexbuf filename;
  Parse.implementation lexbuf

let parsetree_of_string ?(filename="<unknown>") code =
  let lexbuf = Lexing.from_string code in
  Location.init lexbuf filename;
  Parse.implementation lexbuf;;

let parsetree_of_chan ?(filename="<unknown>") chan =
  let lexbuf = Lexing.from_channel ~with_positions:true chan in
  Location.init lexbuf filename;
  Parse.implementation lexbuf;;

let import_for_ezy ptree =
  Ezy.EzyEnrichedAst.import_structure (Ezy.EzyFeatures.all_program_feats true) ptree
