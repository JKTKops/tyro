val parsetree_of_file : string -> Parsetree.structure;;

val parsetree_of_string : ?filename:string -> string -> Parsetree.structure;;

val parsetree_of_chan : ?filename:string -> in_channel -> Parsetree.structure;;

val import_for_ezy : Parsetree.structure -> Ezy.EzyAst.imported_structure;;

(* We probably want a function here that does some combined work, producing 
   Some ast if there is a type error and None otherwise. Then we exit fast
   if there's no type error in the program. *)
