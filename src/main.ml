(*  
  v1. Faisal, 2015.7.5
  v2. Faisal, 2015.7.13 [+Sepinf*, m main, -verify]

  This module is resposible for conducting the whole triple verification. It corresponds between all other modules.
*)

open Parser
open Verify
open Sepinfheader
open Output

(** Initialization of source code line length listing *)
let setftable table = 
  ftable := table;
  0

(** Main entry point *)
let main ()=
  let code = inputstr_stdin () in
  let table = make_ftable code in
  let _ = setftable table in  
  let (triple, inddef) = Parser.parse_system code in
  let entlist = verify_triple triple in
  let s_entlist = List.map (fun (n,f1,f2) -> string_of_entailment (Entailment (fv_list f1, f1, f2)))  entlist in
  output_string stdout (List.fold_left (^) "" (!warning)) ; 
  output_string stdout (List.fold_left (^) "" s_entlist); 
  output_string stdout inddef;
  exit 0;;

main ();; 

