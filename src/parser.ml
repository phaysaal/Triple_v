(* 

   v1. Faisal, 2015.7.4
   v2. Faisal, 2015.7.13 [+Sepinf*, m parse_triple, ]

#load "str.cma";;
ocamlc other options str.cma other files
ocamlopt other options str.cmxa other files

*)

open Sepinfheader
(* open Sepinfparse *)
open String
open Str


(* Extract the initial matching substring and the rest of the string *)
(* let p_str = ref "" ;;
let p_str_len = ref 0 ;; *)

exception Parse of string ;;

(* white = space, tab, linefeed *)
(* input inputstr *)

(* global variables *)

let inputstr = ref "" ;;
let inputstrlen = ref 0 ;;


(* not optimized *)
let parse_error i =
  ("# Parsing Error @ " ^ (abort_loc i))

let parse_sc i =
  ("# Parsing Error @ " ^ (abort_loc i) ^ " : missing semi-colon at the end of statement")

let extract i rexp = 
  let r = Str.regexp rexp
  in if Str.string_match r !inputstr i
    then let m = Str.matched_string !inputstr
	 in (m, i + String.length m)
    else ("", i)
       
(* Skip white spaces *)
let skip_ws i = 
  let (_, i) = extract i "[ \t\n]*"
  in i
  
let parse_names i = 
  let (a, i) = extract i "[a-zA-Z0-9_'][a-zA-Z0-9_']*"
  in (a, skip_ws i)
  
let parse_op i op =
  let (a, i) = extract i op
  in (a, skip_ws i)
  
let parse_num i = 
  let (a, i) = extract i "[0-9]+"
  in if a = ""
    then warn ((parse_error i) ^ " : wrong number format/expected index") (0, skip_ws i)
    else (int_of_string a, skip_ws i) 
      
(* ------------------------------------------ *)
      
let parse_term i = 
  let (nm, i) = parse_names i
  in match nm with
    "nil" -> (Nil, i)
  | "inf" -> (Inf, i)
(*  | "" -> warn (parse_error i) (Nil, i) *)
  | ys -> (Var ys, i)
    
let parse_eqformula i = 
  let (op_a, i) = parse_term i in
  (* if op_a = Var "" then warn ((parse_error i) ^ " : identifier should be in [a-zA-Z_'][a-zA-Z0-9_']*") (true, Neq (Nil, Nil), i) else *)
    let (op, i) = parse_op i "=/?" in 
    let (op_b, i) = parse_term i in
    if op_a <> Var "" && op <> "" && op_b <> (Var "") then
      if op = "=" then 
	(true, Eq (op_a, op_b), i)
      else 
	(true, Neq (op_a, op_b), i)
    else 
      (false, Eq (Nil, Nil), i) (** May be pointer or predicate *)

let rec parse_var_list i = 
  let (x, i) = parse_names i
  in if x = "" 
    then ([], i)
    else let (ys, i) = parse_var_list i
	 in (x::ys, i)
	 
      

let rec parse_term_list i = 
  let (x, i') = parse_term i
  in if x = Var ""
    then ([], i)
    else let (_, i) = parse_op i' ","
	 in let (ys, i) = parse_term_list i
	    in (x::ys, i)
	    
let rec parse_eqformula_list i =
  let (b, x, i') = parse_eqformula i in
  if b = false then 
    ([], i) 
  else
    let (_, i) = parse_op i' "&" in
    let (ys, i) = parse_eqformula_list (skip_ws i) in
    (x::ys, i)
    
let parse_ptr i = 
  let (name, i') = parse_names i in
  if name = "" then
    (("", []),i)
  else
    let (ptr, i') = parse_op i' "->" in
    if ptr <> "" then 
      let (_, i) = parse_op i' "(" in
      let (var_list, i) = parse_term_list i in
      let (_, i) = parse_op i ")" in
      if var_list = [] then warn ((parse_error i) ^ " : empty list of " ^ name) ((name, [Nil]), i) else
      ((name, var_list), i)
    else 
      ((name, []), i)
	 
let parse_pred i =
  let (name, i') = parse_names i in
  if name <> "" then 
    let (br, i') = parse_op i' "(" in
    if br <> "" then
      let (var_list, i) = parse_term_list i' in
      let (_, i) = parse_op i ")" in
      if var_list = [] then warn ((parse_error i) ^ " : empty list of " ^ name) ((name, [Nil]), i) else
      ((name, var_list), i)
    else 
      warn ((parse_error i) ^ " : inappropriate symbol after " ^ name)  ((name, [Nil]), i)
  else 
    warn ((parse_error i) ^ " : Identifier is not found") (("", []), i)
	 
let rec parse_ptr_pred_list i =
  let (emp, i1) = parse_op i "[eE]mp" in 
  if emp = "" then 
    let ((name, list), i2) = parse_ptr i in     (** Try to read a pointer entry x->(e1,e2) *)
    if name = "" then
      ([], [], i)
    else 
      if list = [] then                           (** If there is no pointer entry *)
	let ((name, list), i3) = parse_pred i in  (** Try to read a predicate entry *) 
	if list = [] || name = "" then                         (** If there is no predicate entry *) 
	  warn ((parse_error i3) ^ " : no identifier found") ([], [], i)
(*	  raise (Parse ("Parsing error at " ^ (abort_loc i)))                             (** No pointer of predicate entry *) *)
	else                                      (** Successful predicate parsing *) 
	  let (s, i4) = parse_op i3 "*" in        (** Read separator *)
	  if s <> "" then                         (** There are more pointer/predicate entry *)
	    let (ptr_list, pred_list, i5) = parse_ptr_pred_list i4 in  (** Read other pointer/predicate entry *)
	    if ptr_list = [] && pred_list = [] then warn ((parse_error i5) ^ " : extra *") ([], [(name, list)], i5) else
	    (ptr_list, (name, list) :: pred_list, i5)  (** Merge the current predicate with rest of the list *)
	  else                                    (** There are no pointer/predicate list *)
	    ([], (name, list)::[], i3)            (** Return the predicate last parsed *)
      else                                        (** Successful pointer parsing *)
	let (s, i3) = parse_op i2 "*" in          (** Read separator *)
	if s <> "" then 
	  let (ptr_list, pred_list, i4) = parse_ptr_pred_list i3 in
	  if ptr_list = [] && pred_list = [] then warn ((parse_error i4) ^ " : extra *") ([(name, list)], [], i4) else
	  ((name, list) :: ptr_list, pred_list, i4)
	else 
	  ((name, list)::[], [], i2)
  else 
    ([],[],i1)
      
	    
let parse_formula' i var_list = 
  let (eqformula_list, i) = parse_eqformula_list i in (* read Pi *)
  let (ptr_list, pred_list, i) = parse_ptr_pred_list i in
  match (ptr_list, pred_list) with
    ([], []) -> (Formula (var_list, eqformula_list, true, [], []), i)
  | _ -> (Formula (var_list, eqformula_list, false, ptr_list, pred_list), i)
    
let parse_formula i =
  let (ex, i') = parse_op i "Ex" 
  in if ex <> "" then 
      (* let (_, i) = parse_op i' "(" in *)
      let (var_list, i) = parse_var_list i' in (* read z *)
      (* let (_, i) = parse_op i ")" in *)
      let (dot, i) = parse_op i "." in
      if dot <> "." then 
	warn ((parse_error i) ^ " : dot expected after `Ex'") (parse_formula' (i+1) var_list) 
      else 
	parse_formula' i var_list
    else 
      parse_formula' i []
		      
		
let rec parse_p i =
  let (t_a, ia) = parse_names i
  in if t_a = "if"
    then let (_, ia) = parse_op ia "(" in 
	 let (_, b, ia) = parse_eqformula ia in 
	 let (_, ia) = parse_op ia ")[ \n\t]*\\(then\\)?[ \n\t]*{" in 
	 let (p_a, ia) = parse_p ia in 
	 let (_, ia) = parse_op ia "}[ \n\t]*\\(else\\)?[ \n\t]*{" in 
	 let (p_b, ia) = parse_p ia in 
	 let (_, ia) = parse_op ia "}" in 
	 let (p, ia) = parse_p ia in 
	 (If (b, p_a, p_b, p, i), ia)
    else   
      if t_a = "dispose" 
      then let (_, ia) = parse_op ia "(" in
	   let (e, ia) = parse_names ia in 
	   let (_, ia) = parse_op ia ")" in 
	   let (sc, ia) = parse_op ia ";" in
	   let (p, ia) = parse_p ia in 
	   if sc = "" then warn (parse_sc i) (Skip, ia) else 
	     (Dispose (e, p, i), ia)
      else 
	if t_a <> ""
	then let (op, ia) = parse_op ia ":=\\|\\." in 
	     if op = ":="
	     then let (t_b, ia) = parse_names ia in (* assignment or cons or lookup *)
		  if t_b = "cons"
		  then let (_, ia) = parse_op ia "(" in (* cons *)
		       let (tl, ia) = parse_term_list ia in
		       let (_, ia) = parse_op ia ")" in 
		       let (sc, ia) = parse_op ia ";" in
		       if sc = "" then warn (parse_sc i) (Skip, ia) else
			 let (p, ia) = parse_p ia in 
			 (Cons (t_a, tl, p, i), ia)
		  else let e = if t_b = "nil" then Nil else (Var t_b) in 
		       let (op, ib) = parse_op ia "." in 
		       if op = "."
		       then let (index, ia) = parse_num ib in  (* lookup *)
			    let (sc, ia) = parse_op ia ";" in 
			    if sc = "" then warn (parse_sc i) (Skip, ia) else
			      let (p, ia) = parse_p ia  in 
			      (Lookup (t_a, t_b, index, p, i), ia)
		       else let (sc, ia) = parse_op ia ";" in (* assignment *)
			    if sc = "" then warn (parse_sc i) (Skip, ia) else
			      let (p, ia) = parse_p ia in 
			      (Assign (t_a, e, p, i), ia)
	     else 
		 if op = "."
		 then let (index, ia) = parse_num ia in (* mutation *)
		      let (op, ia) = parse_op ia ":=" in
		      let (v, ia) = parse_term ia in 
		      let (sc, ia) = parse_op ia ";" in
		      if sc = "" then warn (parse_sc i) (Skip, ia) else
			let (p, ia) = parse_p ia in
		      (* in let ptr = if t_a = "nil" then Nil else (Var t_a) *)
			(Mutate (t_a, index, v, p, i), ia)
		 else warn ((parse_error i) ^ " : inappropriate symbol " ^ op) (Skip, i)
	else (Skip, i)
	  
let init xs = 
  inputstr := xs ;
  inputstrlen := String.length !inputstr; 
  0;;

(** Note: if parse_formula is kept finally, no need skip_a_string  *)
let parse_triple i =
  let (_,i) = parse_op i "{" in
  let (f1,i) = parse_formula i in
  let (_,i) = parse_op i "}" in
  let (p, i) = parse_p i in
  let (_,i) = parse_op i "{" in  
  let (f2,i) = parse_formula i in (* skip '{' *)
  let (br,i) = parse_op i "}" in
  if br = "" || p = Skip then warn (parse_error i) ((f1, p, f2), i) else  
  ((f1, p, f2), i) (* skip last '}' *) 
		
let rec parse_program i = 
  let i = skip_ws i in
  let (triple, i) = parse_triple i in 
  let rest = Bytes.sub (!inputstr) i (!inputstrlen - i) in
  (triple, rest)
					   
let parse_system x =
  let _ = init x in 
  parse_program 0

(*
let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic 
     in let s = Bytes.create n 
	in really_input ic s 0 n;
	close_in ic;
	(s)
*)

let inputstr_stdin () =
let x = ref "" in
try
while true do
x := !x ^ (input_line stdin) ^ "\n"
done ;
"" (* dummy *)
with End_of_file -> !x ;;


let rec cum l i n = match l with
    [] -> []
  | h::t -> (i, n+h) :: cum t (i+1) (n+h)
 
let make_ftable code = cum (List.map (fun x -> String.length x) (Str.split (Str.regexp "\n") code)) 1 0
