(**
   v1. Faisal, 2015.7.5

   This module is responsible for converting string from various data of triple verifier for printing
*)

open Sepinfheader

let rec string_of_list f d xs = match xs with 
    [] -> ""
  | head :: [] -> (f head)  
  | head :: tail -> (f head) ^ d ^ (string_of_list f d tail)

let string_of_var x = x

let string_of_term x = match x with
    Var n -> n
  | Nil -> "nil"
  | Inf -> "inf"
let string_of_eqformula x = match x with
    Eq (t1, t2) -> (string_of_term t1) ^ " = " ^ (string_of_term t2)
  | Neq (t1, t2) -> (string_of_term t1) ^ " =/ " ^ (string_of_term t2)


let string_of_ptr x = match x with
    (name, list) -> name ^ " -> (" ^ (string_of_list string_of_term "," list) ^ ")"

let string_of_pred x = match x with
    (name, list) -> name ^ "(" ^ (string_of_list string_of_term "," list) ^ ")"

let string_of_formula x = match x with
    Formula (z, pi, emp, r, d) -> 
      let exists_str = if z = [] then "" else "Ex " ^ (string_of_list string_of_var " " z) ^ "." in
      let pi_str = if pi = [] then "" else (string_of_list string_of_eqformula " & " pi) in
      let pi_str = pi_str ^ (if pi=[] then "" else " & ") in
      if emp = true then 
	exists_str ^ pi_str ^ "Emp "
      else 
	let j_str = if r = [] || d = [] then "" else " * " in
	exists_str ^ pi_str ^ (string_of_list string_of_ptr " * " r ) ^ j_str ^ (string_of_list string_of_pred " * " d)
	  
let string_of_entailment x = match x with 
    Entailment (sl, f_a, f_b) -> 
      if sl = [] 
      then (string_of_formula f_a) ^ " |- " ^ (string_of_formula f_b) ^ "\n\n"
      else "Ex " ^ (string_of_list string_of_var " " sl) ^ "." ^ (string_of_formula f_a) ^ " |- " ^ (string_of_formula f_b) ^ "\n\n"

let string_of_defclause x = match x with
    Defclause (z, pi, u, v) -> "[" ^ (string_of_list string_of_var " " z) ^ "-" ^ (string_of_list string_of_eqformula " & " pi) ^ "-" ^ (string_of_list string_of_term "," u) ^ "-" ^ (string_of_list string_of_ptr "*" v)

let string_of_inddef x = match x with
    (a, b, cl, dl) -> a ^ " " ^ b ^ " " ^ (string_of_list string_of_var " " cl) ^ "-" ^ (string_of_list string_of_defclause " " dl)

let string_of_inddefs xs = match xs with 
    Inddef ys -> string_of_list string_of_inddef "\n" ys

