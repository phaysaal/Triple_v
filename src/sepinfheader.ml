(* SepInf header (Tatsuta 2015.6.29--) *)

(*

myMakefile
sepinfheader.ml
sepinfparse.ml
sepinftosns.ml
sepinfparsemain.ml

*)

(*

text syntax

names given
t ::= names | nil | inf
Pi ::= t = t & t =/ t ... 
Sigma ::= Emp * ... * t -> (t,t,t) * ... * P(t,t,t) * ...
formula phi::= Ex z1 z1. Pi & Sigma
entailment ::= phi |- phi

definition clause R := phi

definition clause R(x,y1,y2) := 
	Ex z1 z2. Pi & x -> u1,u2,u3 * P(t1,y1,y2) * P(t2,y1,y2)
where
u1,u2,u3 in x,y1,y2,z1,z2,nil
t1,t2 different, in (u1,u2,u3) cap (z1,z2)
Pi consists of x=y1, y1=nil, y1=y2 (different), y1 =/ nil, y1 =/ x,
	y1 =/ z, y1 =/ y2 (different)

predicate-definition ::= P(x1,x2,x3) := R | R | R

inductive-definition ::= (predicate-definition \n\n)* 

program ::= (entailment \n\n)* "---\n\n"  inductive-definition

*)

(*

functions for the text syntax in sepinfparse.ml

read_formula i
	assume:
	let inputstr = ref "..."
	input: the index i on inputstr
	output:	(formula, i)

str_formula formula
	input: the type formula
	output: the type string

*)

(*

s-expression syntax

Pi ::= (= t t) | (=/ t t) | (& Pi Pi ...)
Sigma ::= Emp | (-> t (t t t)) | (P t t t) | ( * Sigma Sigma ...)
formula phi::= (Ex (z1 z1) (& Pi  Sigma))
entailment ::= (|- phi phi)

definition clause R := phi

predicate-definition ::= (:= (P x1 x2 x3) (| R R ...))

inductive-definition ::= (predicate-definition predicate-definition ...)

program ::= (entailment inductive-definition)
*)

open Printf ;;
open List ;; (* useless for List.map List.iter *)
open String ;;

(* Types *)
(*
type term = Var of string | Nil | Inf ;;
type eqformula = Eq of term * term | Neq of term * term ;;

type defclause = Defclause of string list * eqformula list * term list * (string * term list) list ;;
	(* x,y are given. z, Pi, u, (P,t list) list *)
type inddef = Inddef of (string * string * string list * defclause list) list ;;
	(* (P, x, y, R list) list *)
type formula = Formula of (string list) * eqformula list * bool * (string * term list) list * (string * term list) list ;;
	(* z, Pi, emp, (w, u) list, (P, t list) list *)
type entailment = Entailment of string list * formula * formula ;;
	(* x, phiL, phiR *)
type program = Program of int * (entailment list) * inddef ;;
*)


type term = Var of string 
 | Nil 
 | Inf

type eqformula = Eq of term * term 
 | Neq of term * term

(* z, Pi, emp, (w, u) list, (P, t list) list *)
(*
  <exists> [x,y,z] [x=y,x=/z] false [(x,[w,z]), (y,[u,v])] [(tree, [x,y]), (ls, [y,u])] 
*)
type formula = Formula of string list * eqformula list * bool * (string * term list) list * (string * term list) list 


type entailment = Entailment of string list * formula * formula

(* x,y are given. z, Pi, u, (P,t list) list *)
type defclause = Defclause of string list * eqformula list * term list * (string * term list) list

(* (P, x, y, R list) list *)
type inddef = Inddef of (string * string * string list * defclause list) list 

type program = Program of int * entailment list * inddef 
   
type p = Skip 
 | Assign of string * term * p * int
 | Cons of string * term list * p * int
 | Lookup of string * string * int * p * int
 | Mutate of string * int * term * p * int
 | Dispose of string * p * int
 | If of eqformula * p * p * p * int

type connections = string list
type cgraph = (string * connections) list

type system = p * inddef



let inv (eqf: eqformula) : eqformula = match eqf with
  | Eq (a, b) -> Neq (a, b)
  | Neq (a, b) -> Eq (a, b)
  
let i_to_v (x:int) : string = "_fv" ^ (string_of_int x)


exception SParse of string ;;
exception Abort of string ;;
exception Leak of string;;
exception PLeak of eqformula list;;

(* My functions *)

let p2 x y = printf "%s: %s\n" y x ;;

let myiter x y = List.iter y x ;;

let mymap x y = List.map y x ;;

let streq x y = ((String.compare x y) = 0) ;;

let strfind x y = List.find (fun x0 -> streq x x0) y ;;  (* Can be List.find (streq x) y  *)

let sortuniq f x = let rec g x = match x with [] -> []
	| h::[] -> h::[]
	| h0::h1::t -> if (f h0 h1) = 0 then (g (h1::t)) else h0::(g (h1::t))
	in g (List.sort f x) ;;

let listN n1 n2 = (let rec f x = if (x > n2) then [] else x :: (f(x+1)) in f n1) ;;

let rec strlistdiff x y = match x with [] -> []
	| h::t -> if List.mem h y then strlistdiff t y 
		else h::(strlistdiff t y) ;;

let ftable = ref [] ;;

let warning = ref [""]  ;;

let warn s f = warning := (!warning) @ [s ^ "\n"]; f
 
let col l n = if l = 1 then n else let (l,m) = List.nth (!ftable) (l-2) in (n-m)
 
let rec abort_loc n = 
  try 
    let (l,_) = List.find (fun (i,x) -> x > n) !ftable in
    "Line " ^ (string_of_int l) ^ ", column " ^ (string_of_int (col l n)) 
  with
    Not_found -> ""
