open Sepinfheader



(* c[x := b] *)
let substitute_term  (x:string) (b:term) (c:term): term = match c with
    Nil -> Nil
  | Inf -> Inf
  | Var s -> 
    if s = x 
    then b
    else c 

let substitute_eqformula (v:string) (e: term) (eq: eqformula) : eqformula = match eq with
  | Neq (t_a, t_b) -> Neq (substitute_term v e t_a, substitute_term v e t_b)
  | Eq (t_a, t_b) -> Eq (substitute_term v e t_a, substitute_term v e t_b)

let substitute_ptr (v:string) (e: term) ((x, ts):string * term list) : string * term list = 
  let ts' = List.map (substitute_term v e) ts
  in let x' = if x = v then match e with Var e' -> e' | _ -> x else x  
     in (x', ts')

let substitute_pred (v:string) (e: term) ((x, ts):string * term list) : string * term list = 
  let ts' = List.map (substitute_term v e) ts
  in (x, ts')
 
let is_in_term x t = match t with
    Eq (Var a, Var b) -> x = a || x = b
  | Neq (Var a, Var b) -> x = a || x = b
  | _ -> false
 
let is_memory_leak eq_list ptr_list exp = match exp with
    Var x -> 
      if List.exists (fun (ptr, _) -> ptr = x) ptr_list
      then if List.exists (is_in_term x) eq_list
	then false (* raise (PLeak eq_list) *)
	else true
      else false
  | _ -> false



let substitute (v:string) (exp: term) (a:formula) (loc:int) : formula = match a with
    Formula (var_list, eq_list, b, ptr_list, pred_list) ->
      let eq_list' = List.map (substitute_eqformula v exp) eq_list in
      let ptr_list' = List.map (substitute_ptr v exp) ptr_list in
      let pred_list' = List.map (substitute_pred v exp) pred_list in 
      if not (is_memory_leak eq_list' ptr_list' exp) then
	Formula (var_list, eq_list', b, ptr_list', pred_list')
      else
	warn ("# Warning: Memory Leak by reassigning " ^ v ^ " @ " ^ (abort_loc loc)) (Formula (var_list, eq_list', b, ptr_list', pred_list'))
(*	warning := (!warning) @ [("# Warning: Memory Leak by reassigning " ^ v ^ " @ " ^ (abort_loc loc))]; (Formula (var_list, eq_list', b, ptr_list', pred_list')) 
raise (Leak ("Memory leak at " ^ (abort_loc loc) ^ " By reassigning " ^ v )) *)
	  
	

