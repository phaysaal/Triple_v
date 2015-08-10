open Sepinfheader
open Substitute

let fresh_variable (x:int) : int = x + 1

let rec (===) (eqlist: eqformula list) (x: term) (y: term)  = 
    if (List.exists (fun z -> match z with Eq (x', y') -> (x'=x && y'=y) || (x'=y && y'=x) | _ -> false) eqlist) || x = y (** Direct structural match*)
    then true
    else let (eqs,rest) = List.partition (fun z -> match z with Eq (x',y') -> x'=y || y'=y | _ -> false) eqlist in (** Partition all z=y or y=z vs rest *)
	 let es =  List.map (fun z -> match z with Eq (x', y') -> if x'=y then y' else x' | _ -> Nil) eqs in       (** Collect the zs *)
	 List.exists (rest === x) es       (** a=b, b=c implies a=c *)


let add_to_formula (a: formula) (c: eqformula) : formula = match a with 
    Formula (var_list, eq_list, b, ptr_list, pred_list) -> Formula (var_list, c::eq_list, b, ptr_list, pred_list)


let add_to_spatial (a: formula) (c: string * term list) : formula = match a with 
    Formula (var_list, eq_list, b, ptr_list, pred_list) -> Formula (var_list, eq_list, false, c::ptr_list, pred_list)


let assign (ass:formula) (x:string) (e:term) (fv:int) (loc:int): formula * int = 
  let x' = fresh_variable fv    
  in let e' = substitute_term x (Var (i_to_v x')) e
     in let ass' = substitute x (Var (i_to_v x')) ass loc
	in let ass1 = add_to_formula ass' (Eq ((Var x), e'))
	   in (ass1, x')

	 
let get_from_spatial (Formula (_, eq_list, _, ptr_list, _):formula) (pt:string) (i:int) (loc:int) : term =
  try  
    let v_ptr = List.find (fun (p,_) -> (eq_list === (Var p)) (Var pt)) ptr_list in
    let (pts, ts) = v_ptr in 
    if List.length ts > i then
      List.nth ts i
    else
      warn ("# Abort: Index " ^ (string_of_int i) ^ " is out of bound @ " ^ (abort_loc loc)) Nil
  with 
    _ -> warn ("# Abort: " ^ pt ^ " does not points to allocated memory @ " ^ (abort_loc loc)) Nil

let set_to_spatial  (Formula (a, eq_list, c, ptr_list, d):formula) (pt:string) (i:int) (v:term) (loc:int): formula =  
  let (matched, unmatched) = List.partition (fun (p,_) -> (eq_list === (Var p)) (Var pt)) ptr_list in
  match matched with
    [] -> warn ("# Abort: " ^ pt ^ " does not points to allocated memory @ " ^ (abort_loc loc)) (Formula (a, eq_list, c, ptr_list, d))
  | (p,ps)::_ -> 
      if List.length ps <= i then
	warn ("# Warning: Index " ^ (string_of_int i) ^ " is out of bound @ " ^ (abort_loc loc)) (Formula (a, eq_list, c, ptr_list, d))
      else 
	let (_,ps') = List.fold_left (fun (j,l) r -> if j = i then (j+1, l@[v]) else (j+1, l@[r]) ) (0,[]) ps in
	Formula (a, eq_list, c, (p,ps')::unmatched, d)
	  
let delete_from_spatial (Formula (a, eq_list, c, ptr_list, d):formula) (pt:string) (loc:int) : formula =
  let ptr_list' = List.filter (fun (p,ps) -> not ((eq_list === (Var pt)) (Var p))) ptr_list in
  if List.length ptr_list = List.length ptr_list' then 
    warn ("# Abort: " ^ pt ^ " does not points to allocated memory @ " ^ (abort_loc loc)) (Formula (a, eq_list, c, ptr_list, d))
  else
    let c = if ptr_list' = [] && d = [] then true else false in
    (Formula (a, eq_list, c, ptr_list', d))
 
let rec compose (p1:p) (v_p:p) : p = match p1 with
    Skip -> v_p
  | Assign (var, exp, pr, l) -> Assign (var, exp, compose pr v_p, l)
  | Cons (v, ts, pr, l) -> Cons (v, ts, compose pr v_p, l)
  | Lookup (v, pt, i, pr, l) -> Lookup (v, pt, i, compose pr v_p, l)
  | Mutate (pt, i, t, pr, l) -> Mutate (pt, i, t, compose pr v_p, l)
  | Dispose (pt, pr, l) -> Dispose (pt, compose pr v_p, l)
  | If (e, p1, p2, pr, l) -> If (e, p1, p2, compose pr v_p, l)

let false_entailment = (0, Formula ([],[],true,[],[]), Formula ([],[],false,[],[]))

let rec validate ((pre, program, post):formula * p * formula) (fv:int): (int * formula * formula) list  = match program with
    Skip -> [(fv,pre,post)]
  | Assign (var, exp, pr, l) -> let (pre', fv') = assign pre var exp fv l in
				validate (pre', pr, post) fv'
  | Cons (v, ts, pr, l) -> let fv' = fresh_variable fv in
			   let pre' = substitute v (Var (i_to_v fv')) pre l in 
			   let pre'' = add_to_spatial pre' (v, ts) in
			   validate (pre'', pr, post) fv'
  | Lookup (v, pt, i, pr, l) ->  let v_t = get_from_spatial pre pt i l in
				 let (pre', fv') = assign pre v v_t fv l in
				 validate (pre', pr, post) fv'
  | Mutate (pt, i, t, pr, l) -> let pre' = set_to_spatial pre pt i t l in
				validate (pre', pr, post) fv
  | Dispose (pt, pr, l) -> let pre' = delete_from_spatial pre pt l in
			   validate (pre', pr, post) fv
  | If (e, p1, p2, pr, l) -> let pre1 = add_to_formula pre e in
			     let pre2 = add_to_formula pre (inv e) in 
			     List.append (validate (pre1, compose p1 pr, post) fv)  (validate (pre2, compose p2 pr, post) fv)
let verify_triple (triple:formula * p * formula) :  (int * formula * formula) list = validate triple 0

let fv s = 
  if (String.get s 0) = '_'
  then [s]
  else []


let fv_of_list tl = List.concat (List.map (fun t -> match t with Var s -> fv s | _ -> []) tl)

let fv_of_ptrlist (l:(string* term list) list) = List.concat (List.map (fun (s,tl) -> (fv s) @ (fv_of_list tl)) l)
 
let fv_of_predlist l = List.concat (List.map (fun (s,tl) -> (fv_of_list tl)) l)

let fv_of_eqformulas (l: eqformula list) : string list = 
  List.concat (List.map (fun h -> match h with Eq (Var x, Var y) -> (fv x) @ (fv y) | Neq (Var x,Var y) -> (fv x) @ (fv y) | _ -> []) l)

let rec remove_duplicacy ls = match ls with
    [] -> []
  | h::t -> let t' = remove_duplicacy t in
	    if List.mem h t'
	    then t'
	    else h::t'

let fv_list (Formula (_, eqformula_list, _, ptr_list, pred_list) :formula) : string list = 
  remove_duplicacy ((fv_of_eqformulas eqformula_list) @ (fv_of_ptrlist ptr_list) @ (fv_of_predlist pred_list))

