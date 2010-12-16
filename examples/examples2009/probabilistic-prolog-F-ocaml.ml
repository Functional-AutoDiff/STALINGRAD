type term = Constant of int
  | Variable of ad_number
  | Compound of int*(term list)

let make_p = 0

let make_q = 1

let make_x = (Base 2.0)

let same (Variable variable1) (Variable variable2) =
  variable1<=variable2 && variable2<=variable1

let rec binds p1 variable2 =
  match p1 with
    [] -> false
  | ((variable1, _)::substitution) ->
      if same variable1 variable2 then true else binds substitution variable2

let rec lookup_value variable1 ((variable2, value)::substitution) =
  if same variable1 variable2
  then value
  else lookup_value variable1 substitution

let rec apply_substitution substitution p2 =
  match p2 with
    ((Constant _) as term) -> term
  | ((Variable _) as term) ->
      if binds substitution term then lookup_value term substitution else term
  | (Compound (f, terms)) ->
      Compound (f, (map (fun term -> apply_substitution substitution term)
		      terms))

let rec apply_substitution_to_clause substitution (p, term, terms) =
  (p,
   (apply_substitution substitution term),
   (map (fun term -> apply_substitution substitution term) terms))

let rec member variable1 p =
  match p with
    [] -> false
  | (variable2::set) ->
      if same variable1 variable2 then true else member variable1 set

let rec union p1 set2 =
  match p1 with
    [] -> set2
  | (element::set1) ->
      if member element set2
      then union set1 set2
      else element::(union set1 set2)

let rec variables_in p =
  match p with
    (Constant _) -> []
  | ((Variable _) as term) -> [term]
  | (Compound (f, terms)) -> fold_left union [] (map variables_in terms)

let rec variables_in_clause (p, term, terms) =
  union (variables_in term) (fold_left union [] (map variables_in terms))

let occurs variable term = member variable (variables_in term)

let rec unify p1 p2 =
  match p1, p2 with
    (Constant constant1), (Constant constant2) ->
      if constant1=constant2 then Some [] else None
  | ((Constant _) as term1), ((Variable _) as term2) -> Some [(term2, term1)]
  | (Constant _), (Compound _) -> None
  | ((Variable _) as term1), ((Constant _) as term2) -> Some [(term1, term2)]
  | ((Variable _) as term1), ((Variable _) as term2) -> Some [(term1, term2)]
  | ((Variable _) as term1), ((Compound _) as term2) ->
      if occurs term1 term2 then None else Some [(term1, term2)]
  | (Compound _), (Constant _) -> None
  | ((Compound _) as term1), ((Variable _) as term2) ->
      if occurs term2 term1 then None else Some [(term2, term1)]
  | (Compound (function1, terms1)), (Compound (function2, terms2)) ->
      (if function1=function2
      then let rec loop p1 p2 substitution =
	(match p1, p2 with
	  [], [] -> Some substitution
	| (term1::terms1), (term2::terms2) ->
	    (match unify (apply_substitution substitution term1) (apply_substitution substitution term2) with
	      None -> None
	    | Some substitution1 ->
		loop terms1 terms2 (substitution1@substitution))
	| _, _ -> None)
      in loop terms1 terms2 []
      else None)

let map_indexed f l =
  let rec loop p i =
    match p with
      [] -> []
    | (h::t) -> (f h i)::(loop t (i+.(Base 1.0)))
  in loop l (Base 0.0)

let alpha_rename clause offset =
  apply_substitution_to_clause
    (map_indexed
       (fun variable -> (fun i -> (variable, (Variable (offset+.i)))))
       (variables_in_clause clause))
    clause

let rec proof_distribution term clauses =
  let offset =
    fold_left (fun x y -> if x<=y then y else x)
      (Base 0.0)
      (map (fun (Variable variable) -> variable)
	 (fold_left union
	    []
	    (map variables_in_clause clauses)))
  in fold_left ( @ )
    []
    (map (fun clause ->
      let (p, term1, terms) = alpha_rename clause offset
      in let rec loop p substitution terms =
	match substitution with
	  None -> []
	| Some substitution ->
	    match terms with
	      [] -> [(p, substitution)]
	    | term::terms ->
		fold_left ( @ )
		  []
		  (map (fun (p1, substitution1) ->
		    loop (p*.p1)
		      (Some (substitution@substitution1))
		      terms)
		     (proof_distribution
			(apply_substitution substitution term)
			clauses))
      in loop p (unify term term1) terms)
       clauses)

let likelihood substitution_distribution =
  fold_left ( +. ) (Base 0.0) (map (fun (p, _) -> p) substitution_distribution)

let example _ =
  (gradient_ascent_F
     (fun [p0; p1] ->
       let clauses = [(p0, (Compound (make_p, [(Constant 0)])), []);
		      (((Base 1.0)-.p0),
		       (Compound (make_p, [(Variable make_x)])),
		       [(Compound (make_q, [(Variable make_x)]))]);
		      (p1, (Compound (make_q, [(Constant 1)])), []);
		      (((Base 1.0)-.p1),
		       (Compound (make_q, [(Constant 2)])),
		       [])]
       in fold_left ( *. )
	 (Base 1.0)
	 (map (fun observation ->
	   likelihood
	     (proof_distribution
		(Compound (make_p,
			   [(Constant observation)]))
		clauses))
	    [0; 1; 2; 2]))
     [(Base 0.5); (Base 0.5)]
     (Base 1000.0)
     (Base 0.1))

let _ =
  (let rec loop i result =
    if i<=(Base 0.0) && (Base 0.0)<= i
    then result
    else let ([p0; p1], _, _) = example ()
    in loop (i-.(Base 1.0)) [(write_real p0); (write_real p1)]
  in loop (Base 1000.0) [(Base 0.0); (Base 0.0)]; 0)
