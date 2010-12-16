datatype term = Constant of int
	      | Variable of ad_number
	      | Compound of int*(term list)

val make_p = 0

val make_q = 1

val make_x = (Base 2.0)

fun same (Variable variable1) (Variable variable2) =
    variable1<=variable2 andalso variable2<=variable1

fun binds [] _ = false
  | binds ((variable1, _)::substitution) variable2 =
    if same variable1 variable2 then true else binds substitution variable2

fun lookup_value variable1 ((variable2, value)::substitution) =
    if same variable1 variable2
    then value
    else lookup_value variable1 substitution

fun apply_substitution substitution (term as (Constant _)) = term
  | apply_substitution substitution (term as (Variable _)) =
    if binds substitution term then lookup_value term substitution else term
  | apply_substitution substitution (Compound (function, terms)) =
    Compound (function, (map (fn term => apply_substitution substitution term)
			     terms))

fun apply_substitution_to_clause substitution (p, term, terms) =
    (p,
     (apply_substitution substitution term),
     (map (fn term => apply_substitution substitution term) terms))

fun member variable [] = false
  | member variable1 (variable2::set) =
    if same variable1 variable2 then true else member variable1 set

fun union ([], set) = set
  | union ((element::set1), set2) =
    if member element set2
    then union (set1, set2)
    else element::(union (set1, set2))

fun variables_in (Constant _) = []
  | variables_in (term as (Variable _)) = [term]
  | variables_in (Compound (function, terms)) =
    foldl union [] (map variables_in terms)

fun variables_in_clause (p, term, terms) =
    union ((variables_in term), (foldl union [] (map variables_in terms)))

fun occurs variable term = member variable (variables_in term)

fun unify (Constant constant1) (Constant constant2) =
    if constant1=constant2 then SOME [] else NONE
  | unify (term1 as (Constant _)) (term2 as (Variable _)) =
    SOME [(term2, term1)]
  | unify (Constant _) (Compound _) = NONE
  | unify (term1 as (Variable _)) (term2 as (Constant _)) =
    SOME [(term1, term2)]
  | unify (term1 as (Variable _)) (term2 as (Variable _)) =
    SOME [(term1, term2)]
  | unify (term1 as (Variable _)) (term2 as (Compound _)) =
    if occurs term1 term2 then NONE else SOME [(term1, term2)]
  | unify (Compound _) (Constant _) = NONE
  | unify (term1 as (Compound _)) (term2 as (Variable _)) =
    if occurs term2 term1 then NONE else SOME [(term2, term1)]
  | unify (Compound (function1, terms1)) (Compound (function2, terms2)) =
    if function1=function2
    then let fun loop [] [] substitution = SOME substitution
	       | loop (term1::terms1) (term2::terms2) substitution =
		 (case unify (apply_substitution substitution term1)
			     (apply_substitution substitution term2) of
		      NONE => NONE
		    | SOME substitution1 =>
		      loop terms1 terms2 (substitution1@substitution))
	       | loop _ _ _ = NONE
	 in loop terms1 terms2 [] end
    else NONE

fun map_indexed f l =
    let fun loop [] i = []
	  | loop (h::t) i = (f h i)::(loop t (i+(Base 1.0)))
    in loop l (Base 0.0) end

fun alpha_rename clause offset =
    apply_substitution_to_clause
	(map_indexed
	     (fn variable => (fn i => (variable, (Variable (offset+i)))))
	     (variables_in_clause clause))
	clause

fun proof_distribution term clauses =
    let val offset = foldl (fn (x, y) => if x<=y then y else x)
			   (Base 0.0)
			   (map (fn (Variable variable) => variable)
				(foldl union
				       []
				       (map variables_in_clause clauses)))
    in foldl op @
	     []
	     (map (fn clause =>
		      let val (p, term1, terms) = alpha_rename clause offset
		      in let fun loop p substitution terms =
				 case substitution of
				     NONE => []
				   | SOME substitution =>
				     case terms of
					 [] => [(p, substitution)]
				       | term::terms =>
					 foldl op @
					       []
					       (map (fn (p1, substitution1) =>
							loop (p*p1)
							     (SOME (substitution@
								    substitution1))
							     terms)
						    (proof_distribution
							 (apply_substitution
							      substitution
							      term)
							 clauses))
			 in loop p (unify term term1) terms end end)
		  clauses) end

fun likelihood substitution_distribution =
    foldl op + (Base 0.0) (map (fn (p, _) => p) substitution_distribution)

fun example _ =
    (gradient_ascent_R
	 (fn [p0, p1] =>
	     let val clauses = [(p0, (Compound (make_p, [(Constant 0)])), []),
				(((Base 1.0)-p0),
				 (Compound (make_p, [(Variable make_x)])),
				 [(Compound (make_q, [(Variable make_x)]))]),
				(p1, (Compound (make_q, [(Constant 1)])), []),
				(((Base 1.0)-p1),
				 (Compound (make_q, [(Constant 2)])),
				 [])]
	     in foldl op *
		      (Base 1.0)
		      (map (fn observation =>
			       likelihood
				   (proof_distribution
					(Compound (make_p,
						   [(Constant observation)]))
					clauses))
			   [0, 1, 2, 2]) end)
	 [(Base 0.5), (Base 0.5)]
	 (Base 1000.0)
	 (Base 0.1))

val _ =
    let fun loop i result =
	    if i<=(Base 0.0) andalso (Base 0.0)<= i
	    then result
	    else let val ([p0, p1], _, _) = example ()
		 in loop (i-(Base 1.0)) [(write_real p0), (write_real p1)] end
    in loop (Base 1000.0) [(Base 0.0), (Base 0.0)] end
