type value = Number of int
  | True
  | False
  | Closure of (((ad_number*((int*value) list)*value) list) ->
      ((ad_number*((int*value) list)*value) list))

type expression = Constant of value
  | Variable of int
  | Lambda of int*expression
  | Application of expression*expression

exception Undecidable

let make_ignore = 0

let make_if_procedure = 1

let make_x0 = 2

let make_x1 = 3

let rec binds a b =
  match a, b with
    [], _ -> false
  | ((variable1, _)::environment), variable2 ->
      if variable1=variable2 then true else binds environment variable2

let rec lookup_value variable1 ((variable2, value)::environment) =
  if variable1=variable2 then value else lookup_value variable1 environment

let same p1 p2 =
  match p1, p2 with
    (Number m), (Number n) -> m=n
  | True, True -> true
  | False, False -> true
  | (Closure _), (Closure _) -> raise Undecidable
  | _, _ -> false

let rec merge_environments p1 p2 =
  (match p1, p2 with
    [], environment2 -> Some environment2
  | ((variable1, value1)::environment1), environment2 ->
      match merge_environments environment1 environment2 with
	None -> None
      | Some environment ->
	  if binds environment variable1
	  then if same (lookup_value variable1 environment) value1
	  then Some environment
	  else None
	  else Some ((variable1, value1)::environment))

let singleton_tagged_distribution value = [((Base 1.0), [], value)]

let boolean_distribution p variable =
  [(((Base 1.0)-.p), [(variable, False)], False);
   (p, [(variable, True)], True)]

let normalize_tagged_distribution tagged_distribution =
  let n = let rec loop a =
    (match a with
      [] -> (Base 0.0)
    | ((p, _, _)::tagged_distribution) -> p+.(loop tagged_distribution))
  in loop tagged_distribution
  in map (fun (p, environment, value) -> ((p/.n), environment, value)) tagged_distribution

let rec remove_inconsistent_triples a =
  match a with
    [] -> []
  | ((_, None, _)::tagged_distribution) -> remove_inconsistent_triples tagged_distribution
  | ((p, (Some environment), value)::tagged_distribution) ->
      ((p, environment, value)::(remove_inconsistent_triples tagged_distribution))

let map_tagged_distribution f tagged_distribution =
  normalize_tagged_distribution
    (let rec loop a =
      match a with
	[] -> []
      | ((p, environment, value)::tagged_distribution) ->
	  (remove_inconsistent_triples
	     (map (fun (p1, environment1, value1) ->
	       ((p*.p1),
		(merge_environments environment environment1),
		value1))
		((f value))))@
	  (loop tagged_distribution)
    in loop tagged_distribution)

let rec evaluate a environment =
  match a with
    (Constant value) -> singleton_tagged_distribution value
  | (Variable variable) -> lookup_value variable environment
  | (Lambda (variable, body)) -> singleton_tagged_distribution
	(Closure (fun tagged_distribution ->
	  evaluate body
	    ((variable, tagged_distribution)::environment)))
  | (Application (callee, argument)) ->
      let tagged_distribution = evaluate argument environment
      in map_tagged_distribution
	(fun value ->
	  match value with
	    Closure f -> f tagged_distribution)
	(evaluate callee environment)

let rec likelihood p1 p2 =
  match p1, p2 with
    value, [] -> (Base 0.0)
  | value1, ((p, _, value2)::tagged_distribution) ->
      (if same value1 value2 then p else (Base 0.0))+.
	(likelihood value1 tagged_distribution)

let make_if antecedent consequent alternate =
  (Application
     ((Application
	 ((Application ((Variable make_if_procedure), antecedent)),
	  (Lambda (make_ignore, consequent)))),
      (Lambda (make_ignore, alternate))))

let example _ =
  (gradient_ascent_F
     (fun [p0; p1] ->
       let tagged_distribution =
	 evaluate
	   (make_if (Variable make_x0)
	      (Constant (Number 0))
	      (make_if (Variable make_x1)
		 (Constant (Number 1))
		 (Constant (Number 2))))
	   [(make_x0, (boolean_distribution p0 make_x0));
	    (make_x1, (boolean_distribution p1 make_x1));
	    (make_if_procedure,
	     (singleton_tagged_distribution
		(Closure
		   (fun x ->
		     (singleton_tagged_distribution
			(Closure
			   (fun y ->
			     (singleton_tagged_distribution
				(Closure
				   (fun z ->
				     (map_tagged_distribution
					(fun xe ->
					  (map_tagged_distribution
					     (fun ye ->
					       match ye with
						 Closure yf ->
						   (map_tagged_distribution
						      (fun ze ->
							match ze with
							  Closure zf ->
							    (match xe with
							      Number _ -> (yf (singleton_tagged_distribution False))
							    | True -> (yf (singleton_tagged_distribution False))
							    | False -> (zf (singleton_tagged_distribution False))
							    | Closure _ -> (yf (singleton_tagged_distribution False))))
						      z))
					     y))
					x)))))))))))]
       in fold_left ( *. )
	 (Base 1.0)
	 (map (fun observation -> likelihood observation tagged_distribution)
	    [(Number 0); (Number 1); (Number 2); (Number 2)]))
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
