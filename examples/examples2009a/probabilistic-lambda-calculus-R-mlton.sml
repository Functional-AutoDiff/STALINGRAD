datatype value = Number of int
	       | True
	       | False
	       | Closure of ((ad_number*((int*value) list)*value) list)->
			    ((ad_number*((int*value) list)*value) list)

datatype expression = Constant of value
		    | Variable of int
		    | Lambda of int*expression
		    | Application of expression*expression

exception undecidable

val make_ignore = 0

val make_if_procedure = 1

val make_x0 = 2

val make_x1 = 3

fun binds [] _ = false
  | binds ((variable1, _)::environment) variable2 =
    if variable1=variable2 then true else binds environment variable2

fun lookup_value variable1 ((variable2, value)::environment) =
    if variable1=variable2 then value else lookup_value variable1 environment

fun same (Number m) (Number n) = m=n
  | same True True = true
  | same False False = true
  | same (Closure _) (Closure _) = raise undecidable
  | same _ _ = false

fun merge_environments [] environment2 = SOME environment2
  | merge_environments ((variable1, value1)::environment1) environment2 =
    case merge_environments environment1 environment2 of
	NONE => NONE
      | SOME environment =>
	if binds environment variable1
	then if same (lookup_value variable1 environment) value1
	     then SOME environment
	     else NONE
	else SOME ((variable1, value1)::environment)

fun singleton_tagged_distribution value = [((Base 1.0), [], value)]

fun boolean_distribution p variable =
    [(((Base 1.0)-p), [(variable, False)], False),
     (p, [(variable, True)], True)]

fun normalize_tagged_distribution tagged_distribution =
    let val n = let fun loop [] = (Base 0.0)
		      | loop ((p, _, _)::tagged_distribution) =
			p+(loop tagged_distribution)
		in loop tagged_distribution end
    in map (fn (p, environment, value) => ((p/n), environment, value))
	   tagged_distribution end

fun remove_inconsistent_triples [] = []
  | remove_inconsistent_triples ((_, NONE, _)::tagged_distribution) =
    remove_inconsistent_triples tagged_distribution
  | remove_inconsistent_triples
	((p, (SOME environment), value)::tagged_distribution) =
    ((p, environment, value)::
     (remove_inconsistent_triples tagged_distribution))

fun map_tagged_distribution f (tagged_distribution) =
    (normalize_tagged_distribution
	 let fun loop [] = []
	       | loop ((p, environment, value)::tagged_distribution) =
		 (remove_inconsistent_triples
		      (map (fn (p1, environment1, value1) =>
			       ((p*p1),
				(merge_environments environment environment1),
				value1))
			   ((f value))))@
		 (loop tagged_distribution)
	 in loop tagged_distribution end)

fun evaluate (Constant value) environment =
    singleton_tagged_distribution value
  | evaluate (Variable variable) environment =
    lookup_value variable environment
  | evaluate (Lambda (variable, body)) environment =
    singleton_tagged_distribution
	(Closure (fn tagged_distribution =>
		     evaluate body
			      ((variable, tagged_distribution)::environment)))
  | evaluate (Application (callee, argument)) environment =
    let val tagged_distribution = evaluate argument environment
    in map_tagged_distribution (fn value =>
				   case value of
				       Closure f => f tagged_distribution)
			       (evaluate callee environment) end

fun likelihood value [] = (Base 0.0)
  | likelihood value1 ((p, _, value2)::tagged_distribution) =
    (if same value1 value2 then p else (Base 0.0))+
    (likelihood value1 tagged_distribution)

fun make_if antecedent consequent alternate =
    (Application
	 ((Application
	       ((Application ((Variable make_if_procedure), antecedent)),
		(Lambda (make_ignore, consequent)))),
	  (Lambda (make_ignore, alternate))))

fun example _ =
    (gradient_ascent_R
	 (fn [p0, p1] =>
	     let val tagged_distribution =
		     evaluate
			 (make_if (Variable make_x0)
				  (Constant (Number 0))
				  (make_if (Variable make_x1)
					   (Constant (Number 1))
					   (Constant (Number 2))))
			 [(make_x0, (boolean_distribution p0 make_x0)),
			  (make_x1, (boolean_distribution p1 make_x1)),
			  (make_if_procedure,
			   (singleton_tagged_distribution
				(Closure
				     (fn x =>
					 (singleton_tagged_distribution
					      (Closure
						   (fn y =>
						       (singleton_tagged_distribution
							    (Closure
								 (fn z =>
								     (map_tagged_distribution
									  (fn xe =>
									      (map_tagged_distribution
										   (fn ye =>
										       case ye of
											   Closure yf =>
											   (map_tagged_distribution
												(fn ze =>
												    case ze of
													Closure zf =>
													case xe of
													    Number _ => (yf (singleton_tagged_distribution False))
													  | True => (yf (singleton_tagged_distribution False))
													  | False => (zf (singleton_tagged_distribution False))
													  | Closure _ => (yf (singleton_tagged_distribution False)))
												z))
										   y))
									  x)))))))))))]
	     in foldl op *
		      (Base 1.0)
		      (map (fn observation =>
			       likelihood observation tagged_distribution)
			   [(Number 0), (Number 1), (Number 2), (Number 2)]) end)
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
