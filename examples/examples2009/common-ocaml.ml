type ad_number = Dual_number of ad_number*ad_number*ad_number
  | Tape of ad_number*
	ad_number*
	(ad_number list)*
	(ad_number list)*
	(ad_number ref)*
	(ad_number ref)
  | Base of float

let epsilon = ref (Base 0.0)

let dual_number e x x' ( <= ) =
    if x'<=(Base 0.0) && (Base 0.0)<=x'
    then x
    else Dual_number (e, x, x')

let tape e x factors tapes =
    Tape (e, x, factors, tapes, ref (Base 0.0), ref (Base 0.0))

let lift_real_to_real f dfdx ( * ) ( <= ) =
    let rec self p =
      match p
      with
	(Dual_number (e, x, x')) -> dual_number e (self x) ((dfdx x)*x') ( <= )
      | (Tape (e, x, _, _, _, _)) -> tape e (self x) [dfdx x] [p]
      | Base x -> Base (f x)
    in self

let lift_real_cross_real_to_real f dfdx1 dfdx2 ( +. ) ( *. ) ( < ) ( <= ) =
    let rec self p1 p2 =
      match p1
      with (Dual_number (e1, x1, x1')) ->
	(match p2
	with (Dual_number (e2, x2, x2')) ->
	  if e1<e2
	  then dual_number e2 (self p1 x2) ((dfdx2 p1 x2)*.x2') ( <= )
	  else if e2<e1
	  then dual_number e1 (self x1 p2) ((dfdx1 x1 p2)*.x1') ( <= )
	  else dual_number
	      e1
	      (self x1 x2)
	      ((dfdx1 x1 x2)*.x1'+.(dfdx2 x1 x2)*.x2')
	      ( <= )
	| (Tape (e2, x2, _, _, _, _)) ->
	    if e1<e2
	    then tape e2 (self p1 x2) [dfdx2 p1 x2] [p2]
	    else dual_number e1 (self x1 p2) ((dfdx1 x1 p2)*.x1') ( <= )
	| (Base x2) ->
	    dual_number e1 (self x1 p2) ((dfdx1 x1 p2)*.x1') ( <= ))
      | (Tape (e1, x1, _, _, _, _)) ->
	  (match p2
	  with (Dual_number (e2, x2, x2')) ->
	    if e1<e2
	    then dual_number e2 (self p1 x2) ((dfdx2 p1 x2)*.x2') ( <= )
	    else tape e1 (self x1 p2) [dfdx1 x1 p2] [p1]
	  | (Tape (e2, x2, _, _, _, _)) ->
	      if e1<e2
	      then tape e2 (self p1 x2) [dfdx2 p1 x2] [p2]
	      else if e2<e1
	      then tape e1 (self x1 p2) [dfdx1 x1 p2] [p1]
	      else
		tape e1 (self x1 x2) [(dfdx1 x1 x2); (dfdx2 x1 x2)] [p1; p2]
	  | (Base x2) ->
	      tape e1 (self x1 p2) [dfdx1 x1 p2] [p1])
      | (Base x1) ->
	  (match p2
	  with (Dual_number (e2, x2, x2')) ->
	    dual_number e2 (self p1 x2) ((dfdx2 p1 x2)*.x2') ( <= )
	  | (Tape (e2, x2, _, _, _, _)) ->
	      tape e2 (self p1 x2) [dfdx2 p1 x2] [p2]
	  | (Base x2) -> Base (f x1 x2))
    in self

let lift_real_cross_real_to_bool f =
    let rec self p1 p2 =
      match p1
      with (Dual_number (_, x1, _)) ->
	(match p2
	with (Dual_number (_, x2, _)) -> self x1 x2
	| (Tape (_, x2, _, _, _, _)) ->  self x1 x2
	| (Base _) -> self x1 p2)
      | (Tape (_, x1, _, _, _, _)) ->
	  (match p2
	  with (Dual_number (_, x2, _)) -> self x1 x2
	  | (Tape (_, x2, _, _, _, _)) ->  self x1 x2
	  | (Base _) -> self x1 p2)
      | (Base x1) ->
	  (match p2
	  with (Dual_number (_, x2, _)) -> self p1 x2
	  | (Tape (_, x2, _, _, _, _)) -> self p1 x2
	  | (Base x2) -> f x1 x2)
    in self

let rec write_real p =
  match p with (Dual_number (_, x, _)) -> ((write_real x); p)
  | (Tape (_, x, _, _, _, _)) -> ((write_real x); p)
  | (Base x) -> ((Printf.printf "%.18g\n" x); p)

let (( +. ), ( -. ), ( *. ), ( /. ), sqrt, exp, ( < ), ( <= )) =
  let (plus, minus, times, divide, original_sqrt, original_exp, lt, ge) =
    (( +. ), ( -. ), ( *. ), ( /. ), sqrt, exp, ( < ), ( <= ))
  in let rec ( +. ) x1 x2 = (lift_real_cross_real_to_real
			       plus
			       (fun x1 x2 -> Base 1.0)
			       (fun x1 x2 -> Base 1.0)
			       ( +. )
			       ( *. )
			       ( < )
			       ( <= )
			       x1
			       x2)
  and ( -. ) x1 x2 = (lift_real_cross_real_to_real
			minus
			(fun x1 x2 -> Base 1.0)
			(fun x1 x2 -> Base (-1.0))
			( +. )
			( *. )
			( < )
			( <= )
			x1
			x2)
  and ( *. ) x1 x2 = (lift_real_cross_real_to_real
			times
			(fun x1 x2 -> x2)
			(fun x1 x2 -> x1)
			( +. )
			( *. )
			( < )
			( <= )
			x1
			x2)
  and ( /. ) x1 x2 = (lift_real_cross_real_to_real
			divide
			(fun x1 x2 -> (Base 1.0)/.x2)
			(fun x1 x2 -> (Base 0.0)-.x1/.(x2*.x2))
			( +. )
			( *. )
			( < )
			( <= )
			x1
			x2)
  and sqrt x = (lift_real_to_real
		  original_sqrt
		  (fun x -> (Base 1.0)/.((sqrt x)+.(sqrt x)))
		  ( *. )
		  ( <= )
		  x)
  and exp x = (lift_real_to_real
		 original_exp
		 exp
		 ( *. )
		 ( <= )
		 x)
  and ( < ) x1 x2 = lift_real_cross_real_to_bool lt x1 x2
  and ( <= ) x1 x2 = lift_real_cross_real_to_bool ge x1 x2
  in (( +. ), ( -. ), ( *. ), ( /. ), sqrt, exp, ( < ), ( <= ))

let derivative_F f x =
  (epsilon := !epsilon +. (Base 1.0);
   let y' =
     match (f (dual_number (!epsilon) x (Base 1.0) ( <= ) )) with
       Dual_number (e1, _, y') ->
	 if e1<(!epsilon) then Base 0.0 else y'
     | (Tape _) -> Base 0.0
     | (Base _) -> Base 0.0
   in epsilon := !epsilon -. (Base 1.0); y')

open List

let sqr x = x*.x

let map_n f n =
  let rec loop i = if i=n then [] else (f i)::(loop (i+1)) in loop 0

let vplus u v = map2 ( +. ) u v

let vminus u v = map2 ( -. ) u v

let ktimesv k = map (fun x -> k*.x)

let magnitude_squared x = fold_left ( +. ) (Base 0.0) (map sqr x)

let magnitude x = sqrt (magnitude_squared x)

let distance_squared u v = magnitude_squared (vminus v u)

let distance u v = sqrt (distance_squared u v)

let rec replace_ith (xh::xt) i xi =
    if i<=(Base 0.0) && (Base 0.0)<=i
    then xi::xt
    else xh::(replace_ith xt (i-.(Base 1.0)) xi)

let gradient_F f x =
  map_n
    (fun i -> derivative_F (fun xi -> f (replace_ith x (Base (float i)) xi)) (nth x i))
    (length x)

let rec determine_fanout (Tape (_, _, _, tapes, fanout, _)) =
    (fanout := !fanout+.(Base 1.0);
     if !fanout<=(Base 1.0) && (Base 1.0)<=(!fanout)
     (* for-each *)
     then (map determine_fanout tapes; ())
     else ())

let rec reverse_phase sensitivity1 (Tape (_, _, factors, tapes, fanout, sensitivity)) =
  (sensitivity := !sensitivity+.sensitivity1;
   fanout := !fanout-.(Base 1.0);
   if !fanout<=(Base 0.0) && (Base 0.0)<=(!fanout)
       (* for-each *)
   then ((map2
	    (fun factor tape -> reverse_phase (!sensitivity*.factor) tape)
	    factors tapes);
	 ())
   else ())

let gradient_R f x =
    (epsilon := !epsilon+.(Base 1.0);
     let x = map (fun xi -> (tape (!epsilon) xi [] [])) x in
     let y = f x in
     (match f x with (Dual_number _) -> ()
     | Tape (e1, _, _, _, _, _) ->
	 if e1<(!epsilon)
	 then ()
	 else (determine_fanout y; reverse_phase (Base 1.0) y)
     | Base _ -> ());
     epsilon := !epsilon-.(Base 1.0);
     map (fun (Tape (_, _, _, _, _, sensitivity)) -> !sensitivity) x)

let rec gradient_ascent_F f x0 n eta =
    if n<=(Base 0.0) && (Base 0.0)<=n
    then (x0, (f x0), (gradient_F f x0))
    else gradient_ascent_F
	     f (vplus x0 (ktimesv eta (gradient_F f x0))) (n-.(Base 1.0)) eta

let rec gradient_ascent_R f x0 n eta =
    if n<=(Base 0.0) && (Base 0.0)<=n
    then (x0, (f x0), (gradient_R f x0))
    else gradient_ascent_R
	     f (vplus x0 (ktimesv eta (gradient_R f x0))) (n-.(Base 1.0)) eta

let multivariate_argmin_F f x =
    let g = gradient_F f in
    let rec loop x fx gx eta i =
	       if (magnitude gx)<=(Base 1e-5)
	       then x
	       else if i<=(Base 10.0) && (Base 10.0)<=i
	       then loop x fx gx ((Base 2.0)*.eta) (Base 0.0)
	       else let x' = vminus x (ktimesv eta gx)
		    in if (distance x x')<=(Base 1e-5)
		       then x
		       else let fx' = (f x')
			    in if fx'<fx
			       then loop x' fx' (g x') eta (i+.(Base 1.0))
			       else loop x fx gx (eta/.(Base 2.0)) (Base 0.0)
       in loop x (f x) (g x) (Base 1e-5) (Base 0.0)

let rec multivariate_argmax_F f x =
    multivariate_argmin_F (fun x -> (Base 0.0)-.(f x)) x

let rec multivariate_max_F f x = f (multivariate_argmax_F f x)

let multivariate_argmin_R f x =
    let g = gradient_R f
    in let rec loop x fx gx eta i =
	       if (magnitude gx)<=(Base 1e-5)
	       then x
	       else if i<=(Base 10.0) && (Base 10.0)<=i
	       then loop x fx gx ((Base 2.0)*.eta) (Base 0.0)
	       else let x' = vminus x (ktimesv eta gx)
		    in if (distance x x')<=(Base 1e-5)
		       then x
		       else let fx' = (f x')
			    in if fx'<fx
			       then loop x' fx' (g x') eta (i+.(Base 1.0))
			       else loop x fx gx (eta/.(Base 2.0)) (Base 0.0)
       in loop x (f x) (g x) (Base 1e-5) (Base 0.0)

let rec multivariate_argmax_R f x =
  multivariate_argmin_R (fun x -> (Base 0.0)-.(f x)) x

let multivariate_max_R f x = f (multivariate_argmax_R f x)
