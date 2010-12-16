datatype ad_number = Dual_number of ad_number*ad_number*ad_number
		   | Tape of ad_number*
			     ad_number*
			     (ad_number list)*
			     (ad_number list)*
			     (ad_number ref)*
			     (ad_number ref)
		   | Base of real

val epsilon = ref (Base 0.0)

fun dual_number e x x' op <= =
    if x'<=(Base 0.0) andalso (Base 0.0)<=x'
    then x
    else Dual_number (e, x, x')

fun tape e x factors tapes =
    Tape (e, x, factors, tapes, ref (Base 0.0), ref (Base 0.0))

fun lift_real_to_real f dfdx op * op <= =
    let fun self (Dual_number (e, x, x')) =
	    dual_number e (self x) ((dfdx x)*x') op <=
          | self (p as (Tape (e, x, _, _, _, _))) =
	    tape e (self x) [dfdx x] [p]
	  | self (Base x) = Base (f x)
    in self end

fun lift_real_cross_real_to_real f dfdx1 dfdx2 op + op * op < op <= =
    let fun self ((p1 as (Dual_number (e1, x1, x1'))),
		  (p2 as (Dual_number (e2, x2, x2')))) =
            if e1<e2
            then dual_number e2 (self (p1, x2)) ((dfdx2 p1 x2)*x2') op <=
	    else if e2<e1
	    then dual_number e1 (self (x1, p2)) ((dfdx1 x1 p2)*x1') op <=
	    else dual_number
		     e1
		     (self (x1, x2))
		     ((dfdx1 x1 x2)*x1'+(dfdx2 x1 x2)*x2')
		     op <=
	  | self ((p1 as (Dual_number (e1, x1, x1'))),
		  (p2 as (Tape (e2, x2, _, _, _, _)))) =
	    if e1<e2
	    then tape e2 (self (p1, x2)) [dfdx2 p1 x2] [p2]
	    else dual_number e1 (self (x1, p2)) ((dfdx1 x1 p2)*x1') op <=
	  | self ((Dual_number (e1, x1, x1')), (p2 as (Base x2))) =
	    dual_number e1 (self (x1, p2)) ((dfdx1 x1 p2)*x1') op <=
	  | self ((p1 as (Tape (e1, x1, _, _, _, _))),
		  (p2 as (Dual_number (e2, x2, x2')))) =
	    if e1<e2
	    then dual_number e2 (self (p1, x2)) ((dfdx2 p1 x2)*x2') op <=
	    else tape e1 (self (x1, p2)) [dfdx1 x1 p2] [p1]
	  | self ((p1 as (Tape (e1, x1, _, _, _, _))),
		  (p2 as (Tape (e2, x2, _, _, _, _)))) =
	    if e1<e2
	    then tape e2 (self (p1, x2)) [dfdx2 p1 x2] [p2]
	    else if e2<e1
	    then tape e1 (self (x1, p2)) [dfdx1 x1 p2] [p1]
	    else
		tape e1 (self (x1, x2)) [(dfdx1 x1 x2), (dfdx2 x1 x2)] [p1, p2]
	  | self ((p1 as (Tape (e1, x1, _, _, _, _))), (p2 as (Base x2))) =
	    tape e1 (self (x1, p2)) [dfdx1 x1 p2] [p1]
	  | self ((p1 as (Base x1)), (Dual_number (e2, x2, x2'))) =
	    dual_number e2 (self (p1, x2)) ((dfdx2 p1 x2)*x2') op <=
	  | self ((p1 as (Base x1)), (p2 as (Tape (e2, x2, _, _, _, _)))) =
	    tape e2 (self (p1, x2)) [dfdx2 p1 x2] [p2]
	  | self ((Base x1), (Base x2)) = Base (f (x1, x2))
    in self end

fun lift_real_cross_real_to_bool f =
    let fun self ((Dual_number (_, x1, _)), (Dual_number (_, x2, _))) =
	    self (x1, x2)
	  | self ((Dual_number (_, x1, _)), (Tape (_, x2, _, _, _, _))) =
	    self (x1, x2)
	  | self ((Dual_number (_, x1, _)), (p2 as (Base _))) = self (x1, p2)
	  | self ((Tape (_, x1, _, _, _, _)), (Dual_number (_, x2, _))) =
	    self (x1, x2)
	  | self ((Tape (_, x1, _, _, _, _)), (Tape (_, x2, _, _, _, _))) =
	    self (x1, x2)
	  | self ((Tape (_, x1, _, _, _, _)), (p2 as (Base _))) = self (x1, p2)
	  | self ((p1 as (Base _)), (Dual_number (_, x2, _))) = self (p1, x2)
	  | self ((p1 as (Base _)), (Tape (_, x2, _, _, _, _))) = self (p1, x2)
	  | self ((Base x1), (Base x2)) = f (x1, x2)
    in self end

open Real.Math

val (op +, op -, op *, op /, sqrt, exp, op <, op <=) =
    let val plus = op +
	val minus = op -
	val times = op *
	val divide = op /
	val original_sqrt = sqrt
	val original_exp = exp
        val lt = op <
        val le = op <=
    in let fun op + (x1, x2) =
	       lift_real_cross_real_to_real
		   plus
		   (fn _ => fn _ => Base 1.0)
		   (fn _ => fn _ => Base 1.0)
		   op +
		   op *
                   op <
		   op <=
		   (x1, x2)
	   and op - (x1, x2) =
	       lift_real_cross_real_to_real
		   minus
		   (fn _ => fn _ => Base 1.0)
		   (fn _ => fn _ => Base ~1.0)
		   op +
		   op *
                   op <
		   op <=
		   (x1, x2)
	   and op * (x1, x2) =
	       lift_real_cross_real_to_real
		   times
		   (fn _ => fn x2 => x2)
		   (fn x1 => fn _ => x1)
		   op +
		   op *
                   op <
		   op <=
		   (x1, x2)
	   and op / (x1, x2) =
	       lift_real_cross_real_to_real
		   divide
		   (fn _ => fn x2 => (Base 1.0)/x2)
		   (fn x1 => fn x2 => (Base 0.0)-x1/(x2*x2))
		   op +
		   op *
                   op <
		   op <=
		   (x1, x2)
	   and sqrt x =
	       lift_real_to_real
		   original_sqrt
		   (fn x => (Base 1.0)/((Base 2.0)*(sqrt x)))
		   op *
		   op <=
		   x
	   and exp x =
	       lift_real_to_real
		   original_exp
		   exp
		   op *
		   op <=
		   x
	   and op < (x1, x2) = lift_real_cross_real_to_bool lt (x1, x2)
	   and op <= (x1, x2) = lift_real_cross_real_to_bool le (x1, x2)
       in (op +, op -, op *, op /, sqrt, exp, op <, op <=) end end

fun derivative_F f x =
    (epsilon := !epsilon+(Base 1.0);
     let val y' =
	     case (f (dual_number (!epsilon) x (Base 1.0) op <=)) of
		 Dual_number (e1, _, y') =>
		 if e1<(!epsilon) then Base 0.0 else y'
	       | Tape t => Base 0.0
	       | Base x => Base 0.0
     in epsilon := !epsilon-(Base 1.0); y' end)

fun replace_ith (xh::xt) i xi =
    if i<=(Base 0.0) andalso (Base 0.0)<=i
    then xi::xt
    else xh::(replace_ith xt (i-(Base 1.0)) xi)

fun gradient_F f x =
    List.tabulate
	((length x),
	 (fn i => derivative_F (fn xi => f (replace_ith x (Base (real i)) xi))
			       (List.nth (x, i))))

fun determine_fanout (Tape (_, _, _, tapes, fanout, _)) =
    (fanout := !fanout+(Base 1.0);
     if !fanout<=(Base 1.0) andalso (Base 1.0)<=(!fanout)
     (* for-each *)
     then (map determine_fanout tapes; ())
     else ())

fun reverse_phase sensitivity1
		  (Tape (_, _, factors, tapes, fanout, sensitivity)) =
    (sensitivity := !sensitivity+sensitivity1;
     fanout := !fanout-(Base 1.0);
     if !fanout<=(Base 0.0) andalso (Base 0.0)<=(!fanout)
     (* for-each *)
     then (ListPair.map
               (fn (factor, tape) => reverse_phase (!sensitivity*factor) tape)
               (factors, tapes);
	   ())
     else ())

fun gradient_R f x =
    (epsilon := !epsilon+(Base 1.0);
     let val x = map (fn xi => (tape (!epsilon) xi [] [])) x
     in (case f x of
             Dual_number _ => ()
	   | y as Tape (e1, _, _, _, _, _) =>
             if e1<(!epsilon)
             then ()
	     else (determine_fanout y; reverse_phase (Base 1.0) y)
	   | Base _ => ());
        epsilon := !epsilon-(Base 1.0);
        map (fn (Tape (_, _, _, _, _, sensitivity)) => !sensitivity) x end)

fun derivative_R f x = let val [y'] = gradient_R (fn [x] => f x) [x] in y' end

fun write_real (p as (Dual_number (_, x, _))) = ((write_real x); p)
  | write_real (p as (Tape (_, x, _, _, _, _))) = ((write_real x); p)
  | write_real (p as (Base x)) = ((print (Real.toString x)); (print "\n"); p)

fun sqr x = x*x

fun vplus u v = ListPair.map op + (u, v)

fun vminus u v = ListPair.map op - (u, v)

fun ktimesv k = map (fn x => k*x)

fun magnitude_squared x = foldl op + (Base 0.0) (map sqr x)

fun magnitude x = sqrt (magnitude_squared x)

fun distance_squared u v = magnitude_squared (vminus v u)

fun distance u v = sqrt (distance_squared u v)

fun gradient_ascent_F f x0 n eta =
    if n<=(Base 0.0) andalso (Base 0.0)<=n
    then (x0, (f x0), (gradient_F f x0))
    else gradient_ascent_F
	     f (vplus x0 (ktimesv eta (gradient_F f x0))) (n-(Base 1.0)) eta

fun gradient_ascent_R f x0 n eta =
    if n<=(Base 0.0) andalso (Base 0.0)<=n
    then (x0, (f x0), (gradient_R f x0))
    else gradient_ascent_R
	     f (vplus x0 (ktimesv eta (gradient_R f x0))) (n-(Base 1.0)) eta

fun multivariate_argmin_F f x =
    let val g = gradient_F f
    in let fun loop x fx gx eta i =
	       if (magnitude gx)<=(Base 1e~5)
	       then x
	       else if i<=(Base 10.0) andalso (Base 10.0)<=i
	       then loop x fx gx ((Base 2.0)*eta) (Base 0.0)
	       else let val x' = vminus x (ktimesv eta gx)
		    in if (distance x x')<=(Base 1e~5)
		       then x
		       else let val fx' = (f x')
			    in if fx'<fx
			       then loop x' fx' (g x') eta (i+(Base 1.0))
			       else loop x fx gx (eta/(Base 2.0)) (Base 0.0)
			    end end
       in loop x (f x) (g x) (Base 1e~5) (Base 0.0) end end

fun multivariate_argmax_F f x =
    multivariate_argmin_F (fn x => (Base 0.0)-(f x)) x

fun multivariate_max_F f x = f (multivariate_argmax_F f x)

fun multivariate_argmin_R f x =
    let val g = gradient_R f
    in let fun loop x fx gx eta i =
	       if (magnitude gx)<=(Base 1e~5)
	       then x
	       else if i<=(Base 10.0) andalso (Base 10.0)<=i
	       then loop x fx gx ((Base 2.0)*eta) (Base 0.0)
	       else let val x' = vminus x (ktimesv eta gx)
		    in if (distance x x')<=(Base 1e~5)
		       then x
		       else let val fx' = (f x')
			    in if fx'<fx
			       then loop x' fx' (g x') eta (i+(Base 1.0))
			       else loop x fx gx (eta/(Base 2.0)) (Base 0.0)
			    end end
       in loop x (f x) (g x) (Base 1e~5) (Base 0.0) end end

fun multivariate_argmax_R f x =
    multivariate_argmin_R (fn x => (Base 0.0)-(f x)) x

fun multivariate_max_R f x = f (multivariate_argmax_R f x)
