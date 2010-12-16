fun naive_euler w =
    let val charges = [[(Base 10.0), ((Base 10.0)-w)],
		       [(Base 10.0), (Base 0.0)]]
	val x_initial = [(Base 0.0), (Base 8.0)]
	val xdot_initial = [(Base 0.75), (Base 0.0)]
	val delta_t = (Base 1e~1)
	fun p x = foldl op +
			(Base 0.0)
			(map (fn c => (Base 1.0)/(distance x c)) charges)
	fun loop x xdot =
	    let val xddot = ktimesv (Base ~1.0) (gradient_F p x)
		val x_new = vplus x (ktimesv delta_t xdot)
	    in if (Base 0.0)<(List.nth (x_new, 1))
	       then loop x_new (vplus xdot (ktimesv delta_t xddot))
	       else let val delta_t_f = ((Base 0.0)-(List.nth (x, 1)))/
					(List.nth (xdot, 1))
			val x_t_f = vplus x (ktimesv delta_t_f xdot)
		    in sqr (List.nth (x_t_f, 0)) end end
    in loop x_initial xdot_initial end

fun run _ = (write_real let val w0 = (Base 0.0)
			    val [w_star] = multivariate_argmin_F
					       (fn [w] => naive_euler w)
					       [w0]
			in w_star end; 0)
