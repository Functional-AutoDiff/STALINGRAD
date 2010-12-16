let naive_euler w =
  let charges = [[(Base 10.0); ((Base 10.0)-.w)];
		 [(Base 10.0); (Base 0.0)]]
  in let x_initial = [(Base 0.0); (Base 8.0)]
  in let xdot_initial = [(Base 0.75); (Base 0.0)]
  in let delta_t = (Base 1e-1)
  in let p x = fold_left
      ( +. )
      (Base 0.0)
      (map (fun c -> (Base 1.0)/.(distance x c)) charges)
  in let rec loop x xdot =
    let xddot = ktimesv (Base (-1.0)) (gradient_R p x)
    in let x_new = vplus x (ktimesv delta_t xdot)
    in if (Base 0.0)<(nth x_new 1)
    then loop x_new (vplus xdot (ktimesv delta_t xddot))
    else let delta_t_f = ((Base 0.0)-.(nth x 1))/.(nth xdot 1)
    in let x_t_f = vplus x (ktimesv delta_t_f xdot)
    in sqr (nth x_t_f 0)
  in loop x_initial xdot_initial


let _ = write_real
    (let w0 = (Base 0.0)
    in let [w_star] = multivariate_argmin_F (fun [w] -> naive_euler w) [w0]
    in w_star)
