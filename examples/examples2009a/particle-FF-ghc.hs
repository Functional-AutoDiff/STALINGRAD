import Common

naive_euler w =
    let charges = [[10, 10 - lift w], [10, 0]]
        x_initial = [0, 8]
        xdot_initial = [0.75, 0]
        delta_t = 1e-1
        p x = foldl (+) 0 (map (recip . (distance x)) charges)
        loop x @ [_, x_1] xdot @ [_, xdot_1] =
            let xddot = ktimesv (-1) ((gradient p) x)
                x_new @ [_, x_new_1] = vplus x (ktimesv delta_t xdot)
            in if x_new_1 > 0
               then loop x_new (vplus xdot (ktimesv delta_t xddot))
               else let delta_t_f = - x_1 / xdot_1
                        [x_t_f_0, _] = vplus x (ktimesv delta_t_f xdot)
                    in sqr x_t_f_0
    in loop x_initial xdot_initial

run = let w0 = 0
          [w_star] = multivariate_argmin (\ [w] -> naive_euler w) [w0]
      in w_star

main = print run
