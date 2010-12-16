let _ =
  let start = [(Base 1.0); (Base 1.0)] in
  let f x1 y1 x2 y2 = ((sqr x1)+.(sqr y1))-.((sqr x2)+.(sqr y2)) in
  let [x1_star; y1_star] =
    multivariate_argmin_F
      (fun [x1; y1] ->
	multivariate_max_R (fun [x2; y2] -> f x1 y1 x2 y2) start)
      start in
  let [x2_star; y2_star] =
    multivariate_argmax_R
      (fun [x2; y2] -> f x1_star y1_star x2 y2)
      start in
  [[(write_real x1_star); (write_real y1_star)];
   [(write_real x2_star); (write_real y2_star)]];
  0
