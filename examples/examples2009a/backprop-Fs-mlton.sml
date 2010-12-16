fun sum_activities activities (bias::ws) =
    foldl op + bias (ListPair.map op * (ws, activities))

fun sum_layer activities ws_layer = map (sum_activities activities) ws_layer

fun sigmoid x = (Base 1.0)/((exp ((Base 0.0)-x))+(Base 1.0))

fun forward_pass [] in1 = in1
  | forward_pass (ws_layer::ws_layers) in1 =
    forward_pass ws_layers (map sigmoid (sum_layer in1 ws_layer))

fun error_on_dataset dataset ws_layers =
    foldl op +
	  (Base 0.0)
	  (map (fn (in1, target) =>
		   (Base 0.5)*
		   (magnitude_squared
			(vminus (forward_pass ws_layers in1) target)))
	       dataset)

fun s_kstar ws k y =
    ListPair.map (fn (l, y) =>
		     ListPair.map (fn (u, y) =>
				      ListPair.map (fn (w, y) => w-k*y)
						   (u, y))
				  (l, y))
		 (ws, y)

fun weight_gradient f ws =
    List.tabulate
	((length ws),
	 (fn li =>
	     let val ll = List.nth (ws, li)
	     in List.tabulate
		    ((length ll),
		     (fn ui =>
			 List.tabulate
			     ((length (List.nth (ll, ui))),
			      (fn wi =>
				  (derivative_F
				       (fn x =>
					   f (replace_ith
						  ws
						  (Base (real li))
						  (replace_ith
						       (List.nth (ws, li))
						       (Base (real ui))
						       (replace_ith
							    (List.nth
								 ((List.nth
								       (ws,
									li)),
								  ui))
							    (Base (real wi))
							    x))))
				       (List.nth
					    ((List.nth
						  ((List.nth (ws, li)),
						   ui)),
					     wi))))))) end))

fun vanilla f w0 n eta =
    if n<=(Base 0.0) andalso (Base 0.0)<=n
    then f w0
    else vanilla f (s_kstar w0 eta (weight_gradient f w0)) (n-(Base 1.0)) eta

val xor_ws0 = [[[Base 0.0, Base ~0.284227, Base 1.16054],
		[Base 0.0, Base 0.617194, Base 1.30467]],
	       [[Base 0.0, Base ~0.084395, Base 0.648461]]]

val xor_data = [([Base 0.0, Base 0.0], [Base 0.0]),
		([Base 0.0, Base 1.0], [Base 1.0]),
		([Base 1.0, Base 0.0], [Base 1.0]),
		([Base 1.0, Base 1.0], [Base 0.0])]

val _ = write_real (vanilla (error_on_dataset xor_data)
			    xor_ws0
			    (Base 1000000.0)
			    (Base 0.3))
