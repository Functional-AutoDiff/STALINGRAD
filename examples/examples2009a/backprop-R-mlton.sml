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
    (epsilon := !epsilon+(Base 1.0);
     let val ws = map (fn l =>
			  map (fn u =>
				  map (fn w => (tape (!epsilon) w [] [])) u) l)
		      ws
     in (case f ws of
             Dual_number _ => ()
	   | y as Tape (e1, _, _, _, _, _) =>
             if e1<(!epsilon)
             then ()
	     else (determine_fanout y; reverse_phase (Base 1.0) y)
	   | Base _ => ());
        epsilon := !epsilon-(Base 1.0);
        map (fn l =>
		map (fn u =>
			map (fn (Tape (_, _, _, _, _, sensitivity)) =>
				!sensitivity)
			    u)
		    l)
	    ws end)

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
