(let ((factorial
       (y (lambda factorial
	   (lambda n
	    (if (zero? n)
		1
		(* (cons n (factorial (- (cons n 1)))))))))))
 (factorial 5))
