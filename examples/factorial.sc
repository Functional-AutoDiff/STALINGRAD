(letrec ((factorial (lambda (n) (if (zero? n) 1 (* n (factorial (- n 1)))))))
 (factorial 5))
