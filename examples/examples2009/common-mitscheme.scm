(define *e* 0)

(define <_e <)

(define dual-number?
 (let ((pair? pair?)) (lambda (p) (and (pair? p) (eq? (car p) 'dual-number)))))

(define (dual-number e x x-prime)
 (if (dzero? x-prime) x (list 'dual-number e x x-prime)))

(define dual-number-epsilon cadr)

(define dual-number-primal caddr)

(define dual-number-perturbation cadddr)

(define tape?
 (let ((pair? pair?)) (lambda (p) (and (pair? p) (eq? (car p) 'tape)))))

(define (tape e primal factors tapes) (list 'tape e primal factors tapes 0 0))

(define tape-epsilon cadr)

(define tape-primal caddr)

(define tape-factors cadddr)

(define (tape-tapes tape) (cadddr (cdr tape)))

(define (tape-fanout tape) (cadddr (cddr tape)))

(define (set-tape-fanout! tape fanout) (set-car! (cdddr (cddr tape)) fanout))

(define (tape-sensitivity tape) (cadddr (cdddr tape)))

(define (set-tape-sensitivity! tape sensitivity)
 (set-car! (cdddr (cdddr tape)) sensitivity))

(define (lift-real->real f df/dx)
 (letrec ((self (lambda (p)
		 (cond ((dual-number? p)
			(dual-number (dual-number-epsilon p)
				     (self (dual-number-primal p))
				     (d* (df/dx (dual-number-primal p))
					 (dual-number-perturbation p))))
		       ((tape? p)
			(tape (tape-epsilon p)
			      (self (tape-primal p))
			      (list (df/dx (tape-primal p)))
			      (list p)))
		       (else (f p))))))
  self))

(define (lift-real*real->real f df/dx1 df/dx2)
 (letrec ((self
	   (lambda (p1 p2)
	    (cond
	     ((dual-number? p1)
	      (cond
	       ((dual-number? p2)
		(cond ((<_e (dual-number-epsilon p1)
			    (dual-number-epsilon p2))
		       (dual-number (dual-number-epsilon p2)
				    (self p1 (dual-number-primal p2))
				    (d* (df/dx2 p1 (dual-number-primal p2))
					(dual-number-perturbation p2))))
		      ((<_e (dual-number-epsilon p2)
			    (dual-number-epsilon p1))
		       (dual-number (dual-number-epsilon p1)
				    (self (dual-number-primal p1) p2)
				    (d* (df/dx1 (dual-number-primal p1) p2)
					(dual-number-perturbation p1))))
		      (else
		       (dual-number (dual-number-epsilon p1)
				    (self (dual-number-primal p1)
					  (dual-number-primal p2))
				    (d+ (d* (df/dx1 (dual-number-primal p1)
						    (dual-number-primal p2))
					    (dual-number-perturbation p1))
					(d* (df/dx2 (dual-number-primal p1)
						    (dual-number-primal p2))
					    (dual-number-perturbation p2)))))))
	       ((tape? p2)
		(if (<_e (dual-number-epsilon p1) (tape-epsilon p2))
		    (tape (tape-epsilon p2)
			  (self p1 (tape-primal p2))
			  (list (df/dx2 p1 (tape-primal p2)))
			  (list p2))
		    (dual-number (dual-number-epsilon p1)
				 (self (dual-number-primal p1) p2)
				 (d* (df/dx1 (dual-number-primal p1) p2)
				     (dual-number-perturbation p1)))))
	       (else (dual-number (dual-number-epsilon p1)
				  (self (dual-number-primal p1) p2)
				  (d* (df/dx1 (dual-number-primal p1) p2)
				      (dual-number-perturbation p1))))))
	     ((tape? p1)
	      (cond
	       ((dual-number? p2)
		(if (<_e (tape-epsilon p1) (dual-number-epsilon p2))
		    (dual-number (dual-number-epsilon p2)
				 (self p1 (dual-number-primal p2))
				 (d* (df/dx2 p1 (dual-number-primal p2))
				     (dual-number-perturbation p2)))
		    (tape (tape-epsilon p1)
			  (self (tape-primal p1) p2)
			  (list (df/dx1 (tape-primal p1) p2))
			  (list p1))))
	       ((tape? p2)
		(cond
		 ((<_e (tape-epsilon p1) (tape-epsilon p2))
		  (tape (tape-epsilon p2)
			(self p1 (tape-primal p2))
			(list (df/dx2 p1 (tape-primal p2)))
			(list p2)))
		 ((<_e (tape-epsilon p2) (tape-epsilon p1))
		  (tape (tape-epsilon p1)
			(self (tape-primal p1) p2)
			(list (df/dx1 (tape-primal p1) p2))
			(list p1)))
		 (else (tape (tape-epsilon p1)
			     (self (tape-primal p1) (tape-primal p2))
			     (list (df/dx1 (tape-primal p1) (tape-primal p2))
				   (df/dx2 (tape-primal p1) (tape-primal p2)))
			     (list p1 p2)))))
	       (else (tape (tape-epsilon p1)
			   (self (tape-primal p1) p2)
			   (list (df/dx1 (tape-primal p1) p2))
			   (list p1)))))
	     (else (cond ((dual-number? p2)
			  (dual-number (dual-number-epsilon p2)
				       (self p1 (dual-number-primal p2))
				       (d* (df/dx2 p1 (dual-number-primal p2))
					   (dual-number-perturbation p2))))
			 ((tape? p2)
			  (tape (tape-epsilon p2)
				(self p1 (tape-primal p2))
				(list (df/dx2 p1 (tape-primal p2)))
				(list p2)))
			 (else (f p1 p2))))))))
  self))

(define (primal* p)
 (cond ((dual-number? p) (primal* (dual-number-primal p)))
       ((tape? p) (primal* (tape-primal p)))
       (else p)))

(define (lift-real^n->boolean f) (lambda ps (apply f (map primal* ps))))

(define dpair?
 (let ((pair? pair?))
  (lambda (x) (and (pair? x) (not (dual-number? x)) (not (tape? x))))))

(define d+ (lift-real*real->real + (lambda (x1 x2) 1) (lambda (x1 x2) 1)))

(define d- (lift-real*real->real - (lambda (x1 x2) 1) (lambda (x1 x2) -1)))

(define d*
 (lift-real*real->real * (lambda (x1 x2) x2) (lambda (x1 x2) x1)))

(define d/
 (lift-real*real->real
  / (lambda (x1 x2) (d/ 1 x2)) (lambda (x1 x2) (d- 0 (d/ x1 (d* x2 x2))))))

(define dsqrt (lift-real->real sqrt (lambda (x) (d/ 1 (d* 2 (dsqrt x))))))

(define dexp (lift-real->real exp (lambda (x) (dexp x))))

(define dlog (lift-real->real log (lambda (x) (d/ 1 x))))

(define dsin (lift-real->real sin (lambda (x) (dcos x))))

(define dcos (lift-real->real cos (lambda (x) (d- 0 (dsin x)))))

(define datan (lift-real*real->real
	       atan
	       (lambda (x1 x2) (d/ (d- 0 x2) (d+ (d* x1 x1) (d* x2 x2))))
	       (lambda (x1 x2) (d/ x1 (d+ (d* x1 x1) (d* x2 x2))))))

(define d= (lift-real^n->boolean =))

(define d< (lift-real^n->boolean <))

(define d> (lift-real^n->boolean >))

(define d<= (lift-real^n->boolean <=))

(define d>= (lift-real^n->boolean >=))

(define dzero? (let ((= =)) (lift-real^n->boolean (lambda (x) (= x 0)))))

(define dpositive? (lift-real^n->boolean positive?))

(define dnegative? (lift-real^n->boolean negative?))

(define dreal? (lift-real^n->boolean real?))

(define (derivative-F f)
 (lambda (x)
  (set! *e* (d+ *e* 1))
  (let* ((y (f (dual-number *e* x 1)))
	 (y-prime (if (or (not (dual-number? y))
			  (<_e (dual-number-epsilon y) *e*))
		      0
		      (dual-number-perturbation y))))
   (set! *e* (d- *e* 1))
   y-prime)))

(define (replace-ith x i xi)
 (if (dzero? i)
     (cons xi (cdr x))
     (cons (car x) (replace-ith (cdr x) (d- i 1) xi))))

(define (gradient-F f)
 (lambda (x)
  ((map-n
    (lambda (i)
     ((derivative-F (lambda (xi) (f (replace-ith x i xi)))) (list-ref x i))))
   (length x))))

(define (determine-fanout! tape)
 (set-tape-fanout! tape (d+ (tape-fanout tape) 1))
 (cond ((d= (tape-fanout tape) 1)
	(for-each determine-fanout! (tape-tapes tape)))))

(define (reverse-phase! sensitivity tape)
 (set-tape-sensitivity! tape (d+ (tape-sensitivity tape) sensitivity))
 (set-tape-fanout! tape (d- (tape-fanout tape) 1))
 (cond ((dzero? (tape-fanout tape))
	(let ((sensitivity (tape-sensitivity tape)))
	 (for-each (lambda (factor tape)
		    (reverse-phase! (d* sensitivity factor) tape))
		   (tape-factors tape)
		   (tape-tapes tape))))))

(define (gradient-R f)
 (lambda (x)
  (set! *e* (d+ *e* 1))
  (let* ((x (map (lambda (xi) (tape *e* xi '() '())) x)) (y (f x)))
   (cond ((and (tape? y) (not (<_e (tape-epsilon y) *e*)))
	  (determine-fanout! y)
	  (reverse-phase! 1 y)))
   (set! *e* (d- *e* 1))
   (map tape-sensitivity x))))

(define (derivative-R f)
 (lambda (x) (car ((gradient-R (lambda (x) (f (car x)))) (list x)))))

(define (write-real x)
 (cond ((dual-number? x) (write-real (dual-number-primal x)) x)
       ((tape? x) (write-real (tape-primal x)) x)
       (else (write x) (newline) x)))

(define (first x) (car x))

(define (second x) (car (cdr x)))

(define (third x) (car (cdr (cdr x))))

(define (fourth x) (car (cdr (cdr (cdr x)))))

(define (rest x) (cdr x))

(define (sqr x) (d* x x))

(define (map-n f)
 (lambda (n)
  (letrec ((loop (lambda (i) (if (d= i n) '() (cons (f i) (loop (d+ i 1)))))))
   (loop 0))))

(define (reduce f i)
 (lambda (l) (if (null? l) i (f (car l) ((reduce f i) (cdr l))))))

(define (map-reduce g i f l)
 (if (null? l) i (g (f (first l)) (map-reduce g i f (rest l)))))

(define (remove-if p l)
 (cond ((null? l) '())
       ((p (first l)) (remove-if p (rest l)))
       (else (cons (first l) (remove-if p (rest l))))))

(define (v+ u v) (map d+ u v))

(define (v- u v) (map d- u v))

(define (k*v k v) (map (lambda (x) (d* k x)) v))

(define (magnitude-squared x) ((reduce d+ 0.0) (map sqr x)))

(define (magnitude x) (dsqrt (magnitude-squared x)))

(define (distance-squared u v) (magnitude-squared (v- v u)))

(define (distance u v) (dsqrt (distance-squared u v)))

(define (gradient-ascent-F f x0 n eta)
 (if (dzero? n)
     (list x0 (f x0) ((gradient-F f) x0))
     (gradient-ascent-F
      f
      (map (lambda (xi gi) (d+ xi (d* eta gi))) x0 ((gradient-F f) x0))
      (d- n 1)
      eta)))

(define (gradient-ascent-R f x0 n eta)
 (if (dzero? n)
     (list x0 (f x0) ((gradient-R f) x0))
     (gradient-ascent-R
      f
      (map (lambda (xi gi) (d+ xi (d* eta gi))) x0 ((gradient-R f) x0))
      (d- n 1)
      eta)))

(define (multivariate-argmin-F f x)
 (let ((g (gradient-F f)))
  (letrec ((loop
	    (lambda (x fx gx eta i)
	     (cond ((d<= (magnitude gx) 1e-5) x)
		   ((d= i 10) (loop x fx gx (d* 2.0 eta) 0))
		   (else
		    (let ((x-prime (v- x (k*v eta gx))))
		     (if (d<= (distance x x-prime) 1e-5)
			 x
			 (let ((fx-prime (f x-prime)))
			  (if (d< fx-prime fx)
			      (loop x-prime fx-prime (g x-prime) eta (d+ i 1))
			      (loop x fx gx (d/ eta 2.0) 0))))))))))
   (loop x (f x) (g x) 1e-5 0))))

(define (multivariate-argmax-F f x)
 (multivariate-argmin-F (lambda (x) (d- 0.0 (f x))) x))

(define (multivariate-max-F f x) (f (multivariate-argmax-F f x)))

(define (multivariate-argmin-R f x)
 (let ((g (gradient-R f)))
  (letrec ((loop
	    (lambda (x fx gx eta i)
	     (cond ((d<= (magnitude gx) 1e-5) x)
		   ((d= i 10) (loop x fx gx (d* 2.0 eta) 0))
		   (else
		    (let ((x-prime (v- x (k*v eta gx))))
		     (if (d<= (distance x x-prime) 1e-5)
			 x
			 (let ((fx-prime (f x-prime)))
			  (if (d< fx-prime fx)
			      (loop x-prime fx-prime (g x-prime) eta (d+ i 1))
			      (loop x fx gx (d/ eta 2.0) 0))))))))))
   (loop x (f x) (g x) 1e-5 0))))

(define (multivariate-argmax-R f x)
 (multivariate-argmin-R (lambda (x) (d- 0.0 (f x))) x))

(define (multivariate-max-R f x) (f (multivariate-argmax-R f x)))
