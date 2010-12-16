(module particle-FR-bigloo (include "common-bigloo.sc"))

(define (naive-euler w)
 (let* ((charges (list (list 10.0 (d- 10.0 w)) (list 10.0 0.0)))
	(x-initial (list 0.0 8.0))
	(xdot-initial (list 0.75 0.0))
	(delta-t 1e-1)
	(p (lambda (x)
	    ((reduce d+ 0.0)
	     (map (lambda (c) (d/ 1.0 (distance x c))) charges)))))
  (letrec ((loop (lambda (x xdot)
		  (let* ((xddot (k*v -1.0 ((gradient-R p) x)))
			 (x-new (v+ x (k*v delta-t xdot))))
		   (if (dpositive? (list-ref x-new 1))
		       (loop x-new (v+ xdot (k*v delta-t xddot)))
		       (let* ((delta-t-f (d/ (d- 0.0 (list-ref x 1))
					     (list-ref xdot 1)))
			      (x-t-f (v+ x (k*v delta-t-f xdot))))
			(sqr (list-ref x-t-f 0))))))))
   (loop x-initial xdot-initial))))

(define (run)
 (write-real (let* ((w0 0.0)
		    (w*-list
		     (multivariate-argmin-F
		      (lambda (w-list) (naive-euler (car w-list))) (list w0))))
	      (car w*-list))))

(run)
