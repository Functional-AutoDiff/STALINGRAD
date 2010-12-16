(define (make-constant-expression value) (list 0 value))

(define (constant-expression? expression) (d= (first expression) 0))

(define (constant-expression-value expression) (second expression))

(define (make-variable-access-expression variable) (list 1 variable))

(define (variable-access-expression? expression) (d= (first expression) 1))

(define (variable-access-expression-variable expression) (second expression))

(define (make-lambda-expression variable body) (list 2 variable body))

(define (lambda-expression? expression) (d= (first expression) 2))

(define (lambda-expression-variable expression) (second expression))

(define (lambda-expression-body expression) (third expression))

(define (make-application callee argument) (list 3 callee argument))

(define (application-callee expression) (second expression))

(define (application-argument expression) (third expression))

(define (make-ignore) 0)

(define (make-if-procedure) 1)

(define (make-x0) 2)

(define (make-x1) 3)

(define (make-binding variable value) (list variable value))

(define (binding-variable binding) (first binding))

(define (binding-value binding) (second binding))

(define (make-triple p environment value) (list p environment value))

(define (triple-p triple) (first triple))

(define (triple-environment triple) (second triple))

(define (triple-value triple) (third triple))

(define (binds? environment variable)
 (and (not (null? environment))
      (or (equal? variable (binding-variable (first environment)))
	  (binds? (rest environment) variable))))

(define (lookup-value variable environment)
 (if (equal? variable (binding-variable (first environment)))
     (binding-value (first environment))
     (lookup-value variable (rest environment))))

(define (merge-environments environment1 environment2)
 (if (null? environment1)
     environment2
     (let ((environment (merge-environments (rest environment1) environment2)))
      (if (boolean? environment)
	  #f
	  (if (binds? environment (binding-variable (first environment1)))
	      (if (equal? (lookup-value
			   (binding-variable (first environment1))
			   environment)
			  (binding-value (first environment1)))
		  environment
		  #f)
	      (cons (first environment1) environment))))))

(define (singleton-tagged-distribution value)
 (list (make-triple 1.0 '() value)))

(define (boolean-distribution p variable)
 (list (make-triple (- 1.0 p) (list (make-binding variable #f)) #f)
       (make-triple p (list (make-binding variable #t)) #t)))

(define (normalize-tagged-distribution tagged-distribution)
 (let ((n (let loop ((tagged-distribution tagged-distribution))
	   (if (null? tagged-distribution)
	       0.0
	       (+ (triple-p (first tagged-distribution))
		  (loop (rest tagged-distribution)))))))
  (map (lambda (triple)
	(make-triple (/ (triple-p triple) n)
		     (triple-environment triple)
		     (triple-value triple)))
       tagged-distribution)))

(define (map-tagged-distribution f tagged-distribution)
 (normalize-tagged-distribution
  (let loop ((tagged-distribution tagged-distribution))
   (if (null? tagged-distribution)
       '()
       (append
	(remove-if
	 (lambda (triple) (boolean? (triple-environment triple)))
	 (map (lambda (triple)
	       (make-triple (* (triple-p (first tagged-distribution))
			       (triple-p triple))
			    (merge-environments
			     (triple-environment (first tagged-distribution))
			     (triple-environment triple))
			    (triple-value triple)))
	      (f (triple-value (first tagged-distribution)))))
	(loop (rest tagged-distribution)))))))

(define (evaluate expression environment)
 (cond
  ((constant-expression? expression)
   (singleton-tagged-distribution (constant-expression-value expression)))
  ((variable-access-expression? expression)
   (lookup-value (variable-access-expression-variable expression) environment))
  ((lambda-expression? expression)
   (singleton-tagged-distribution
    (lambda (tagged-distribution)
     (evaluate (lambda-expression-body expression)
	       (cons (make-binding (lambda-expression-variable expression)
				   tagged-distribution)
		     environment)))))
  (else (let ((tagged-distribution
	       (evaluate (application-argument expression) environment)))
	 (map-tagged-distribution
	  (lambda (value) (value tagged-distribution))
	  (evaluate (application-callee expression) environment))))))

(define (likelihood value tagged-distribution)
 (if (null? tagged-distribution)
     0.0
     (+ (if (equal? value (triple-value (first tagged-distribution)))
	    (triple-p (first tagged-distribution))
	    0.0)
	(likelihood value (rest tagged-distribution)))))

(define (make-if antecedent consequent alternate)
 (make-application
  (make-application
   (make-application
    (make-variable-access-expression (make-if-procedure)) antecedent)
   (make-lambda-expression (make-ignore) consequent))
  (make-lambda-expression (make-ignore) alternate)))

(define (example)
 (gradient-ascent-F
  (lambda (p)
   (let ((tagged-distribution
	  (evaluate
	   (make-if (make-variable-access-expression (make-x0))
		    (make-constant-expression 0)
		    (make-if (make-variable-access-expression (make-x1))
			     (make-constant-expression 1)
			     (make-constant-expression 2)))
	   (list (make-binding
		  (make-x0) (boolean-distribution (list-ref p 0) (make-x0)))
		 (make-binding
		  (make-x1) (boolean-distribution (list-ref p 1) (make-x1)))
		 (make-binding
		  (make-if-procedure)
		  (singleton-tagged-distribution
		   (lambda (x)
		    (singleton-tagged-distribution
		     (lambda (y)
		      (singleton-tagged-distribution
		       (lambda (z)
			(map-tagged-distribution
			 (lambda (xe)
			  (map-tagged-distribution
			   (lambda (ye)
			    (map-tagged-distribution
			     (lambda (ze) (if xe (ye #f) (ze #f))) z))
			   y))
			 x))))))))))))
    (map-reduce
     *
     1.0
     (lambda (observation) (likelihood observation tagged-distribution))
     '(0 1 2 2))))
  '(0.5 0.5)
  1000.0
  0.1))

(define (run)
 (let loop ((i 10.0) (result (list 0.0 0.0)))
  (if (dzero? i)
      result
      (let ((p (first (example))))
       (loop (- i 1)
	     (list (write-real (list-ref p 0))
		   (write-real (list-ref p 1))))))))
