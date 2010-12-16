(module probabilistic-prolog-F-bigloo (include "common-bigloo.sc"))

(define (make-constant symbol) (list 0 symbol))

(define (constant? thing) (d= (first thing) 0))

(define (make-variable symbol) (list 1 symbol))

(define (variable? thing) (d= (first thing) 1))

(define (variable-symbol thing) (second thing))

(define (make-compound-term functor terms) (list 2 functor terms))

(define (compound-term? thing) (d= (first thing) 2))

(define (compound-term-functor compound-term) (second compound-term))

(define (compound-term-terms compound-term) (third compound-term))

(define (make-clause p term terms) (list 4 p term terms))

(define (clause? thing) (d= (first thing) 4))

(define (clause-p clause) (second clause))

(define (clause-term clause) (third clause))

(define (clause-terms clause) (fourth clause))

(define (make-p) 0)

(define (make-q) 1)

(define (make-x) 2)

(define (make-binding variable value) (list variable value))

(define (binding-variable binding) (first binding))

(define (binding-value binding) (second binding))

(define (make-double p substitution) (list p substitution))

(define (double-p double) (first double))

(define (double-substitution double) (second double))

(define (binds? substitution variable)
 (and (not (null? substitution))
      (or (equal? variable (binding-variable (first substitution)))
	  (binds? (rest substitution) variable))))

(define (lookup-value variable substitution)
 (if (equal? variable (binding-variable (first substitution)))
     (binding-value (first substitution))
     (lookup-value variable (rest substitution))))

(define (apply-substitution substitution thing)
 (let loop ((thing thing))
  (cond ((clause? thing)
	 (make-clause (clause-p thing)
		      (loop (clause-term thing))
		      (map loop (clause-terms thing))))
	((compound-term? thing)
	 (make-compound-term (compound-term-functor thing)
			     (map loop (compound-term-terms thing))))
	((and (variable? thing) (binds? substitution thing))
	 (lookup-value thing substitution))
	(else thing))))

(define (member? variable set)
 (and (not (null? set))
      (or (equal? variable (first set)) (member? variable (rest set)))))

(define (union set1 set2)
 (if (or (null? set1) (member? (first set1) set2))
     set2
     (cons (first set1) (union (rest set1) set2))))

(define (variables-in thing)
 (cond ((clause? thing)
	(map-reduce union
		    (variables-in (clause-term thing))
		    variables-in
		    (clause-terms thing)))
       ((compound-term? thing)
	(map-reduce union '() variables-in (compound-term-terms thing)))
       ((variable? thing) (list thing))
       (else '())))

(define (occurs? variable term) (member? variable (variables-in term)))

(define (unify term1 term2)
 (cond
  ((compound-term? term1)
   (cond
    ((compound-term? term2)
     (if (equal? (compound-term-functor term1)
		 (compound-term-functor term2))
	 (let loop ((terms1 (compound-term-terms term1))
		    (terms2 (compound-term-terms term2))
		    (substitution '()))
	  (if (null? terms1)
	      (if (null? terms2)
		  substitution
		  #f)
	      (if (null? terms2)
		  #f
		  (let ((substitution1
			 (unify
			  (apply-substitution substitution (first terms1))
			  (apply-substitution substitution (first terms2)))))
		   (if (boolean? substitution1)
		       #f
		       (loop (rest terms1)
			     (rest terms2)
			     (append substitution1 substitution)))))))
	 #f))
    ((variable? term2)
     (if (occurs? term2 term1) #f (list (make-binding term2 term1))))
    (else #f)))
  ((variable? term1)
   (cond ((compound-term? term2)
	  (if (occurs? term1 term2) #f (list (make-binding term1 term2))))
	 ((variable? term2) (list (make-binding term1 term2)))
	 (else (list (make-binding term1 term2)))))
  (else (cond ((compound-term? term2) #f)
	      ((variable? term2) (list (make-binding term2 term1)))
	      (else (if (equal? term1 term2) '() #f))))))

(define (map-indexed f l)
 (let loop ((l l) (i 0))
  (if (null? l) '() (cons (f (first l) i) (loop (rest l) (d+ i 1))))))

(define (alpha-rename clause offset)
 (apply-substitution
  (map-indexed
   (lambda (variable i) (make-binding variable (make-variable (d+ offset i))))
   (variables-in clause))
  clause))

(define (proof-distribution term clauses)
 (let ((offset
	(d+ (map-reduce
	     max
	     0
	     variable-symbol
	     (map-reduce union (variables-in term) variables-in clauses))
	    1)))
  (map-reduce
   append
   '()
   (lambda (clause)
    (let ((clause (alpha-rename clause offset)))
     (let loop ((p (clause-p clause))
		(substitution (unify term (clause-term clause)))
		(terms (clause-terms clause)))
      (if (boolean? substitution)
	  '()
	  (if (null? terms)
	      (list (make-double p substitution))
	      (map-reduce
	       append
	       '()
	       (lambda (double)
		(loop (d* p (double-p double))
		      (append substitution (double-substitution double))
		      (rest terms)))
	       (proof-distribution
		(apply-substitution substitution (first terms)) clauses)))))))
   clauses)))

(define (likelihood substitution-distribution)
 (map-reduce d+ 0.0 double-p substitution-distribution))

(define (example)
 (gradient-ascent-F
  (lambda (p)
   (let ((clauses
	  (list
	   (make-clause (list-ref p 0)
			(make-compound-term (make-p) (list (make-constant 0)))
			'())
	   (make-clause
	    (d- 1.0 (list-ref p 0))
	    (make-compound-term (make-p) (list (make-variable (make-x))))
	    (list (make-compound-term
		   (make-q) (list (make-variable (make-x))))))
	   (make-clause (list-ref p 1)
			(make-compound-term (make-q) (list (make-constant 1)))
			'())
	   (make-clause (d- 1.0 (list-ref p 1))
			(make-compound-term (make-q) (list (make-constant 2)))
			'()))))
    (map-reduce
     d*
     1.0
     (lambda (observation)
      (likelihood
       (proof-distribution
	(make-compound-term (make-p) (list (make-constant observation)))
	clauses)))
     '(0 1 2 2))))
  '(0.5 0.5)
  1000.0
  0.1))

(define (run)
 (let loop ((i 10.0) (result (list 0.0 0.0)))
  (if (dzero? i)
      result
      (let ((p (first (example))))
       (loop (d- i 1)
	     (list (write-real (list-ref p 0))
		   (write-real (list-ref p 1))))))))

(run)
