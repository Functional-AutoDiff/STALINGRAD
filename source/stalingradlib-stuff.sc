(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004 and 2005 Purdue University. All rights reserved.

;;; This program is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU General Public License
;;; as published by the Free Software Foundation; either version 2
;;; of the License, or (at your option) any later version.

;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.

;;; You should have received a copy of the GNU General Public License
;;; along with this program; if not, write to the Free Software
;;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

;;; written by:
;;;    Jeffrey Mark Siskind
;;;    School of Electrical and Computer Engineering
;;;    Purdue University
;;;    465 Northwestern Avenue
;;;    Lafayette IN 47907-1285 USA
;;;    voice: +1 765/496-3197
;;;    FAX:   +1 765/494-6440
;;;    qobi@purdue.edu
;;;    ftp://ftp.ecn.purdue.edu/qobi
;;;    http://www.ece.purdue.edu/~qobi
;;;             and
;;;    Barak A. Pearlmutter
;;;    Hamilton Institute
;;;    National University of Ireland, Maynooth
;;;    Maynooth, Co. Kildare
;;;    Ireland
;;;    voice: +353 1 7086394
;;;    FAX: +353 1 7086269
;;;    barak@cs.nuim.ie
;;;    http://www-bcl.cs.nuim.ie/~bap

;;; needs work
;;;  1. forward-{primal,adjoint,conjoin,j} and reverse-{zero,plus,primal,j}
;;;     should be lazy.
;;;  2. does making reverse-plus lazy eliminate the need to special case for
;;;     generic zeros
;;;  3. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  4. We removed -wizard because macro expansion required (ignore) and
;;;     (consvar x1 x2). Someday we need to put it back in.
;;;  5. For now, we don't optimize away null adjoints.

;;; Church Numerals
;;;  1. pair? will return #t and procedure? will return #f on some procedures
;;;     that are compatible with pairs.
;;;  2. You can take the car and cdr of some procedures that are compatible
;;;     with pairs and not get an error.
;;;  3. Primitives that expect tuples will accept procedures that are
;;;     compatible with pairs and not give an error.
;;;  4. Procedures that are compatible with pairs will print as pairs rather
;;;     than as procedures.
;;;  5. You can call a pair.
;;;  6. forward-{primal,adjoint,conjoin,j} and reverse-{zero,plus,primal,j}

(include "QobiScheme.sch")
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. unary -
;;;  2. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  3. chars, ports, eof object, symbols, continuations, strings, vectors
;;;  4. enforce don't shadow: car, cdr, cons-procedure, if-procedure, and ys

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete parameter
;;;  x: concrete variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: value
;;;  d: definition
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

;;; Structures

(define-structure variable-access-expression variable index)

(define-structure lambda-expression
 tags
 base-free-variables
 free-variables
 free-variable-indices			;vector
 variable
 body)

(define-structure application callee argument)

(define-structure let*-expression variables expressions body)

(define-structure letrec-expression
 tags
 bodies-base-free-variables
 bodies-free-variables
 bodies-free-variable-indices		;vector
 body-free-variables
 body-free-variable-indices		;vector
 procedure-variables
 argument-variables
 bodies
 body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure name procedure forward reverse meter)

(define-structure closure
 tags
 base-variables
 variables
 values					;vector
 variable
 body)

(define-structure recursive-closure
 tags
 base-variables
 variables
 values					;vector
 procedure-variables			;vector
 argument-variables			;vector
 bodies					;vector
 index)

(define-structure forward-value primal adjoint)

(define-structure reverse-value primal)

(define-structure forward-cache-entry primal? primal adjoint? adjoint forward)

(define-structure reverse-cache-entry primal reverse)

(define-structure fake base-free-variables)

;;; Variables

(define *gensym* 0)

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *forward-cache* '())

(define *reverse-cache* '())

;;; Parameters

(define *include-path* '())

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-nicely?* #f)

(define *unabbreviate-transformed?* #t)

(define *unabbreviate-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *letrec-as-y?* #f)

(define *anal?* #t)

(define *x* #f)

(define *memoized?* #f)

;;; Procedures

(define (check-base x xs)
 (when (and (or (not x)
		(not (list? (variable-base x)))
		(not (eq? (first (variable-base x)) 'sensitivity)))
	    (some (lambda (x)
		   (and (symbol? x)
			(not (eq? (string->symbol (symbol->string x)) x))
			(char=? (string-ref (symbol->string x) 0) #\H)))
		  xs))
  (fuck-up)))

;;; VLAD datastructures

(define (vlad-forward? v)
 (or (forward-value? v)
     (and (closure? v)
	  (not (null? (closure-tags v)))
	  (eq? (first (closure-tags v)) 'forward))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'forward))))

(define (vlad-reverse? v)
 (or (reverse-value? v)
     (and (closure? v)
	  (not (null? (closure-tags v)))
	  (eq? (first (closure-tags v)) 'reverse))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'reverse))))

(define (vlad-pair? v tags)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (if (null? tags)
     (and (closure? v)
	  (not (vlad-forward? v))
	  (not (vlad-reverse? v))
	  (= (length (closure-variables v)) 2)
	  (let*-expression? (closure-body v))
	  (= (length (let*-expression-variables (closure-body v))) 2)
	  (application? (first (let*-expression-expressions (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee
	    (first (let*-expression-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee
	     (first (let*-expression-expressions (closure-body v)))))
	   (closure-variable v))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument
	    (first (let*-expression-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-argument
	     (first (let*-expression-expressions (closure-body v)))))
	   (first (closure-variables v)))
	  (application? (second (let*-expression-expressions (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee
	    (second (let*-expression-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee
	     (second (let*-expression-expressions (closure-body v)))))
	   (first (let*-expression-variables (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument
	    (second (let*-expression-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-argument
	     (second (let*-expression-expressions (closure-body v)))))
	   (second (closure-variables v)))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression? (let*-expression-body (closure-body v)))
	  (variable=?
	   (variable-access-expression-variable
	    (let*-expression-body (closure-body v)))
	   (second (let*-expression-variables (closure-body v)))))
     (case (first tags)
      ((forward) (vlad-pair? (forward-primal v) (rest tags)))
      ((reverse) (vlad-pair? (reverse-primal v) (rest tags)))
      (else (fuck-up)))))

(define (vlad-car v tags)
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take vlad-car of a non-pair" v))
	(vector-ref (closure-values v) 0))
       (else
	(case (first tags)
	 ((forward)
	  (forward-conjoin (vlad-car (forward-primal v) (rest tags))
			   (vlad-car (forward-adjoint v) (rest tags))))
	 ((reverse) (reverse-j (vlad-car (reverse-primal v) (rest tags))))
	 (else (fuck-up))))))

(define (vlad-cdr v tags)
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take vlad-cdr of a non-pair" v))
	(vector-ref (closure-values v) 1))
       (else
	(case (first tags)
	 ((forward)
	  (forward-conjoin (vlad-cdr (forward-primal v) (rest tags))
			   (vlad-cdr (forward-adjoint v) (rest tags))))
	 ((reverse) (reverse-j (vlad-cdr (reverse-primal v) (rest tags))))
	 (else (fuck-up))))))

(define (vlad-cons v1 v2)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (create-closure
  '()
  '(a d)
  '(a d)
  (vector v1 v2)
  'm
  (index 'm
	 '(a d)
	 (new-let*-expression
	  '(x1 x2)
	  (list (new-application (new-variable-access-expression 'm)
				 (new-variable-access-expression 'a))
		(new-application (new-variable-access-expression 'x1)
				 (new-variable-access-expression 'd)))
	  (new-variable-access-expression 'x2)))))

(define (cons*ify xs tags)
 (if (null? tags)
     (let loop ((xs xs))
      (cond ((null? xs) '())
	    ((null? (rest xs)) (first xs))
	    (else (vlad-cons (first xs) (loop (rest xs))))))
     (case (first tags)
      ((forward)
       (forward-conjoin (cons*ify (map forward-primal xs) (rest tags))
			(cons*ify (map forward-adjoint xs) (rest tags))))
      ((reverse) (reverse-j (cons*ify (map reverse-primal xs) (rest tags))))
      (else (fuck-up)))))

(define (vlad-procedure? v)
 (and (or (primitive-procedure? v) (closure? v) (recursive-closure? v))
      (not (vlad-pair? v '()))))

(define (vlad-equal? v1 v2)
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (and (boolean? v1) (boolean? v2) (eq? v1 v2))
     (and (real? v1) (real? v2) (= v1 v2))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (closure? v1)
	  (closure? v2)
	  (equal? (closure-tags v1) (closure-tags v2))
	  (= (vector-length (closure-values v1))
	     (vector-length (closure-values v2)))
	  (alpha-equivalent?
	   (closure-body v1)
	   (closure-body v2)
	   (cons (closure-variable v1) (closure-variables v1))
	   (cons (closure-variable v2) (closure-variables v2)))
	  (every-vector vlad-equal? (closure-values v1) (closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (equal? (recursive-closure-tags v1) (recursive-closure-tags v2))
	  (= (vector-length (recursive-closure-bodies v1))
	     (vector-length (recursive-closure-bodies v2)))
	  (= (recursive-closure-index v1) (recursive-closure-index v2))
	  (= (vector-length (recursive-closure-values v1))
	     (vector-length (recursive-closure-values v2)))
	  (every-vector
	   (lambda (x1 x2 e1 e2)
	    (alpha-equivalent?
	     e1
	     e2
	     (cons x1
		   (append
		    (vector->list (recursive-closure-procedure-variables v1))
		    (recursive-closure-variables v1)))
	     (cons x2
		   (append
		    (vector->list (recursive-closure-procedure-variables v2))
		    (recursive-closure-variables v2)))))
	   (recursive-closure-argument-variables v1)
	   (recursive-closure-argument-variables v2)
	   (recursive-closure-bodies v1)
	   (recursive-closure-bodies v2))
	  (every-vector vlad-equal?
			(recursive-closure-values v1)
			(recursive-closure-values v2)))
     (and (forward-value? v1)
	  (forward-value? v2)
	  (vlad-equal? (forward-value-primal v1) (forward-value-primal v2))
	  (vlad-equal? (forward-value-adjoint v1) (forward-value-adjoint v2)))
     (and (reverse-value? v1)
	  (reverse-value? v2)
	  (vlad-equal? (reverse-value-primal v1) (reverse-value-primal v2)))))

(define (forwardize v)
 (unless (and (closure? v)
	      (null? (closure-tags v))
	      (every-vector (lambda (v)
			     (and (not (vlad-forward? v))
				  (not (vlad-reverse? v))))
			    (closure-values v))
	      (let*-expression? (closure-body v))
	      (not (some lambda-expression?
			 (let*-expression-expressions (closure-body v)))))
  (fuck-up))
 (create-closure '(forward)
		 '()
		 (closure-variables v)
		 (closure-values v)
		 (closure-variable v)
		 (closure-body v)))

(define (reversize v)
 (unless (and (recursive-closure? v)
	      (null? (recursive-closure-tags v))
	      (every-vector (lambda (v)
			     (and (not (vlad-forward? v))
				  (not (vlad-reverse? v))))
			    (recursive-closure-values v))
	      (every-vector
	       (lambda (e)
		(and (let*-expression? e)
		     (every (lambda (e)
			     (or (not (lambda-expression? e))
				 (and
				  (let*-expression? (lambda-expression-body e))
				  (not (some lambda-expression?
					     (let*-expression-expressions
					      (lambda-expression-body e)))))))
			    (let*-expression-expressions e))))
	       (recursive-closure-bodies v)))
  (fuck-up))
 (create-recursive-closure
  '(reverse)
  '()
  (recursive-closure-variables v)
  (recursive-closure-values v)
  (recursive-closure-procedure-variables v)
  (recursive-closure-argument-variables v)
  (map-vector
   (lambda (e)
    (new-let*-expression
     (let*-expression-variables e)
     (map (lambda (e)
	   (if (lambda-expression? e)
	       ;; This is so we don't have to index it again.
	       (make-lambda-expression
		(lambda-expression-tags e)
		(set-differencep variable=?
				 (lambda-expression-base-free-variables e)
				 (recursive-closure-variables v))
		(lambda-expression-free-variables e)
		(lambda-expression-free-variable-indices e)
		(lambda-expression-variable e)
		(lambda-expression-body e))
	       e))
	  (let*-expression-expressions e))
     (let*-expression-body e)))
   (recursive-closure-bodies v))
  (recursive-closure-index v)))

(define (dereference v) v)

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (hensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "H~a" (number->padded-string-of-length gensym 9)))))

(define (variable? x)
 (or (and (symbol? x)
	  (not (memq x '(quote
			 lambda
			 letrec
			 let
			 let*
			 if
			 cons
			 cons*
			 list
			 cond
			 else
			 and
			 or
			 ignore
			 consvar
			 alpha
			 anf
			 perturbation
			 forward
			 sensitivity
			 backpropagator
			 reverse))))
     (and (list? x)
	  (= (length x) 1)
	  (eq? (first x) 'ignore))
     (and (list? x)
	  (= (length x) 3)
	  (eq? (first x) 'consvar)
	  (variable? (second x))
	  (variable? (third x)))
     (and (list? x)
	  (= (length x) 3)
	  (eq? (first x) 'alpha)
	  (variable? (second x))
	  (integer? (third x))
	  (exact? (third x))
	  (not (negative? (third x))))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'anf)
	  (integer? (second x))
	  (exact? (second x))
	  (not (negative? (second x))))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'perturbation)
	  (variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'forward)
	  (variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'sensitivity)
	  (variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'backpropagator)
	  (variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'reverse)
	  (variable? (second x)))))

(define (variable-anf-max x)
 (cond ((symbol? x) 0)
       ((list? x)
	(case (first x)
	 ((ignore) 0)
	 ((consvar) (max (variable-anf-max (second x))
			 (variable-anf-max (third x))))
	 ((alpha) (variable-anf-max (second x)))
	 ((anf) (second x))
	 ((perturbation forward sensitivity backpropagator reverse)
	  (variable-anf-max (second x)))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (variable=? x1 x2) (equal? x1 x2))

(define (variable-base x)
 (if (and (list? x) (eq? (first x) 'alpha)) (variable-base (second x)) x))

(define (variable-alpha x)
 (if (and (list? x) (eq? (first x) 'alpha))
     (cons (third x) (variable-alpha (second x)))
     '()))

(define (base-variable<? x1 x2)
 (if (symbol? x1)
     (if (symbol? x2)
	 (string<? (symbol->string x1) (symbol->string x2))
	 #t)
     (if (symbol? x2)
	 #f
	 (if (eq? (first x1) (first x2))
	     (case (first x1)
	      ((ignore) #f)
	      ((consvar) (or (variable<? (second x1) (second x2))
			     (and (variable=? (second x1) (second x2))
				  (variable<? (third x1) (third x2)))))
	      ((anf) (< (second x1) (second x2)))
	      ((perturbation forward sensitivity backpropagator reverse)
	       (variable<? (second x1) (second x2)))
	      (else (fuck-up)))
	     (not (not (memq (first x2)
			     (memq (first x1)
				   '(ignore
				     consvar
				     anf
				     perturbation
				     forward
				     sensitivity
				     backpropagator
				     reverse)))))))))

(define (variable<? x1 x2)
 (or (base-variable<? (variable-base x1) (variable-base x2))
     (and (variable=? (variable-base x1) (variable-base x2))
	  ((lexicographically<? < =)
	   (reverse (variable-alpha x1)) (reverse (variable-alpha x2))))))

(define (parameter->consvar p)
 (cond ((variable? p) p)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3) (fuck-up))
	  `(consvar ,(parameter->consvar (second p))
		    ,(parameter->consvar (third p))))
	 ((cons*)
	  (case (length (rest p))
	   ((0) '(ignore))
	   ((1) (parameter->consvar (second p)))
	   (else `(consvar ,(parameter->consvar (second p))
			   ,(parameter->consvar `(cons* ,@(rest (rest p))))))))
	 ((list)
	  (if (null? (rest p))
	      '(ignore)
	      `(consvar ,(parameter->consvar (second p))
			,(parameter->consvar `(list ,@(rest (rest p)))))))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (duplicates? xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (member (first xs) (rest xs)) (duplicates? (rest xs)))))

(define (sort-variables xs) (sort xs variable<? identity))

(define (sensitivityify x) `(sensitivity ,x))

(define (backpropagatorify x) `(backpropagator ,x))

(define (sensitivity-access x)
 (new-variable-access-expression (sensitivityify x)))

;;; Expression constructors

(define (new-variable-access-expression x)
 (make-variable-access-expression x #f))

(define (transformed-lambda-expression tags new? xs x e)
 (let ((xs1 (removep variable=? x (free-variables e))))
  (unless (or new? (fake? xs) (subsetp? variable=? xs xs1)) (fuck-up))
  (unless (or new? (fake? xs)) (check-base x (if new? xs1 xs)))
  (make-lambda-expression tags (if new? xs1 xs) xs1 #f x e)))

(define (new-lambda-expression x e)
 (transformed-lambda-expression '() #t '() x e))

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))
     (and (let*-expression? e)
	  (or (some contains-letrec? (let*-expression-expressions e))
	      (contains-letrec? (let*-expression-body e))))))

(define (new-application e1 e2)
 (if (and (lambda-expression? e1)
	  (not (contains-letrec? (lambda-expression-body e1)))
	  (not (contains-letrec? e2)))
     (if (let*-expression? (lambda-expression-body e1))
	 ;; needs work: This belongs in new-let*-expression.
	 (new-let*-expression
	  (cons (lambda-expression-variable e1)
		(let*-expression-variables (lambda-expression-body e1)))
	  (cons e2 (let*-expression-expressions (lambda-expression-body e1)))
	  (let*-expression-body (lambda-expression-body e1)))
	 ;; call-to-let conversion
	 ;; needs work: This belongs in expression->anf.
	 ;; needs work: This fails to type-check the argument.
	 (new-let*-expression (list (lambda-expression-variable e1))
			      (list e2)
			      (lambda-expression-body e1)))
     (make-application e1 e2)))

(define (create-application bs tags e . es)
 (new-application e (make-cons* bs tags es)))

(define (new-let*-expression xs es e)
 ;; This is a stronger check than:
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 (when (or (contains-letrec? e)
	   (and (not (null? es)) (some contains-letrec? (rest es))))
  (fuck-up))
 (if (null? xs) e (make-let*-expression xs es e)))

(define (create-let* bs e)
 (new-let*-expression
  (map variable-binding-variable bs) (map variable-binding-expression bs) e))

(define (transformed-letrec-expression tags new? xs3 xs1 xs2 es e)
 (let ((xs3a (letrec-free-variables xs1 xs2 es)))
  (when (and (not new?) (not (subsetp? variable=? xs3 xs3a))) (fuck-up))
  (check-base #f (if new? xs3a xs3))
  (if (null? xs1)
      e
      (make-letrec-expression
       tags
       (if new? xs3a xs3)
       xs3a
       #f
       (sort-variables
	(set-differencep
	 variable=?
	 (union-variables
	  (reduce
	   union-variables
	   (map (lambda (x e) (removep variable=? x (free-variables e)))
		xs2
		es)
	   '())
	  (free-variables e))
	 xs1))
       #f
       xs1
       xs2
       es
       e))))

(define (new-letrec-expression xs1 xs2 es e)
 (transformed-letrec-expression '() #t '() xs1 xs2 es e))

(define (reference-graph xs1 xs2 es e)
 ;; needs work: Should have structure instead of list.
 (list
  (map (lambda (x1 x2 e)
	(list
	 x1
	 (intersectionp variable=?
			xs1
			(free-variables (new-lambda-expression x2 e)))))
       xs1
       xs2
       es)
  (intersectionp variable=? xs1 (free-variables e))))

(define (union-variables xs1 xs2) (unionp variable=? xs1 xs2))

(define (transitive-closure arms)
 ;; needs work: Should have structure instead of list.
 (let loop ((arms arms))
  (let ((new-arms
	 (map
	  (lambda (arm)
	   (list (first arm)
		 (union-variables
		  (second arm)
		  (reduce union-variables
			  (map (lambda (target)
				(second (assp variable=? target arms)))
			       (second arm))
			  '()))))
	  arms)))
   (if (every (lambda (arm new-arm)
	       (set-equalq? (second arm) (second new-arm)))
	      arms
	      new-arms)
       arms
       (loop new-arms)))))

(define (strongly-connected-components arms transitive-arms)
 ;; needs work: Should have structure instead of list.
 (equivalence-classesp
  (lambda (x1 x2)
   (and (memp variable=? x1 (second (assp variable=? x2 transitive-arms)))
	(memp variable=? x2 (second (assp variable=? x1 transitive-arms)))))
  (map first arms)))

(define (lightweight-letrec-conversion xs1 xs2 es e)
 ;; needs work: Should have structure instead of list.
 (let* ((reference-graph (reference-graph xs1 xs2 es e))
	(arms (first reference-graph))
	(xs (second reference-graph))
	(transitive-arms (transitive-closure arms)))
  (map
   (lambda (this)
    (list
     this
     (or (not (null? (rest this)))
	 (not (not (memp variable=?
			 (first this)
			 (second (assp variable=? (first this) arms))))))))
   (topological-sort
    ;; component2 calls component1
    (lambda (component1 component2)
     (some (lambda (x2)
	    (some (lambda (x1)
		   (memp variable=?
			 x1
			 (second (assp variable=? x2 transitive-arms))))
		  component1))
	   component2))
    (remove-if-not
     (lambda (component)
      (some
       (lambda (x1)
	(some (lambda (x2)
	       (or (variable=? x2 x1)
		   (memp variable=?
			 x2
			 (second (assp variable=? x1 transitive-arms)))))
	      component))
       xs))
     (strongly-connected-components arms transitive-arms))))))

(define (new-lightweight-letrec-expression xs1 xs2 es e)
 (let loop ((clusters (lightweight-letrec-conversion xs1 xs2 es e)))
  (if (null? clusters)
      e
      (let ((cluster (first clusters)))
       (if (second cluster)
	   (new-letrec-expression
	    (first cluster)
	    (map (lambda (x) (list-ref xs2 (positionp variable=? x xs1)))
		 (first cluster))
	    (map (lambda (x) (list-ref es (positionp variable=? x xs1)))
		 (first cluster))
	    (loop (rest clusters)))
	   (let ((x (first (first cluster))))
	    (new-application
	     (new-lambda-expression x (loop (rest clusters)))
	     (new-lambda-expression
	      (list-ref xs2 (positionp variable=? x xs1))
	      (list-ref es (positionp variable=? x xs1))))))))))

;;; Other constructors

(define (create-closure tags xs1 xs2 vs x e)
 (unless (subsetp? variable=? xs1 xs2) (fuck-up))
 (check-base x xs1)
 (make-closure tags xs1 xs2 vs x e))

(define (create-recursive-closure tags xs1 xs2 vs xs3 xs4 es i)
 (unless (subsetp? variable=? xs1 xs2) (fuck-up))
 (check-base #f xs1)
 (make-recursive-closure tags xs1 xs2 vs xs3 xs4 es i))

;;; Search path

(define (search-include-path-without-extension pathname)
 (cond ((can-open-file-for-input? pathname) pathname)
       ((and (>= (string-length pathname) 1)
	     (char=? (string-ref pathname 0) #\/))
	(panic (format #f "Cannot find: ~a" pathname)))
       (else (let loop ((include-path *include-path*))
	      (cond ((null? include-path)
		     (panic (format #f "Cannot find: ~a" pathname)))
		    ((can-open-file-for-input?
		      (string-append (first include-path) "/" pathname))
		     (string-append (first include-path) "/" pathname))
		    (else (loop (rest include-path))))))))

(define (search-include-path pathname)
 (search-include-path-without-extension (default-extension pathname "vlad")))

(define (read-source pathname)
 (let ((pathname (default-extension pathname "vlad")))
  (unless (can-open-file-for-input? pathname)
   (panic (format #f "Cannot find: ~a" pathname)))
  (call-with-input-file pathname
   (lambda (input-port)
    (let loop ((es '()))
     (let ((e (read input-port)))
      (cond
       ((eof-object? e) (reverse es))
       ((and (list? e)
	     (= (length e) 2)
	     (eq? (first e) 'include)
	     (string? (second e)))
	(loop
	 (append (reverse (read-source (search-include-path (second e)))) es)))
       (else (loop (cons e es))))))))))

;;; Standard prelude

(define (standard-prelude e)
 `(let* ((car (lambda (p) (p (lambda (a) (lambda (d) a)))))
	 (cdr (lambda (p) (p (lambda (a) (lambda (d) d)))))
	 (cons-procedure (lambda (a) (lambda (d) (lambda (m) ((m a) d)))))
	 ,@(if *letrec-as-y?*
	       '((ys (let* ((y (lambda (f)
				((lambda (g) (lambda (x) ((f (g g)) x)))
				 (lambda (g) (lambda (x) ((f (g g)) x))))))
			    (map
			     (lambda (f)
			      (y (lambda (map)
				  (lambda (l)
				   (if (null? l)
				       '()
				       (cons (f (car l)) (map (cdr l))))))))))
		      (y (lambda (ys)
			  (lambda (fs)
			   ((map (lambda (f) (lambda (x) ((f (ys fs)) x))))
			    fs)))))))
	       '()))
   ,e))

;;; Definitions

(define (definens? e)
 (or (variable? e) (and (list? e) (not (null? e)) (definens? (first e)))))

(define (definition? d)
 (and
  (list? d) (= (length d) 3) (eq? (first d) 'define) (definens? (second d))))

(define (definens-name e) (if (variable? e) e (definens-name (first e))))

(define (definens-expression e1 e2)
 (if (variable? e1)
     e2
     (definens-expression (first e1) `(lambda ,(rest e1) ,e2))))

(define (expand-definitions ds e)
 (for-each (lambda (d)
	    (unless (definition? d)
	     (panic (format #t "Invalid definition: ~s" d))))
	   ds)
 (standard-prelude
  `(letrec ,(map (lambda (d)
		  `(,(definens-name (second d))
		    ,(definens-expression (second d) (third d))))
		 ds)
    ,e)))

;;; Alpha conversion

(define (alphaify x xs)
 (if (or #t				;debugging
	 (memp variable=? x xs))
     `(alpha ,x
	     ,(+ (reduce max
			 (map (lambda (x1)
			       (if (and (list? x1)
					(eq? (first x1) 'alpha)
					(variable=? (second x1) x))
				   (third x1)
				   0))
			      xs)
			 0)
		 1))
     x))

(define (alpha-convert new? e xs)
 ;; needs work: Should have structure instead of list.
 ;; needs work: to make faster
 (second
  (let outer ((e e) (xs xs) (bs (map make-alpha-binding xs xs)))
   (cond
    ((variable-access-expression? e)
     (list xs
	   (new-variable-access-expression
	    (alpha-binding-variable2
	     (find-if (lambda (b)
		       (variable=? (alpha-binding-variable1 b)
				   (variable-access-expression-variable e)))
		      bs)))))
    ((lambda-expression? e)
     (let* ((x (alphaify (lambda-expression-variable e) xs))
	    (result (outer (lambda-expression-body e)
			   (cons x xs)
			   (cons (make-alpha-binding
				  (lambda-expression-variable e) x)
				 bs))))
      (list (first result)
	    (transformed-lambda-expression
	     (lambda-expression-tags e)
	     new?
	     (if (fake? (lambda-expression-base-free-variables e))
		 (make-fake
		  (map (lambda (x)
			(alpha-binding-variable2
			 (find-if (lambda (b)
				   (variable=? x (alpha-binding-variable1 b)))
				  bs)))
		       (fake-base-free-variables
			(lambda-expression-base-free-variables e))))
		 (map (lambda (x)
		       (alpha-binding-variable2
			(find-if (lambda (b)
				  (variable=? x (alpha-binding-variable1 b)))
				 bs)))
		      (lambda-expression-base-free-variables e)))
	     x
	     (second result)))))
    ((application? e)
     (let* ((result1 (outer (application-callee e) xs bs))
	    (result2 (outer (application-argument e) (first result1) bs)))
      (list (first result2)
	    (new-application (second result1) (second result2)))))
    ((let*-expression? e)
     (let inner ((xs1 (let*-expression-variables e))
		 (es1 (let*-expression-expressions e))
		 (xs2 '())
		 (es2 '())
		 (xs xs)
		 (bs bs))
      (if (null? es1)
	  (let ((result (outer (let*-expression-body e) xs bs)))
	   (list (first result)
		 (new-let*-expression
		  (reverse xs2) (reverse es2) (second result))))
	  (let* ((result (outer (first es1) xs bs))
		 (x (alphaify (first xs1) (first result))))
	   (inner (rest xs1)
		  (rest es1)
		  (cons x xs2)
		  (cons (second result) es2)
		  (cons x (first result))
		  (cons (make-alpha-binding (first xs1) x) bs))))))
    ((letrec-expression? e)
     (let loop ((xs1 (letrec-expression-procedure-variables e))
		(xs3 '())
		(xs xs))
      (if (null? xs1)
	  (let ((bs (append (map make-alpha-binding
				 (letrec-expression-procedure-variables e)
				 (reverse xs3))
			    bs)))
	   (let inner ((xs2 (letrec-expression-argument-variables e))
		       (xs4 '())
		       (es (letrec-expression-bodies e))
		       (es1 '())
		       (xs xs))
	    (if (null? es)
		(let ((result (outer (letrec-expression-body e) xs bs)))
		 (list
		  (first result)
		  (transformed-letrec-expression
		   (letrec-expression-tags e)
		   new?
		   (map (lambda (x)
			 (alpha-binding-variable2
			  (find-if
			   (lambda (b)
			    (variable=? x (alpha-binding-variable1 b)))
			   bs)))
			(letrec-expression-bodies-base-free-variables e))
		   (reverse xs3)
		   (reverse xs4)
		   (reverse es1)
		   (second result))))
		(let* ((x (alphaify (first xs2) xs))
		       (result
			(outer
			 (first es)
			 (cons x xs)
			 (cons (make-alpha-binding (first xs2) x) bs))))
		 (inner (rest xs2)
			(cons x xs4)
			(rest es)
			(cons (second result) es1)
			(first result))))))
	  (let ((x (alphaify (first xs1) xs)))
	   (loop (rest xs1) (cons x xs3) (cons x xs))))))
    (else (fuck-up))))))

(define (alpha-equivalent? e1 e2 xs1 xs2)
 (or
  (and (variable-access-expression? e1)
       (variable-access-expression? e2)
       (= (positionp variable=? (variable-access-expression-variable e1) xs1)
	  (positionp variable=? (variable-access-expression-variable e2) xs2)))
  (and (lambda-expression? e1)
       (lambda-expression? e2)
       (alpha-equivalent? (lambda-expression-body e1)
			  (lambda-expression-body e2)
			  (cons (lambda-expression-variable e1) xs1)
			  (cons (lambda-expression-variable e2) xs2)))
  (and (application? e1)
       (application? e2)
       (alpha-equivalent?
	(application-callee e1) (application-callee e2) xs1 xs2)
       (alpha-equivalent?
	(application-argument e1) (application-argument e2) xs1 xs2))
  (and (let*-expression? e1)
       (let*-expression? e2)
       (= (length (let*-expression-variables e1))
	  (length (let*-expression-variables e2)))
       (let loop ((xs1 xs1)
		  (xs2 xs2)
		  (xs3 (let*-expression-variables e1))
		  (xs4 (let*-expression-variables e2))
		  (es3 (let*-expression-expressions e1))
		  (es4 (let*-expression-expressions e2)))
	(if (null? xs3)
	    (alpha-equivalent?
	     (let*-expression-body e1) (let*-expression-body e2) xs1 xs2)
	    (and (alpha-equivalent? (first es3) (first es4) xs1 xs2)
		 (loop (cons (first xs3) xs1)
		       (cons (first xs4) xs2)
		       (rest xs3)
		       (rest xs4)
		       (rest es3)
		       (rest es4))))))
  (and (letrec-expression? e1)
       (letrec-expression? e2)
       (= (length (letrec-expression-procedure-variables e1))
	  (length (letrec-expression-procedure-variables e2)))
       (every
	(lambda (e3 e4 x3 x4)
	 (alpha-equivalent?
	  e3
	  e4
	  (cons x3 (append (letrec-expression-procedure-variables e1) xs1))
	  (cons
	   x4 (append (letrec-expression-procedure-variables e2) xs2))))
	(letrec-expression-bodies e1)
	(letrec-expression-bodies e2)
	(letrec-expression-argument-variables e1)
	(letrec-expression-argument-variables e2))
       (alpha-equivalent?
	(letrec-expression-body e1)
	(letrec-expression-body e2)
	(append (letrec-expression-procedure-variables e1) xs1)
	(append (letrec-expression-procedure-variables e2) xs2)))))

;;; Free variables

(define (letrec-free-variables xs1 xs2 es)
 (sort-variables
  (set-differencep
   variable=?
   (reduce
    union-variables
    (map (lambda (x e) (removep variable=? x (free-variables e))) xs2 es)
    '())
   xs1)))

(define (free-variables e)
 (define (free-variables e)
  (cond ((variable-access-expression? e)
	 (list (variable-access-expression-variable e)))
	((lambda-expression? e) (lambda-expression-free-variables e))
	((application? e)
	 (union-variables (free-variables (application-callee e))
			  (free-variables (application-argument e))))
	((let*-expression? e)
	 (let loop ((xs (let*-expression-variables e))
		    (es (let*-expression-expressions e))
		    (xs1 '()))
	  (if (null? es)
	      (set-differencep variable=?
			       (free-variables (let*-expression-body e)) xs1)
	      (union-variables
	       (set-differencep variable=? (free-variables (first es)) xs1)
	       (loop (rest xs)
		     (rest es)
		     (adjoinp variable=? (first xs) xs1))))))
	((letrec-expression? e) (letrec-expression-body-free-variables e))
	(else (fuck-up))))
 (sort-variables (free-variables e)))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (variable=? x-prime x) (memp variable=? x-prime xs)) (fuck-up))
  ;; The reverse is necessary because let*-expression doesn't prune unaccessed
  ;; variables.
  (if (memp variable=? x-prime xs)
      (- (length xs) (positionp variable=? x-prime (reverse xs)) 1)
      -1))
 (cond
  ((variable-access-expression? e)
   (make-variable-access-expression
    (variable-access-expression-variable e)
    (lookup (variable-access-expression-variable e))))
  ((lambda-expression? e)
   (make-lambda-expression
    (lambda-expression-tags e)
    (lambda-expression-base-free-variables e)
    (lambda-expression-free-variables e)
    (list->vector (map lookup (lambda-expression-free-variables e)))
    (lambda-expression-variable e)
    (index (lambda-expression-variable e)
	   (lambda-expression-free-variables e)
	   (lambda-expression-body e))))
  ((application? e)
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))))
  ((let*-expression? e)
   (let loop ((xs1 (let*-expression-variables e))
	      (es1 (let*-expression-expressions e))
	      (xs xs)
	      (es2 '()))
    (if (null? xs1)
	(new-let*-expression (let*-expression-variables e)
			     (reverse es2)
			     (index x xs (let*-expression-body e)))
	(loop (rest xs1)
	      (rest es1)
	      ;; needs work: This is not safe-for-space because we don't remove
	      ;;             unused elements of xs.
	      (append xs (list (first xs1)))
	      (cons (index x xs (first es1)) es2)))))
  ((letrec-expression? e)
   (make-letrec-expression
    (letrec-expression-tags e)
    (letrec-expression-bodies-base-free-variables e)
    (letrec-expression-bodies-free-variables e)
    (list->vector (map lookup (letrec-expression-bodies-free-variables e)))
    (letrec-expression-body-free-variables e)
    (list->vector (map lookup (letrec-expression-body-free-variables e)))
    (letrec-expression-procedure-variables e)
    (letrec-expression-argument-variables e)
    (let ((xs (append (letrec-expression-procedure-variables e)
		      (letrec-expression-bodies-free-variables e))))
     (map (lambda (x e) (index x xs e))
	  (letrec-expression-argument-variables e)
	  (letrec-expression-bodies e)))
    (index x
	   (append (letrec-expression-procedure-variables e)
		   (letrec-expression-body-free-variables e))
	   (letrec-expression-body e))))
  (else (fuck-up))))

;;; ANF conversion

(define (anf-result new? result)
 ;; needs work: Should have structure instead of list.
 (when (and (not (null? (fourth result)))
	    (not
	     (null?
	      (rest
	       (remove-duplicates
		(map (lambda (b)
		      (lambda-expression-tags (variable-binding-expression b)))
		     (fourth result)))))))
  (fuck-up))
 (unless (or new?
	     (null? (fourth result))
	     (null? (rest (remove-duplicatesp
			   (lambda (xs1 xs2)
			    (and (= (length xs1) (length xs2))
				 (every variable=? xs1 xs2)))
			   (map (lambda (b)
				 (fake-base-free-variables
				  (lambda-expression-base-free-variables
				   (variable-binding-expression b))))
				(fourth result))))))
  (fuck-up))
 (transformed-letrec-expression
  (if (null? (fourth result))
      '()
      (lambda-expression-tags
       (variable-binding-expression (first (fourth result)))))
  new?
  (if (or new? (null? (fourth result)))
      '()
      (fake-base-free-variables
       (lambda-expression-base-free-variables
	(variable-binding-expression (first (fourth result))))))
  (map variable-binding-variable (reverse (fourth result)))
  (map (lambda (b)
	(lambda-expression-variable (variable-binding-expression b)))
       (reverse (fourth result)))
  (map (lambda (b) (lambda-expression-body (variable-binding-expression b)))
       (reverse (fourth result)))
  (new-let*-expression
   (map variable-binding-variable (reverse (third result)))
   (map variable-binding-expression (reverse (third result)))
   (new-variable-access-expression (second result)))))

(define (anf-max e)
 (cond
  ((variable-access-expression? e)
   (variable-anf-max (variable-access-expression-variable e)))
  ((lambda-expression? e)
   (max (variable-anf-max (lambda-expression-variable e))
	(anf-max (lambda-expression-body e))))
  ((application? e)
   (max (anf-max (application-callee e)) (anf-max (application-argument e))))
  ((let*-expression? e)
   (max (reduce max (map variable-anf-max (let*-expression-variables e)) 0)
	(reduce max (map anf-max (let*-expression-expressions e)) 0)
	(anf-max (let*-expression-body e))))
  ((letrec-expression? e)
   (max
    (reduce
     max (map variable-anf-max (letrec-expression-procedure-variables e)) 0)
    (reduce
     max (map variable-anf-max (letrec-expression-argument-variables e)) 0)
    (reduce max (map anf-max (letrec-expression-bodies e)) 0)
    (anf-max (letrec-expression-body e))))
  (else (fuck-up))))

(define (anf-convert new? e)
 ;; The soundness of our method for ANF conversion relies on two things:
 ;;  1. E must be alpha converted.
 ;;     This allows letrecs to be merged.
 ;;     It also allows let*s in expressions of let*s to be merged.
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 ;; needs work: Should have structure instead of list.
 ;; needs work: to make faster
 (anf-result
  new?
  (let outer ((i (anf-max e)) (e e) (bs1 '()) (bs2 '()))
   (cond
    ((variable-access-expression? e)
     ;; result
     (list i (variable-access-expression-variable e) bs1 bs2))
    ((lambda-expression? e)
     (let* ((result (outer i (lambda-expression-body e) '() '()))
	    (i (+ (first result) 1))
	    (x `(anf ,i)))
      ;; result
      (list i
	    x
	    (cons (make-variable-binding
		   x
		   (transformed-lambda-expression
		    (lambda-expression-tags e)
		    new?
		    (lambda-expression-base-free-variables e)
		    (lambda-expression-variable e)
		    (anf-result new? result)))
		  bs1)
	    bs2)))
    ((application? e)
     (let* ((result1 (outer i (application-callee e) bs1 bs2))
	    (result2 (outer (first result1)
			    (application-argument e)
			    (third result1)
			    (fourth result1)))
	    (i (+ (first result2) 1))
	    (x `(anf ,i)))
      ;; result
      (list i
	    x
	    (cons (make-variable-binding
		   x
		   (new-application
		    (new-variable-access-expression (second result1))
		    (new-variable-access-expression (second result2))))
		  (third result2))
	    (fourth result2))))
    ((let*-expression? e)
     (let inner ((i i)
		 (xs (let*-expression-variables e))
		 (es (let*-expression-expressions e))
		 (bs1 bs1)
		 (bs2 bs2))
      (if (null? xs)
	  (outer i (let*-expression-body e) bs1 bs2)
	  (let ((result (outer i (first es) bs1 bs2)))
	   (inner
	    (first result)
	    (rest xs)
	    (rest es)
	    (cons (make-variable-binding
		   (first xs) (new-variable-access-expression (second result)))
		  (third result))
	    (fourth result))))))
    ((letrec-expression? e)
     (let inner ((i i)
		 (xs1 (letrec-expression-procedure-variables e))
		 (xs2 (letrec-expression-argument-variables e))
		 (es (letrec-expression-bodies e))
		 (bs2 bs2))
      (if (null? xs1)
	  (outer i (letrec-expression-body e) bs1 bs2)
	  (let ((result (outer i (first es) '() '())))
	   (inner (first result)
		  (rest xs1)
		  (rest xs2)
		  (rest es)
		  (cons (make-variable-binding
			 (first xs1)
			 (transformed-lambda-expression
			  (letrec-expression-tags e)
			  new?
			  (make-fake
			   (letrec-expression-bodies-base-free-variables e))
			  (first xs2)
			  (anf-result new? result)))
			bs2))))))
    (else (fuck-up))))))

(define (anf-letrec-tags e)
 (if (letrec-expression? e) (letrec-expression-tags e) 'error))

(define (anf-letrec-bodies-base-free-variables e)
 (if (letrec-expression? e)
     (letrec-expression-bodies-base-free-variables e)
     '()))

(define (anf-letrec-bodies-free-variables e)
 (if (letrec-expression? e) (letrec-expression-bodies-free-variables e) '()))

(define (anf-letrec-procedure-variables e)
 (if (letrec-expression? e) (letrec-expression-procedure-variables e) '()))

(define (anf-letrec-argument-variables e)
 (if (letrec-expression? e) (letrec-expression-argument-variables e) '()))

(define (anf-letrec-bodies e)
 (if (letrec-expression? e) (letrec-expression-bodies e) '()))

(define (anf-let*-variables e)
 (if (letrec-expression? e)
     (if (let*-expression? (letrec-expression-body e))
	 (let*-expression-variables (letrec-expression-body e))
	 '())
     (if (let*-expression? e) (let*-expression-variables e) '())))

(define (anf-let*-expressions e)
 (if (letrec-expression? e)
     (if (let*-expression? (letrec-expression-body e))
	 (let*-expression-expressions (letrec-expression-body e))
	 '())
     (if (let*-expression? e) (let*-expression-expressions e) '())))

(define (anf-variable e)
 (variable-access-expression-variable
  (if (letrec-expression? e)
      (if (let*-expression? (letrec-expression-body e))
	  (let*-expression-body (letrec-expression-body e))
	  (letrec-expression-body e))
      (if (let*-expression? e) (let*-expression-body e) e))))

;;; Copy propagation

(define (substitute x1 x2 e)
 ;; This is a special purpose substitute just for the kind of copy propagation
 ;; we do.
 (cond ((variable-access-expression? e)
	(if (variable=? (variable-access-expression-variable e) x2)
	    (new-variable-access-expression x1)
	    e))
       ;; We should never have to substitute a free variable.
       ((lambda-expression? e) e)
       ((application? e)
	(new-application (substitute x1 x2 (application-callee e))
			 (substitute x1 x2 (application-argument e))))
       ;; ANF should never have let*.
       ((let*-expression? e) (fuck-up))
       ;; ANF should never have letrec.
       ((letrec-expression? e) (fuck-up))
       (else (fuck-up))))

(define (copy-propagate new? e)
 ;; needs work: to make faster
 (let outer ((e e))
  (transformed-letrec-expression
   (anf-letrec-tags e)
   new?
   (anf-letrec-bodies-base-free-variables e)
   (anf-letrec-procedure-variables e)
   (anf-letrec-argument-variables e)
   (map outer (anf-letrec-bodies e))
   (let inner ((xs1 (anf-let*-variables e))
	       (es1 (anf-let*-expressions e))
	       (x (anf-variable e))
	       (xs2 '())
	       (es2 '()))
    (if (null? xs1)
	(new-let*-expression
	 (reverse xs2) (reverse es2) (new-variable-access-expression x))
	(let ((x1 (first xs1)) (e1 (first es1)))
	 (cond
	  ((variable-access-expression? e1)
	   ;; let xs2=es2;
	   ;;     x1=e1;
	   ;;     xs1=es1
	   ;; in e end
	   (cond
	    ((and
	      (memp variable=? (variable-access-expression-variable e1) xs2)
	      (not (some (lambda (e)
			  (and (lambda-expression? e)
			       (memp variable=?
				     (variable-access-expression-variable e1)
				     (free-variables e))))
			 (append es1 es2))))
	     ;; let xs2[e1|->x1]=es2[e1|->x1];
	     ;;     xs1[e1|->x1]=es1[e1|->x1]
	     ;; in e[e1|->x1] end
	     (inner (map (lambda (x)
			  (if (variable=?
			       x (variable-access-expression-variable e1))
			      x1
			      x))
			 (rest xs1))
		    (map (lambda (e)
			  (substitute
			   x1 (variable-access-expression-variable e1) e))
			 (rest es1))
		    (if (variable=?
			 x (variable-access-expression-variable e1))
			x1
			x)
		    (map (lambda (x)
			  (if (variable=?
			       x (variable-access-expression-variable e1))
			      x1
			      x))
			 xs2)
		    (map (lambda (e)
			  (substitute
			   x1 (variable-access-expression-variable e1) e))
			 es2)))
	    ((not (some (lambda (e)
			 (and (lambda-expression? e)
			      (memp variable=? x1 (free-variables e))))
			(append es1 es2)))
	     ;; let xs2[x1|->e1]=es2[x1|->e1];
	     ;;     xs1[x1|->e1]=es1[x1|->e1]
	     ;; in e[x1|->e1] end
	     (inner (map (lambda (x)
			  (if (variable=? x x1)
			      (variable-access-expression-variable e1)
			      x))
			 (rest xs1))
		    (map (lambda (e)
			  (substitute
			   (variable-access-expression-variable e1) x1 e))
			 (rest es1))
		    (if (variable=? x x1)
			(variable-access-expression-variable e1)
			x)
		    (map (lambda (x)
			  (if (variable=? x x1)
			      (variable-access-expression-variable e1)
			      x))
			 xs2)
		    (map (lambda (e)
			  (substitute
			   (variable-access-expression-variable e1) x1 e))
			 es2)))
	    (else
	     (inner (rest xs1) (rest es1) x (cons x1 xs2) (cons e1 es2)))))
	  ((lambda-expression? e1)
	   (inner (rest xs1)
		  (rest es1)
		  x
		  (cons x1 xs2)
		  (cons (transformed-lambda-expression
			 (lambda-expression-tags e1)
			 new?
			 (lambda-expression-base-free-variables e1)
			 (lambda-expression-variable e1)
			 (outer (lambda-expression-body e1)))
			es2)))
	  ((application? e1)
	   (inner (rest xs1) (rest es1) x (cons x1 xs2) (cons e1 es2)))
	  (else (fuck-up)))))))))

;;; Concrete->Abstract

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (internalize v)
 (cond ((null? v) v)
       ((boolean? v) v)
       ((real? v) v)
       ((pair? v) (vlad-cons (internalize (car v)) (internalize (cdr v))))
       (else (fuck-up))))

(define (macro-expand e)
 (case (first e)
  ((lambda)
   (unless (and (= (length e) 3) (list? (second e)))
    (panic (format #f "Invalid expression: ~s" e)))
   (case (length (second e))
    ((0) `(lambda ((cons* ,@(second e))) ,(third e)))
    ((1)
     (let ((p (first (second e))))
      (cond
       ((variable? p) e)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3)
	   (panic (format #f "Invalid parameter: ~s" p)))
	  (let ((x (parameter->consvar p)))
	   `(lambda (,x)
	     ;; needs work: to ensure that you don't shadow car and cdr
	     (let* ((,(second p) (car ,x)) (,(third p) (cdr ,x)))
	      ,(third e)))))
	 ((cons*)
	  (case (length (rest p))
	   ((0) `(lambda ((ignore)) ,(third e)))
	   ((1) `(lambda (,(second p)) ,(third e)))
	   (else `(lambda ((cons ,(second p) (cons* ,@(rest (rest p)))))
		   ,(third e)))))
	 ((list)
	  (if (null? (rest p))
	      `(lambda ((ignore)) ,(third e))
	      `(lambda ((cons ,(second p) (list ,@(rest (rest p)))))
		,(third e))))
	 (else (panic (format #f "Invalid parameter: ~s" p)))))
       (else (panic (format #f "Invalid parameter: ~s" p))))))
    (else `(lambda ((cons* ,@(second e))) ,(third e)))))
  ((letrec)
   (unless (and (= (length e) 3)
		(list? (second e))
		(every (lambda (b)
			(and (list? b) (= (length b) 2) (variable? (first b))))
		       (second e)))
    (panic (format #f "Invalid expression: ~s" e)))
   `(let (((list ,@(map first (second e)))
	   ;; needs work: to ensure that you don't shadow ys
	   (ys (list ,@(map (lambda (b)
			     `(lambda ((list ,@(map first (second e))))
			       ,(second b)))
			    (second e))))))
     ,(third e)))
  ((let) (unless (and (= (length e) 3)
		      (list? (second e))
		      (every (lambda (b) (and (list? b) (= (length b) 2)))
			     (second e)))
	  (panic (format #f "Invalid expression: ~s" e)))
	 `((lambda ,(map first (second e)) ,(third e))
	   ,@(map second (second e))))
  ((let*)
   (unless (and (= (length e) 3)
		(list? (second e))
		(every (lambda (b) (and (list? b) (= (length b) 2)))
		       (second e)))
    (panic (format #f "Invalid expression: ~s" e)))
   (case (length (second e))
    ((0) (third e))
    ((1) `(let ,(second e) ,(third e)))
    (else `(let (,(first (second e))) (let* ,(rest (second e)) ,(third e))))))
  ;; needs work: to ensure that you don't shadow if-procedure
  ((if)
   (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
   `((if-procedure
      ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e)))))
  ;; needs work: to ensure that you don't shadow cons-procedure
  ((cons)
   (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
   `((cons-procedure ,(second e)) ,(third e)))
  ((cons*) (case (length (rest e))
	    ((0) ''())
	    ((1) (second e))
	    (else `(cons ,(second e) (cons* ,@(rest (rest e)))))))
  ((list)
   (if (null? (rest e)) ''() `(cons ,(second e) (list ,@(rest (rest e))))))
  ;; We don't allow (cond ... (e) ...) or (cond ... (e1 => e2) ...).
  ((cond) (unless (and (>= (length e) 2)
		       (every (lambda (b) (and (list? b) (= (length b) 2)))
			      (rest e))
		       (eq? (first (last e)) 'else))
	   (panic (format #f "Invalid expression: ~s" e)))
	  (if (null? (rest (rest e)))
	      (second (second e))
	      `(if ,(first (second e))
		   ,(second (second e))
		   (cond ,@(rest (rest e))))))
  ((and) (case (length (rest e))
	  ((0) #t)
	  ((1) (second e))
	  (else `(if ,(second e) (and ,@(rest (rest e))) #f))))
  ((or) (case (length (rest e))
	 ((0) #f)
	 ((1) (second e))
	 (else (let ((x (gensym)))
		`(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e)))))))))
  (else (case (length (rest e))
	 ((0) `(,(first e) (cons* ,@(rest e))))
	 ((1) e)
	 (else `(,(first e) (cons* ,@(rest e))))))))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs *basis-constants*))
  (cond
   ((null? e) (panic (format #f "Invalid expression: ~s" e)))
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((variable? e)
    (unless (memp variable=? e xs)
     (panic (format #f "Unbound variable: ~s" e)))
    #f)
   ((list? e)
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (panic (format #f "Invalid expression: ~s" e)))
	      #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (if (variable? (first (second e)))
		;; We no longer check for duplicate variables.
		(loop (third e) (cons (first (second e)) xs))
		(loop (macro-expand e) xs)))
       (else (loop (macro-expand e) xs))))
     ((letrec)
      (cond (*letrec-as-y?* (loop (macro-expand e) xs))
	    (else (unless (and (= (length e) 3)
			       (list? (second e))
			       (every (lambda (b)
				       (and (list? b)
					    (= (length b) 2)
					    (variable? (first b))))
				      (second e)))
		   (panic (format #f "Invalid expression: ~s" e)))
		  (let ((xs0 (map first (second e))))
		   (when (duplicates? xs0)
		    (panic (format #f "Duplicate variables: ~s" e)))
		   (for-each (lambda (b)
			      (let ((e1 (macro-expand (second b))))
			       (unless (and (list? e1)
					    (= (length e1) 3)
					    (eq? (first e1) 'lambda))
				(panic (format #f "Invalid expression: ~s" e)))
			       (loop e1  (append xs0 xs))))
			     (second e))
		   (loop (third e) (append xs0 xs))))))
     ((let) (loop (macro-expand e) xs))
     ((let*) (loop (macro-expand e) xs))
     ((if) (loop (macro-expand e) xs))
     ((cons) (loop (macro-expand e) xs))
     ((cons*) (loop (macro-expand e) xs))
     ((list) (loop (macro-expand e) xs))
     ((cond) (loop (macro-expand e) xs))
     ((and) (loop (macro-expand e) xs))
     ((or) (loop (macro-expand e) xs))
     (else (case (length (rest e))
	    ((0) (loop (macro-expand e) xs))
	    ((1) (loop (first e) xs)
		 (loop (second e) xs))
	    (else (loop (macro-expand e) xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (coalesce-constants result)
 ;; needs work: Should have structure instead of list.
 (let ((bss (transitive-equivalence-classesp
	     (lambda (b1 b2)
	      (vlad-equal? (value-binding-value b1) (value-binding-value b2)))
	     (second result))))
  (define (rename x)
   (let ((bs (find-if
	      (lambda (bs)
	       (some (lambda (b) (variable=? (value-binding-variable b) x))
		     bs))
	      bss)))
    (if bs (value-binding-variable (first bs)) x)))
  (list
   (let loop ((e (first result)))
    (cond ((variable-access-expression? e)
	   (new-variable-access-expression
	    (rename (variable-access-expression-variable e))))
	  ((lambda-expression? e)
	   (new-lambda-expression
	    (lambda-expression-variable e)
	    (loop (lambda-expression-body e))))
	  ((application? e)
	   (new-application (loop (application-callee e))
			    (loop (application-argument e))))
	  ((let*-expression? e)
	   (new-let*-expression (let*-expression-variables e)
				(map loop (let*-expression-expressions e))
				(loop (let*-expression-body e))))
	  ((letrec-expression? e)
	   (new-letrec-expression
	    (letrec-expression-procedure-variables e)
	    (letrec-expression-argument-variables e)
	    (map loop (letrec-expression-bodies e))
	    (loop (letrec-expression-body e))))
	  (else (fuck-up))))
   (map first bss))))

(define (concrete->abstract-expression e)
 ;; needs work: Should have structure instead of list.
 (let* ((result
	 (let loop ((e e) (bs *variable-bindings*))
	  (cond
	   ((boolean? e) (loop `',e bs))
	   ((real? e) (loop `',e bs))
	   ((variable? e)
	    (list (variable-binding-expression
		   (find-if (lambda (b)
			     (variable=? (variable-binding-variable b) e))
			    bs))
		  '()))
	   ((list? e)
	    (case (first e)
	     ((quote)
	      (let ((x (gensym)))
	       (list (new-variable-access-expression x)
		     (list (make-value-binding x (internalize (second e)))))))
	     ((lambda)
	      (case (length (second e))
	       ((0) (loop (macro-expand e) bs))
	       ((1)
		(if (variable? (first (second e)))
		    (let* ((x (first (second e)))
			   (result
			    (loop (third e)
				  (cons (make-variable-binding
					 x (new-variable-access-expression x))
					bs))))
		     (list (new-lambda-expression x (first result))
			   (second result)))
		    (loop (macro-expand e) bs)))
	       (else (loop (macro-expand e) bs))))
	     ((letrec)
	      (if *letrec-as-y?*
		  (loop (macro-expand e) bs)
		  (let* ((bs (append
			      (map
			       (lambda (b)
				(make-variable-binding
				 (first b)
				 (new-variable-access-expression (first b))))
			       (second e))
			      bs))
			 (results
			  (map (lambda (b) (loop (macro-expand (second b)) bs))
			       (second e)))
			 (result (loop (third e) bs))
			 (xs1 (map first (second e)))
			 (xs2
			  (map (lambda (result)
				(lambda-expression-variable (first result)))
			       results))
			 (es (map (lambda (result)
				   (lambda-expression-body (first result)))
				  results))
			 (e (first result)))
		   (list (new-lightweight-letrec-expression xs1 xs2 es e)
			 (append (second result)
				 (reduce append (map second results) '()))))))
	     ((let) (loop (macro-expand e) bs))
	     ((let*) (loop (macro-expand e) bs))
	     ((if) (loop (macro-expand e) bs))
	     ((cons) (loop (macro-expand e) bs))
	     ((cons*) (loop (macro-expand e) bs))
	     ((list) (loop (macro-expand e) bs))
	     ((cond) (loop (macro-expand e) bs))
	     ((and) (loop (macro-expand e) bs))
	     ((or) (loop (macro-expand e) bs))
	     (else
	      (case (length (rest e))
	       ((0) (loop (macro-expand e) bs))
	       ((1) (let ((result1 (loop (first e) bs))
			  (result2 (loop (second e) bs)))
		     (list (new-application (first result1) (first result2))
			   (append (second result1) (second result2)))))
	       (else (loop (macro-expand e) bs))))))
	   (else (fuck-up)))))
	(e (first result))
	(xs (free-variables e))
	(bs (remove-if-not
	     (lambda (b) (memp variable=? (value-binding-variable b) xs))
	     (append *value-bindings* (second result))))
	(result (coalesce-constants (list e bs)))
	(xs (map value-binding-variable (second result))))
  (list
   (index #f xs (copy-propagate
		 #t (anf-convert #t (alpha-convert #t (first result) xs))))
   (map value-binding-value (second result)))))

;;; Forward-J

(define (forward-transform e)
 (cond ((variable-access-expression? e) e)
       ((lambda-expression? e)
	(transformed-lambda-expression
	 (cons 'forward (lambda-expression-tags e))
	 #f
	 (lambda-expression-base-free-variables e)
	 (lambda-expression-variable e)
	 (forward-transform (lambda-expression-body e))))
       ((application? e)
	(new-application (forward-transform (application-callee e))
			 (forward-transform (application-argument e))))
       ((let*-expression? e)
	(new-let*-expression
	 (let*-expression-variables e)
	 (map forward-transform (let*-expression-expressions e))
	 (forward-transform (let*-expression-body e))))
       ((letrec-expression? e)
	(transformed-letrec-expression
	 (cons 'forward (letrec-expression-tags e))
	 #f
	 (letrec-expression-bodies-base-free-variables e)
	 (letrec-expression-procedure-variables e)
	 (letrec-expression-argument-variables e)
	 (map forward-transform (letrec-expression-bodies e))
	 (forward-transform (letrec-expression-body e))))
       (else (fuck-up))))

(define (forward-transform-inverse e)
 (cond ((variable-access-expression? e) e)
       ((lambda-expression? e)
	(transformed-lambda-expression
	 (rest (lambda-expression-tags e))
	 #f
	 (lambda-expression-base-free-variables e)
	 (lambda-expression-variable e)
	 (forward-transform-inverse (lambda-expression-body e))))
       ((application? e)
	(new-application
	 (forward-transform-inverse (application-callee e))
	 (forward-transform-inverse (application-argument e))))
       ((let*-expression? e)
	(new-let*-expression
	 (let*-expression-variables e)
	 (map forward-transform-inverse (let*-expression-expressions e))
	 (forward-transform-inverse (let*-expression-body e))))
       ((letrec-expression? e)
	(transformed-letrec-expression
	 (rest (letrec-expression-tags e))
	 #f
	 (letrec-expression-bodies-base-free-variables e)
	 (letrec-expression-procedure-variables e)
	 (letrec-expression-argument-variables e)
	 (map forward-transform-inverse (letrec-expression-bodies e))
	 (forward-transform-inverse (letrec-expression-body e))))
       (else (fuck-up))))

(define (forward-primal x-forward)
 (let ((forward-cache-entry
	(find-if
	 (lambda (forward-cache-entry)
	  (vlad-equal?
	   (forward-cache-entry-forward forward-cache-entry) x-forward))
	 *forward-cache*)))
  (if (and forward-cache-entry
	   (forward-cache-entry-primal? forward-cache-entry))
      (forward-cache-entry-primal forward-cache-entry)
      (let* ((result
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take forward-primal of a non-forward value"
		 x-forward))
	       ((boolean? x-forward)
		(run-time-error
		 "Attempt to take forward-primal of a non-forward value"
		 x-forward))
	       ((real? x-forward)
		(run-time-error
		 "Attempt to take forward-primal of a non-forward value"
		 x-forward))
	       ((primitive-procedure? x-forward)
		(run-time-error
		 "Attempt to take forward-primal of a non-forward value"
		 x-forward))
	       ((closure? x-forward)
		(unless (and (not (null? (closure-tags x-forward)))
			     (eq? (first (closure-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take forward-primal of a non-forward value"
		  x-forward))
		(let ((b (find-if (lambda (b)
				   (vlad-equal? x-forward
						(primitive-procedure-forward
						 (value-binding-value b))))
				  *value-bindings*)))
		 (if b
		     (value-binding-value b)
		     (let* ((e (forward-transform-inverse
				(transformed-lambda-expression
				 (closure-tags x-forward)
				 #f
				 (closure-base-variables x-forward)
				 (closure-variable x-forward)
				 (closure-body x-forward))))
			    (x (lambda-expression-variable e))
			    (xs (lambda-expression-free-variables e)))
		      (create-closure
		       (lambda-expression-tags e)
		       (lambda-expression-base-free-variables e)
		       xs
		       ;; We don't do add/remove-slots here.
		       (map-vector forward-primal (closure-values x-forward))
		       x
		       (index x xs (lambda-expression-body e)))))))
	       ((recursive-closure? x-forward)
		(unless (and (not (null? (recursive-closure-tags x-forward)))
			     (eq? (first (recursive-closure-tags x-forward))
				  'forward))
		 (run-time-error
		  "Attempt to take forward-primal of a non-forward value"
		  x-forward))
		(let ((b (find-if (lambda (b)
				   (vlad-equal? x-forward
						(primitive-procedure-forward
						 (value-binding-value b))))
				  *value-bindings*)))
		 (if b
		     (value-binding-value b)
		     (let* ((es (vector->list
				 (map-vector
				  (lambda (x e)
				   (forward-transform-inverse
				    (transformed-lambda-expression
				     (recursive-closure-tags x-forward)
				     #f
				     (make-fake
				      (recursive-closure-base-variables
				       x-forward))
				     x
				     e)))
				  (recursive-closure-argument-variables
				   x-forward)
				  (recursive-closure-bodies x-forward))))
			    (xs (letrec-free-variables
				 (vector->list
				  (recursive-closure-procedure-variables
				   x-forward))
				 (map lambda-expression-variable es)
				 (map lambda-expression-body es))))
		      (create-recursive-closure
		       (rest (recursive-closure-tags x-forward))
		       ;; base
		       (recursive-closure-base-variables x-forward)
		       xs
		       ;; We don't do add/remove-slots here.
		       (map-vector forward-primal
				   (recursive-closure-values x-forward))
		       (recursive-closure-procedure-variables x-forward)
		       (list->vector (map lambda-expression-variable es))
		       (list->vector
			(map (lambda (e)
			      (index
			       (lambda-expression-variable e)
			       (append
				(vector->list
				 (recursive-closure-procedure-variables
				  x-forward))
				xs)
			       (lambda-expression-body e)))
			     es))
		       (recursive-closure-index x-forward))))))
	       ((forward-value? x-forward) (forward-value-primal x-forward))
	       ((reverse-value? x-forward)
		(run-time-error
		 "Attempt to take forward-primal of a non-forward value"
		 x-forward))
	       (else (fuck-up))))
	     (forward-cache-entry
	      (find-if (lambda (forward-cache-entry)
			(vlad-equal?
			 (forward-cache-entry-forward forward-cache-entry)
			 x-forward))
		       *forward-cache*)))
       (when *memoized?*
	(cond
	 (forward-cache-entry
	  (when (forward-cache-entry-primal? forward-cache-entry) (fuck-up))
	  (set-forward-cache-entry-primal?! forward-cache-entry #t)
	  (set-forward-cache-entry-primal! forward-cache-entry result))
	 (else (set! *forward-cache*
		     (cons (make-forward-cache-entry #t result #f #f x-forward)
			   *forward-cache*)))))
       result))))

(define (base-values xs1 xs2 vs2)
 (map (lambda (x1) (vector-ref vs2 (positionp variable=? x1 xs2))) xs1))

(define (forward-adjoint x-forward)
 (let ((forward-cache-entry
	(find-if
	 (lambda (forward-cache-entry)
	  (vlad-equal?
	   (forward-cache-entry-forward forward-cache-entry) x-forward))
	 *forward-cache*)))
  (if (and forward-cache-entry
	   (forward-cache-entry-adjoint? forward-cache-entry))
      (forward-cache-entry-adjoint forward-cache-entry)
      (let* ((result
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take forward-adjoint of a non-forward value"
		 x-forward))
	       ((boolean? x-forward)
		(run-time-error
		 "Attempt to take forward-adjoint of a non-forward value"
		 x-forward))
	       ((real? x-forward)
		(run-time-error
		 "Attempt to take forward-adjoint of a non-forward value"
		 x-forward))
	       ((primitive-procedure? x-forward)
		(run-time-error
		 "Attempt to take forward-adjoint of a non-forward value"
		 x-forward))
	       ((closure? x-forward)
		(unless (and (not (null? (closure-tags x-forward)))
			     (eq? (first (closure-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take forward-adjoint of a non-forward value"
		  x-forward))
		(if (some (lambda (b)
			   (vlad-equal? x-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
			  *value-bindings*)
		    '()
		    (cons*ify
		     (map forward-adjoint
			  (base-values (closure-base-variables x-forward)
				       (closure-variables x-forward)
				       (closure-values x-forward)))
		     (rest (closure-tags x-forward)))))
	       ((recursive-closure? x-forward)
		(unless (and (not (null? (recursive-closure-tags x-forward)))
			     (eq? (first (recursive-closure-tags x-forward))
				  'forward))
		 (run-time-error
		  "Attempt to take forward-adjoint of a non-forward value"
		  x-forward))
		(if (some (lambda (b)
			   (vlad-equal? x-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
			  *value-bindings*)
		    '()
		    (cons*ify
		     (map forward-adjoint
			  (base-values
			   (recursive-closure-base-variables x-forward)
			   (recursive-closure-variables x-forward)
			   (recursive-closure-values x-forward)))
		     (rest (recursive-closure-tags x-forward)))))
	       ((forward-value? x-forward) (forward-value-adjoint x-forward))
	       ((reverse-value? x-forward)
		(run-time-error
		 "Attempt to take forward-adjoint of a non-forward value"
		 x-forward))
	       (else (fuck-up))))
	     (forward-cache-entry
	      (find-if (lambda (forward-cache-entry)
			(vlad-equal?
			 (forward-cache-entry-forward forward-cache-entry)
			 x-forward))
		       *forward-cache*)))
       (when *memoized?*
	(cond
	 (forward-cache-entry
	  (when (forward-cache-entry-adjoint? forward-cache-entry) (fuck-up))
	  (set-forward-cache-entry-adjoint?! forward-cache-entry #t)
	  (set-forward-cache-entry-adjoint! forward-cache-entry result))
	 (else (set! *forward-cache*
		     (cons (make-forward-cache-entry #f #f #t result x-forward)
			   *forward-cache*)))))
       result))))

(define (forward-conjoin x x-perturbation)
 (define (tagged-null? tags x)
  (if (null? tags)
      (null? x)
      (case (first tags)
       ((forward) (and (forward-value? x)
		       (tagged-null? (rest tags) (forward-value-primal x))
		       (tagged-null? (rest tags) (forward-value-adjoint x))))
       ((reverse) (and (reverse-value? x)
		       (tagged-null? (rest tags) (reverse-value-primal x))))
       (else (fuck-up)))))
 (define (forward-conform*? xs x-perturbations tags)
  ;; XS is a list, X-PERTURBATIONS is a tuple.
  (or
   (and (null? xs) (tagged-null? tags x-perturbations))
   (and (not (null? xs))
	(null? (rest xs))
	(forward-conform? (first xs) x-perturbations))
   (and (not (null? xs))
	(not (null? (rest xs)))
	(vlad-pair? x-perturbations tags)
	(forward-conform? (first xs) (vlad-car x-perturbations tags))
	(forward-conform*? (rest xs) (vlad-cdr x-perturbations tags) tags))))
 (define (forward-conform? x x-perturbation)
  (or (and (null? x) (null? x-perturbation))
      (and (boolean? x) (null? x-perturbation))
      (and (real? x) (real? x-perturbation))
      (and (primitive-procedure? x) (null? x-perturbation))
      (and (closure? x)
	   (forward-conform*? (base-values (closure-base-variables x)
					   (closure-variables x)
					   (closure-values x))
			      x-perturbation
			      (closure-tags x)))
      (and (recursive-closure? x)
	   (forward-conform*? (base-values (recursive-closure-base-variables x)
					   (recursive-closure-variables x)
					   (recursive-closure-values x))
			      x-perturbation
			      (recursive-closure-tags x)))
      (and (forward-value? x)
	   (forward-value? x-perturbation)
	   (forward-conform? (forward-value-primal x)
			     (forward-value-primal x-perturbation))
	   (forward-conform? (forward-value-adjoint x)
			     (forward-value-adjoint x-perturbation)))
      (and (reverse-value? x)
	   (reverse-value? x-perturbation)
	   (forward-conform? (reverse-value-primal x)
			     (reverse-value-primal x-perturbation)))))
 (define (forward-conjoin* xs x-perturbations tags)
  ;; XS is a list, X-PERTURBATIONS is a tuple, the result is a list.
  (cond
   ((null? xs) '())
   ((null? (rest xs)) (list (forward-conjoin (first xs) x-perturbations)))
   (else
    (cons (forward-conjoin (first xs) (vlad-car x-perturbations tags))
	  (forward-conjoin* (rest xs) (vlad-cdr x-perturbations tags) tags)))))
 (define (forward-conjoin x x-perturbation)
  (cond
   ((null? x) (make-forward-value x x-perturbation))
   ((boolean? x) (make-forward-value x x-perturbation))
   ((real? x) (make-forward-value x x-perturbation))
   ((primitive-procedure? x)
    (unless (null? x-perturbation) (fuck-up))
    (primitive-procedure-forward x))
   ((closure? x)
    (let* ((e (forward-transform (transformed-lambda-expression
				  (closure-tags x)
				  #f
				  (closure-base-variables x)
				  (closure-variable x)
				  (closure-body x))))
	   (x1 (lambda-expression-variable e))
	   (xs (lambda-expression-free-variables e)))
     (create-closure
      (lambda-expression-tags e)
      (lambda-expression-base-free-variables e)
      xs
      ;; This should use a generalized add/remove-slots here.
      (list->vector
       (let ((vs (forward-conjoin* (base-values (closure-base-variables x)
						(closure-variables x)
						(closure-values x))
				   x-perturbation
				   (closure-tags x))))
	(map (lambda (x1 v)
	      (let ((i (positionp variable=? x1 (closure-base-variables x))))
	       (if i (list-ref vs i) (forward-j v))))
	     (closure-variables x)
	     (vector->list (closure-values x)))))
      x1
      (index x1 xs (lambda-expression-body e)))))
   ((recursive-closure? x)
    (let* ((es (vector->list
		(map-vector (lambda (x1 e)
			     (forward-transform
			      (transformed-lambda-expression
			       (recursive-closure-tags x)
			       #f
			       (make-fake (recursive-closure-base-variables x))
			       x1
			       e)))
			    (recursive-closure-argument-variables x)
			    (recursive-closure-bodies x))))
	   (xs (letrec-free-variables
		(vector->list (recursive-closure-procedure-variables x))
		(map lambda-expression-variable es)
		(map lambda-expression-body es))))
     (create-recursive-closure
      (cons 'forward (recursive-closure-tags x))
      ;; base
      (recursive-closure-base-variables x)
      xs
      ;; This should use a generalized add/remove-slots here.
      (list->vector
       (let ((vs (forward-conjoin*
		  (base-values (recursive-closure-base-variables x)
			       (recursive-closure-variables x)
			       (recursive-closure-values x))
		  x-perturbation
		  (recursive-closure-tags x))))
	(map (lambda (x1 v)
	      (let ((i (positionp
			variable=? x1 (recursive-closure-base-variables x))))
	       (if i (list-ref vs i) (forward-j v))))
	     (recursive-closure-variables x)
	     (vector->list (recursive-closure-values x)))))
      (recursive-closure-procedure-variables x)
      (list->vector (map lambda-expression-variable es))
      (list->vector
       (map (lambda (e)
	     (let ((x (lambda-expression-variable e))
		   (xs (append
			(vector->list
			 (recursive-closure-procedure-variables x))
			xs)))
	      (index x xs (lambda-expression-body e))))
	    es))
      (recursive-closure-index x))))
   ((forward-value? x) (make-forward-value x x-perturbation))
   ((reverse-value? x) (make-forward-value x x-perturbation))
   (else (fuck-up))))
 ;; needs work: to memoize inside recursion rather than outside
 (let ((forward-cache-entry
	(find-if
	 (lambda (forward-cache-entry)
	  (and (vlad-equal? (forward-cache-entry-primal forward-cache-entry) x)
	       (vlad-equal? (forward-cache-entry-adjoint forward-cache-entry)
			    x-perturbation)))
	 *forward-cache*)))
  (unless forward-cache-entry
   (set! forward-cache-entry
	 (make-forward-cache-entry
	  #t
	  x
	  #t
	  x-perturbation
	  (begin (when *anal?*
		  (unless (forward-conform? x x-perturbation)
		   (run-time-error
		    "The arguments to forward-conjoin are nonconformant"
		    x x-perturbation)))
		 (forward-conjoin x x-perturbation))))
   (when *memoized?*
    (set! *forward-cache* (cons forward-cache-entry *forward-cache*))))
  (forward-cache-entry-forward forward-cache-entry)))

(define (zero x)
 (cond
  ((null? x) '())
  ((boolean? x) '())
  ((real? x) 0)
  ((primitive-procedure? x) '())
  ((closure? x)
   (cons*ify (map zero
		  (base-values (closure-base-variables x)
			       (closure-variables x)
			       (closure-values x)))
	     (closure-tags x)))
  ((recursive-closure? x)
   (cons*ify (map zero
		  (base-values (recursive-closure-base-variables x)
			       (recursive-closure-variables x)
			       (recursive-closure-values x)))
	     (recursive-closure-tags x)))
  ((forward-value? x)
   (make-forward-value (zero (forward-value-primal x))
		       (zero (forward-value-adjoint x))))
  ((reverse-value? x) (make-reverse-value (zero (reverse-value-primal x))))
  (else (fuck-up))))

(define (forward-j x) (forward-conjoin x (zero x)))

;;; Reverse-J

(define (added-variable bs v)
 (new-variable-access-expression
  (alpha-binding-variable2
   (find-if (lambda (b) (variable=? v (alpha-binding-variable1 b))) bs))))

(define (make-forward-primal bs e)
 (new-application (added-variable bs 'forward-primal) e))

(define (make-forward-adjoint bs e)
 (new-application (added-variable bs 'forward-adjoint) e))

(define (make-forward-conjoin bs e1 e2)
 (create-application bs '() (added-variable bs 'forward-conjoin) e1 e2))

(define (make-forward-j bs e)
 (new-application (added-variable bs 'forward-j) e))

(define (make-reverse-zero bs e)
 (new-application (added-variable bs 'reverse-zero) e))

(define (make-reverse-plus bs e1 e2)
 (create-application bs '() (added-variable bs 'reverse-plus) e1 e2))

(define (make-reverse-primal bs e)
 (new-application (added-variable bs 'reverse-primal) e))

(define (make-reverse-j bs e)
 (new-application (added-variable bs 'reverse-j) e))

(define (tagify bs tags e)
 (let loop ((tags tags))
  (if (null? tags)
      e
      ((case (first tags)
	((forward) make-forward-j)
	((reverse) make-reverse-j)
	(else (fuck-up)))
       bs
       (loop (rest tags))))))

(define (make-car bs tags e)
 ;; We no longer do car-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'car) e)
     (case (first tags)
      ((forward)
       (make-forward-conjoin
	bs
	(make-car bs (rest tags) (make-forward-primal bs e))
	(make-car bs (rest tags) (make-forward-adjoint bs e))))
      ((reverse)
       (make-reverse-j
	bs (make-car bs (rest tags) (make-reverse-primal bs e))))
      (else (fuck-up)))))

(define (make-cdr bs tags e)
 ;; We no longer do cdr-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'cdr) e)
     (case (first tags)
      ((forward)
       (make-forward-conjoin
	bs
	(make-cdr bs (rest tags) (make-forward-primal bs e))
	(make-cdr bs (rest tags) (make-forward-adjoint bs e))))
      ((reverse)
       (make-reverse-j
	bs (make-cdr bs (rest tags) (make-reverse-primal bs e))))
      (else (fuck-up)))))

(define (make-cons bs tags e1 e2)
 (if (null? tags)
     (new-application
      (new-application (added-variable bs 'cons-procedure) e1) e2)
     (case (first tags)
      ((forward)
       (make-forward-conjoin bs
			     (make-cons bs
					(rest tags)
					(make-forward-primal bs e1)
					(make-forward-primal bs e2))
			     (make-cons bs
					(rest tags)
					(make-forward-adjoint bs e1)
					(make-forward-adjoint bs e2))))
      ((reverse)
       (make-reverse-j bs
		       (make-cons bs
				  (rest tags)
				  (make-reverse-primal bs e1)
				  (make-reverse-primal bs e2))))
      (else (fuck-up)))))

(define (make-cons* bs tags es)
 (cond ((null? es) (tagify bs tags (added-variable bs 'null)))
       ((null? (rest es)) (first es))
       (else (make-cons bs tags (first es) (make-cons* bs tags (rest es))))))

(define (make-cons*-bindings bs tags xs e)
 (cond
  ((null? xs) '())
  ((null? (rest xs)) (list (make-variable-binding (first xs) e)))
  (else
   (let ((x (parameter->consvar `(cons* ,@xs))))
    (cons
     (make-variable-binding x e)
     (let loop ((xs xs) (x x))
      (if (null? (rest (rest xs)))
	  (list (make-variable-binding
		 (first xs)
		 (make-car bs tags (new-variable-access-expression x)))
		(make-variable-binding
		 (second xs)
		 (make-cdr bs tags (new-variable-access-expression x))))
	  (cons (make-variable-binding
		 (first xs)
		 (make-car bs tags (new-variable-access-expression x)))
		(cons (make-variable-binding
		       (third x)
		       (make-cdr bs tags (new-variable-access-expression x)))
		      (loop (rest xs) (third x)))))))))))

(define (reverse-transform bs e gs zs us)
 (let* ((tags (lambda-expression-tags e))
	(x (lambda-expression-variable e))
	(e1 (lambda-expression-body e))
	(fs (anf-letrec-procedure-variables e1))
	(ws (anf-letrec-bodies-base-free-variables e1))
	(bs0
	 (reduce
	  append
	  (map
	   (lambda (t e)
	    (cond
	     ((variable-access-expression? e)
	      (let ((x1 (variable-access-expression-variable e)))
	       (if (or (variable=? x1 x)
		       (memp variable=? x1 (anf-let*-variables e1))
		       (memp variable=? x1 fs)
		       (memp variable=? x1 gs)
		       (memp variable=? x1 zs))
		   (list (make-variable-binding
			  (sensitivityify x1)
			  (make-reverse-plus
			   bs (sensitivity-access x1) (sensitivity-access t))))
		   '())))
	     ((lambda-expression? e)
	      (make-cons*-bindings
	       bs
	       (lambda-expression-tags e)
	       (map sensitivityify (lambda-expression-base-free-variables e))
	       (make-reverse-plus
		bs
		(make-cons* bs
			    (lambda-expression-tags e)
			    (map sensitivity-access
				 (lambda-expression-base-free-variables e)))
		(sensitivity-access t))))
	     ((application? e)
	      (let* ((x1 (variable-access-expression-variable
			  (application-callee e)))
		     (x1? (or (variable=? x1 x)
			      (memp variable=? x1 (anf-let*-variables e1))
			      (memp variable=? x1 fs)
			      (memp variable=? x1 gs)
			      (memp variable=? x1 zs)))
		     (x2 (variable-access-expression-variable
			  (application-argument e)))
		     (x2? (or (variable=? x2 x)
			      (memp variable=? x2 (anf-let*-variables e1))
			      (memp variable=? x2 fs)
			      (memp variable=? x2 gs)
			      (memp variable=? x2 zs))))
	       (reduce
		append
		(list
		 (if (or x1? x2?)
		     (list
		      (make-variable-binding
		       `(consvar ,(sensitivityify x1) ,(sensitivityify x2))
		       (new-application
			(new-variable-access-expression (backpropagatorify t))
			(sensitivity-access t))))
		     '())
		 (if x1?
		     (list (make-variable-binding
			    (sensitivityify x1)
			    (make-reverse-plus
			     bs
			     (sensitivity-access x1)
			     (make-car
			      bs
			      '()
			      (new-variable-access-expression
			       `(consvar ,(sensitivityify x1)
					 ,(sensitivityify x2)))))))
		     '())
		 (if x2?
		     (list (make-variable-binding
			    (sensitivityify x2)
			    (make-reverse-plus
			     bs
			     (sensitivity-access x2)
			     (make-cdr
			      bs
			      '()
			      (new-variable-access-expression
			       `(consvar ,(sensitivityify x1)
					 ,(sensitivityify x2)))))))
		     '()))
		'())))
	     (else (fuck-up))))
	   (reverse (anf-let*-variables e1))
	   (reverse (anf-let*-expressions e1)))
	  '()))
	(e2
	 (create-let*
	  (reduce
	   append
	   (map (lambda (x e)
		 (cond
		  ((variable-access-expression? e)
		   (list (make-variable-binding x e)))
		  ((lambda-expression? e)
		   (list
		    (make-variable-binding
		     x
		     (reverse-transform
		      bs e '() (lambda-expression-base-free-variables e) us))))
		  ((application? e)
		   (make-cons*-bindings
		    bs '() (list x (backpropagatorify x)) e))
		  (else (fuck-up))))
		(anf-let*-variables e1)
		(anf-let*-expressions e1))
	   '())
	  (make-cons
	   bs
	   '()
	   (new-variable-access-expression (anf-variable e1))
	   (let ((e4
		  (create-let*
		   `(,@(map
			(lambda (x)
			 (make-variable-binding
			  (sensitivityify x)
			  (make-reverse-zero
			   bs (new-variable-access-expression x))))
			(removep
			 variable=?
			 (anf-variable e1)
			 (cons x (append (anf-let*-variables e1) fs gs zs))))
		     ,@bs0
		     ,@(make-cons*-bindings
			bs
			tags
			(map sensitivityify ws)
			(let loop ((fs fs))
			 (if (null? fs)
			     (make-cons* bs tags (map sensitivity-access ws))
			     (make-reverse-plus
			      bs
			      (sensitivity-access (first fs))
			      (loop (rest fs)))))))
		   (make-cons
		    bs
		    '()
		    (let loop ((gs gs))
		     (if (null? gs)
			 (make-cons* bs tags (map sensitivity-access zs))
			 (make-reverse-plus
			  bs
			  (sensitivity-access (first gs)) (loop (rest gs)))))
		    (sensitivity-access x)))))
	    (transformed-lambda-expression
	     '()
	     #f
	     (set-differencep variable=?
			      (removep variable=?
				       (sensitivityify (anf-variable e1))
				       (free-variables e4))
			      us)
	     (sensitivityify (anf-variable e1))
	     e4))))))
  (transformed-lambda-expression
   (cons 'reverse tags)
   #f
   (lambda-expression-base-free-variables e)
   x
   (if (null? fs)
       e2
       (let ((es (map (lambda (x e3)
		       (reverse-transform
			bs
			(transformed-lambda-expression
			 (letrec-expression-tags e1)
			 #f
			 (make-fake
			  (letrec-expression-bodies-base-free-variables e1))
			 x
			 e3)
			fs
			ws
			us))
		      (letrec-expression-argument-variables e1)
		      (letrec-expression-bodies e1))))
	(transformed-letrec-expression
	 (lambda-expression-tags (first es))
	 #f
	 (letrec-expression-bodies-base-free-variables e1)
	 fs
	 (map lambda-expression-variable es)
	 (map lambda-expression-body es)
	 e2))))))

(define (partial-cons? e)
 ;; cons-procedure x0
 (and (application? e)
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-callee e))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-argument e))))

(define (partial-cons-argument e) (application-argument e))

(define (result-cons? x1 x2 x3 e1 e2 e3 e)
 ;; x1=cons-procedure xa
 ;; x2=(lambda ...)
 ;; x3=x1 x2
 ;; in x3 end
 ;; ----------------------------------------------------------------
 ;; in xa end
 (and (partial-cons? e1)
      (variable-access-expression? (partial-cons-argument e1))
      ;; We don't check that this lambda expression is the proper
      ;; backpropagator for the primal.
      (lambda-expression? e2)
      (application? e3)
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-callee e3))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-argument e3))
      (variable=?
       (variable-access-expression-variable (application-callee e3)) x1)
      (variable=?
       (variable-access-expression-variable (application-argument e3)) x2)
      ;; Technically not needed since in ANF.
      (variable-access-expression? e)
      (variable=? (variable-access-expression-variable e) x3)))

(define (cons-split? x1 x2 x3 e1 e2 e3)
 ;; x1=xa xb
 ;; x2=car x1
 ;; x3=cdr x1
 ;; --------------------------------------------
 ;; x2,x3=xa xb
 (and (application? e1)
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-callee e1))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-argument e1))
      (application? e2)
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-callee e2))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-argument e2))
      (variable=?
       (variable-access-expression-variable (application-argument e2)) x1)
      (application? e3)
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-callee e3))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (application-argument e3))
      (variable=?
       (variable-access-expression-variable (application-argument e3)) x1)))

(define (reverse-transform-inverse-internal e)
 (cond
  ((let*-expression? e)
   (let loop ((xs (let*-expression-variables e))
	      (es (let*-expression-expressions e))
	      (xs0 '())
	      (es0 '()))
    (cond
     ((null? xs) (fuck-up))
     ((and (= (length xs) 3)
	   (result-cons? (first xs) (second xs) (third xs)
			 (first es) (second es) (third es)
			 (let*-expression-body e)))
      (if (null? xs0)
	  (partial-cons-argument (first es))
	  (new-let*-expression
	   (reverse xs0) (reverse es0) (partial-cons-argument (first es)))))
     ((and (>= (length xs) 3)
	   (cons-split? (first xs) (second xs) (third xs)
			(first es) (second es) (third es)))
      (loop (rest (rest (rest xs)))
	    (rest (rest (rest es)))
	    (cons (second xs) xs0)
	    (cons (first es) es0)))
     ((lambda-expression? (first es))
      (loop (rest xs)
	    (rest es)
	    (cons (first xs) xs0)
	    (cons (if (null? (lambda-expression-tags (first es)))
		      ;; needs work: This happens for partial conses. I don't
		      ;;             understand why.
		      (first es)
		      (reverse-transform-inverse (first es)))
		  es0)))
     (else
      (loop
       (rest xs) (rest es) (cons (first xs) xs0) (cons (first es) es0))))))
  (else (fuck-up))))

(define (reverse-transform-inverse e)
 (transformed-lambda-expression
  (rest (lambda-expression-tags e))
  #f
  (lambda-expression-base-free-variables e)
  (lambda-expression-variable e)
  (let ((e (lambda-expression-body e)))
   (if (letrec-expression? e)
       (transformed-letrec-expression
	(rest (letrec-expression-tags e))
	#f
	(letrec-expression-bodies-base-free-variables e)
	(letrec-expression-procedure-variables e)
	(letrec-expression-argument-variables e)
	(map reverse-transform-inverse-internal (letrec-expression-bodies e))
	(reverse-transform-inverse-internal (letrec-expression-body e)))
       (reverse-transform-inverse-internal e)))))

(define (added-value x)
 (case x
  ;; These are magic names.
  ((null) '())
  ((car) (evaluate-in-top-level-environment 'car))
  ((cdr) (evaluate-in-top-level-environment 'cdr))
  ((cons-procedure) (evaluate-in-top-level-environment 'cons-procedure))
  (else (value-binding-value
	 (find-if (lambda (b) (variable=? (value-binding-variable b) x))
		  *value-bindings*)))))

(define (add/remove-slots f xs0 xs1 vs0 bs)
 (list->vector
  (map (lambda (x)
	(let ((i (positionp variable=? x xs0)))
	 (if i
	     (f (vector-ref vs0 i))
	     (added-value
	      (alpha-binding-variable1
	       (find-if (lambda (b) (variable=? (alpha-binding-variable2 b) x))
			bs))))))
       xs1)))

(define (reverse-zero x-reverse) (zero (reverse-primal x-reverse)))

(define (reverse-plus x1-sensitivity x2-sensitivity)
 (define (reverse-conform? x1-sensitivity x2-sensitivity)
  (or (and (vlad-forward? x1-sensitivity)
	   (vlad-forward? x2-sensitivity)
	   (reverse-conform? (forward-primal x1-sensitivity)
			     (forward-primal x2-sensitivity))
	   (reverse-conform? (forward-adjoint x1-sensitivity)
			     (forward-adjoint x2-sensitivity)))
      (and (vlad-reverse? x1-sensitivity)
	   (vlad-reverse? x2-sensitivity)
	   (reverse-conform? (reverse-primal x1-sensitivity)
			     (reverse-primal x2-sensitivity)))
      (and (null? x1-sensitivity) (null? x2-sensitivity))
      (and (real? x1-sensitivity) (real? x2-sensitivity))
      (and (vlad-pair? x1-sensitivity '())
	   (vlad-pair? x2-sensitivity '())
	   (reverse-conform? (vlad-car x1-sensitivity '())
			     (vlad-car x2-sensitivity '()))
	   (reverse-conform? (vlad-cdr x1-sensitivity '())
			     (vlad-cdr x2-sensitivity '())))))
 (define (reverse-plus x1-sensitivity x2-sensitivity)
  (cond
   ((vlad-forward? x1-sensitivity)
    (forward-conjoin (reverse-plus (forward-primal x1-sensitivity)
				   (forward-primal x2-sensitivity))
		     (reverse-plus (forward-adjoint x1-sensitivity)
				   (forward-adjoint x2-sensitivity))))
   ((vlad-reverse? x1-sensitivity)
    (reverse-j (reverse-plus (reverse-primal x1-sensitivity)
			     (reverse-primal x2-sensitivity))))
   ((null? x1-sensitivity) '())
   ((real? x1-sensitivity) (+ x1-sensitivity x2-sensitivity))
   (else (vlad-cons
	  (reverse-plus
	   (vlad-car x1-sensitivity '()) (vlad-car x2-sensitivity '()))
	  (reverse-plus
	   (vlad-cdr x1-sensitivity '()) (vlad-cdr x2-sensitivity '()))))))
 (when *anal?*
  (unless (reverse-conform? x1-sensitivity x2-sensitivity)
   (run-time-error "The arguments to reverse-plus are nonconformant"
		   x1-sensitivity x2-sensitivity)))
 (reverse-plus x1-sensitivity x2-sensitivity))

(define (reverse-primal x-reverse)
 (let ((reverse-cache-entry
	(find-if
	 (lambda (reverse-cache-entry)
	  (vlad-equal? (reverse-cache-entry-reverse reverse-cache-entry)
		       x-reverse))
	 *reverse-cache*)))
  (unless reverse-cache-entry
   (set! reverse-cache-entry
	 (make-reverse-cache-entry
	  (cond
	   ((null? x-reverse)
	    (run-time-error
	     "Attempt to take reverse-primal of a non-reverse value"
	     x-reverse))
	   ((boolean? x-reverse)
	    (run-time-error
	     "Attempt to take reverse-primal of a non-reverse value"
	     x-reverse))
	   ((real? x-reverse)
	    (run-time-error
	     "Attempt to take reverse-primal of a non-reverse value"
	     x-reverse))
	   ((primitive-procedure? x-reverse)
	    (run-time-error
	     "Attempt to take reverse-primal of a non-reverse value"
	     x-reverse))
	   ((closure? x-reverse)
	    (unless (and (not (null? (closure-tags x-reverse)))
			 (eq? (first (closure-tags x-reverse)) 'reverse))
	     (run-time-error
	      "Attempt to take reverse-primal of a non-reverse value"
	      x-reverse))
	    (let ((b (find-if
		      (lambda (b)
		       (vlad-equal?
			x-reverse
			(primitive-procedure-reverse (value-binding-value b))))
		      *value-bindings*)))
	     (if b
		 (value-binding-value b)
		 (let* ((e (reverse-transform-inverse
			    (transformed-lambda-expression
			     (closure-tags x-reverse)
			     #f
			     (closure-base-variables x-reverse)
			     (closure-variable x-reverse)
			     (closure-body x-reverse))))
			(x (lambda-expression-variable e))
			(xs (lambda-expression-free-variables e)))
		  (create-closure
		   (lambda-expression-tags e)
		   (lambda-expression-base-free-variables e)
		   xs
		   (add/remove-slots reverse-primal
				     (closure-variables x-reverse)
				     xs
				     (closure-values x-reverse)
				     '())
		   x
		   (index x
			  xs
			  (copy-propagate #f (lambda-expression-body e))))))))
	   ((recursive-closure? x-reverse)
	    (unless (and (not (null? (recursive-closure-tags x-reverse)))
			 (eq? (first (recursive-closure-tags x-reverse))
			      'reverse))
	     (run-time-error
	      "Attempt to take reverse-primal of a non-reverse value"
	      x-reverse))
	    (let ((b (find-if
		      (lambda (b)
		       (vlad-equal?
			x-reverse
			(primitive-procedure-reverse (value-binding-value b))))
		      *value-bindings*)))
	     (if b
		 (value-binding-value b)
		 (let* ((es (vector->list
			     (map-vector
			      (lambda (x e)
			       (reverse-transform-inverse
				(transformed-lambda-expression
				 (recursive-closure-tags x-reverse)
				 #f
				 (make-fake
				  (recursive-closure-base-variables x-reverse))
				 x
				 e)))
			      (recursive-closure-argument-variables x-reverse)
			      (recursive-closure-bodies x-reverse))))
			(xs
			 (letrec-free-variables
			  (vector->list
			   (recursive-closure-procedure-variables x-reverse))
			  (map lambda-expression-variable es)
			  (map lambda-expression-body es))))
		  (create-recursive-closure
		   (rest (recursive-closure-tags x-reverse))
		   ;; base
		   (recursive-closure-base-variables x-reverse)
		   xs
		   (add/remove-slots reverse-primal
				     (recursive-closure-variables x-reverse)
				     xs
				     (recursive-closure-values x-reverse)
				     '())
		   (recursive-closure-procedure-variables x-reverse)
		   (list->vector (map lambda-expression-variable es))
		   (list->vector
		    (map (lambda (e)
			  (index
			   (lambda-expression-variable e)
			   (append
			    (vector->list
			     (recursive-closure-procedure-variables x-reverse))
			    xs)
			   (copy-propagate #f (lambda-expression-body e))))
			 es))
		   (recursive-closure-index x-reverse))))))
	   ((forward-value? x-reverse)
	    (run-time-error
	     "Attempt to take reverse-primal of a non-reverse value"
	     x-reverse))
	   ((reverse-value? x-reverse) (reverse-value-primal x-reverse))
	   (else (fuck-up)))
	  x-reverse))
   (when *memoized?*
    (set! *reverse-cache* (cons reverse-cache-entry *reverse-cache*))))
  (reverse-cache-entry-primal reverse-cache-entry)))

(define (added-bindings)
 ;; needs work: To replace anonymous gensym with derived gensym.
 (map (lambda (x) (make-alpha-binding x (hensym)))
      (append
       ;; These are magic names.
       (list 'null 'car 'cdr 'cons-procedure)
       (map value-binding-variable *value-bindings*))))

(define (reverse-j v)
 (let ((reverse-cache-entry
	(find-if (lambda (reverse-cache-entry)
		  (vlad-equal?
		   (reverse-cache-entry-primal reverse-cache-entry) v))
		 *reverse-cache*)))
  (unless reverse-cache-entry
   (set! reverse-cache-entry
	 (make-reverse-cache-entry
	  v
	  (cond
	   ((null? v) (make-reverse-value v))
	   ((boolean? v) (make-reverse-value v))
	   ((real? v) (make-reverse-value v))
	   ((primitive-procedure? v) (primitive-procedure-reverse v))
	   ((closure? v)
	    (let* ((bs (added-bindings))
		   (e (reverse-transform
		       bs
		       (transformed-lambda-expression
			(closure-tags v)
			#f
			(closure-base-variables v)
			(closure-variable v)
			(closure-body v))
		       '()
		       (closure-base-variables v)
		       (map alpha-binding-variable2 bs)))
		   (e (alpha-convert
		       #f e (lambda-expression-free-variables e)))
		   (x (lambda-expression-variable e))
		   (xs (lambda-expression-free-variables e)))
	     (create-closure
	      (lambda-expression-tags e)
	      (lambda-expression-base-free-variables e)
	      xs
	      (add/remove-slots
	       reverse-j (closure-variables v) xs (closure-values v) bs)
	      x
	      (index x
		     xs
		     (copy-propagate
		      #f (anf-convert #f (lambda-expression-body e)))))))
	   ((recursive-closure? v)
	    (let* ((bs (added-bindings))
		   (es (vector->list
			(map-vector
			 (lambda (x e)
			  (reverse-transform
			   bs
			   (transformed-lambda-expression
			    (recursive-closure-tags v)
			    #f
			    (make-fake (recursive-closure-base-variables v))
			    x
			    e)
			   (vector->list
			    (recursive-closure-procedure-variables v))
			   (recursive-closure-base-variables v)
			   (map alpha-binding-variable2 bs)))
			 (recursive-closure-argument-variables v)
			 (recursive-closure-bodies v))))
		   (xs
		    (append
		     (vector->list (recursive-closure-procedure-variables v))
		     (letrec-free-variables
		      (vector->list (recursive-closure-procedure-variables v))
		      (map lambda-expression-variable es)
		      (map lambda-expression-body es))))
		   (es (map (lambda (e) (alpha-convert #f e xs)) es))
		   (xs
		    (letrec-free-variables
		     (vector->list (recursive-closure-procedure-variables v))
		     (map lambda-expression-variable es)
		     (map lambda-expression-body es))))
	     (create-recursive-closure
	      (cons 'reverse (recursive-closure-tags v))
	      ;; base
	      (recursive-closure-base-variables v)
	      xs
	      (add/remove-slots reverse-j
				(recursive-closure-variables v)
				xs
				(recursive-closure-values v)
				bs)
	      (recursive-closure-procedure-variables v)
	      (list->vector (map lambda-expression-variable es))
	      (list->vector
	       (map (lambda (e)
		     (let ((x (lambda-expression-variable e))
			   (xs (append
				(vector->list
				 (recursive-closure-procedure-variables v))
				xs)))
		      (index
		       x
		       xs
		       (copy-propagate
			#f (anf-convert #f (lambda-expression-body e))))))
		    es))
	      (recursive-closure-index v))))
	   ((forward-value? v) (make-reverse-value v))
	   ((reverse-value? v) (make-reverse-value v))
	   (else (fuck-up)))))
   (when *memoized?*
    (set! *reverse-cache* (cons reverse-cache-entry *reverse-cache*))))
  (reverse-cache-entry-reverse reverse-cache-entry)))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (let? e)
 (and (application? e) (lambda-expression? (application-callee e))))

(define (let*? e) (or (let*-expression? e) (let? e)))

(define (let*-variables e)
 (cond
  ((let*-expression? e)
   (if (let*? (let*-expression-body e))
       (append (let*-expression-variables e)
	       (let*-variables (let*-expression-body e)))
       (let*-expression-variables e)))
  ((let*? e)
   (cons (lambda-expression-variable (application-callee e))
	 (let*-variables (lambda-expression-body (application-callee e)))))
  (else '())))

(define (let*-expressions e)
 (cond ((let*-expression? e)
	(if (let*? (let*-expression-body e))
	    (append (let*-expression-expressions e)
		    (let*-expressions (let*-expression-body e)))
	    (let*-expression-expressions e)))
       ((let*? e)
	(cons
	 (application-argument e)
	 (let*-expressions (lambda-expression-body (application-callee e)))))
       (else '())))

(define (let*-body e)
 (cond ((let*-expression? e)
	(if (let*? (let*-expression-body e))
	    (let*-body (let*-expression-body e))
	    (let*-expression-body e)))
       ((let*? e) (let*-body (lambda-expression-body (application-callee e))))
       (else e)))

(define (abstract->concrete e)
 (cond
  ((let*? e)
   (let loop ((xs (let*-variables e)) (es (let*-expressions e)) (bs '()))
    (cond
     ((null? xs)
      (case (length bs)
       ((0) (fuck-up))
       ((1) `(let ,bs ,(abstract->concrete (let*-body e))))
       (else `(let* ,(reverse bs) ,(abstract->concrete (let*-body e))))))
     ((and *unabbreviate-nicely?*
	   (= (length xs) 3)
	   (result-cons? (first xs) (second xs) (third xs)
			 (first es) (second es) (third es)
			 (let*-body e)))
      (case (length bs)
       ((0) `(cons ,(abstract->concrete (partial-cons-argument (first es)))
		   ,(abstract->concrete (second es))))
       ((1) `(let ,bs
	      (cons ,(abstract->concrete (partial-cons-argument (first es)))
		    ,(abstract->concrete (second es)))))
       (else `(let* ,(reverse bs)
	       (cons ,(abstract->concrete (partial-cons-argument (first es)))
		     ,(abstract->concrete (second es)))))))
     ((and *unabbreviate-nicely?* (partial-cons? (first es)))
      (loop (rest xs)
	    (rest es)
	    (cons `(,(first xs)
		    (cons-procedure
		     ,(abstract->concrete (partial-cons-argument (first es)))))
		  bs)))
     ((and *unabbreviate-nicely?*
	   (>= (length xs) 3)
	   (cons-split? (first xs) (second xs) (third xs)
			(first es) (second es) (third es)))
      (loop (rest (rest (rest xs)))
	    (rest (rest (rest es)))
	    (cons `((cons ,(second xs) ,(third xs))
		    ,(abstract->concrete (first es)))
		  bs)))
     (else (loop (rest xs)
		 (rest es)
		 (cons `(,(first xs) ,(abstract->concrete (first es))) bs))))))
  ((variable-access-expression? e)
   (let* ((x (variable-access-expression-variable e))
	  (x (if (primitive-procedure? x)
		 (primitive-procedure-name x)
		 x)))
    (if *show-access-indices?*
	`(access ,x ,(variable-access-expression-index e))
	x)))
  ((lambda-expression? e)
   (if (or (not (null? (lambda-expression-tags e)))
	   (not (= (length (lambda-expression-base-free-variables e))
		   (length (lambda-expression-free-variables e))))
	   (not (every variable=?
		       (lambda-expression-base-free-variables e)
		       (lambda-expression-free-variables e))))
       `(tagged-lambda ,(lambda-expression-tags e)
		       ,(lambda-expression-base-free-variables e)
		       (,(lambda-expression-variable e))
		       ,(abstract->concrete (lambda-expression-body e)))
       `(lambda (,(lambda-expression-variable e))
	 ,(abstract->concrete (lambda-expression-body e)))))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((let*-expression? e) (fuck-up))
  ((letrec-expression? e)
   (if (or (not (null? (letrec-expression-tags e)))
	   (not (= (length (letrec-expression-bodies-base-free-variables e))
		   (length (letrec-expression-bodies-free-variables e))))
	   (not (every variable=?
		       (letrec-expression-bodies-base-free-variables e)
		       (letrec-expression-bodies-free-variables e))))
       `(tagged-letrec ,(letrec-expression-tags e)
		       ,(letrec-expression-bodies-base-free-variables e)
		       ,(map (lambda (x1 x2 e)
			      `(,x1 (lambda (,x2) ,(abstract->concrete e))))
			     (letrec-expression-procedure-variables e)
			     (letrec-expression-argument-variables e)
			     (letrec-expression-bodies e))
		       ,(abstract->concrete (letrec-expression-body e)))
       `(letrec ,(map (lambda (x1 x2 e)
		       `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		      (letrec-expression-procedure-variables e)
		      (letrec-expression-argument-variables e)
		      (letrec-expression-bodies e))
	 ,(abstract->concrete (letrec-expression-body e)))))
  (else (fuck-up))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((and (not *unabbreviate-transformed?*) (vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (panic "Cannot unabbreviate executably"))
		  `(forward-conjoin ,(loop (forward-primal v) quote?)
				    ,(loop (forward-adjoint v) quote?)))
		 (else `(forward ,(loop (forward-primal v) quote?)
				 ,(loop (forward-adjoint v) quote?)))))
	  ((and (not *unabbreviate-transformed?*) (vlad-reverse? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (panic "Cannot unabbreviate executably"))
		  `(reverse-j ,(loop (reverse-primal v) quote?)))
		 (else `(reverse ,(loop (reverse-primal v) quote?)))))
	  ((null? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((boolean? v) v)
	  ((real? v) v)
	  ((vlad-pair? v '())
	   (if (and *unabbreviate-executably?* (not quote?))
	       `',(cons (loop (vlad-car v '()) #t) (loop (vlad-cdr v '()) #t))
	       (cons (loop (vlad-car v '()) quote?)
		     (loop (vlad-cdr v '()) quote?))))
	  ((primitive-procedure? v)
	   (cond (*unabbreviate-executably?*
		  (when quote? (panic "Cannot unabbreviate executably"))
		  (string->symbol
		   (string-append (symbol->string (primitive-procedure-name v))
				  (symbol->string '-primitive))))
		 (else (primitive-procedure-name v))))
	  ((closure? v)
	   (cond
	    ((or (not (null? (closure-tags v)))
		 (not (= (length (closure-base-variables v))
			 (length (closure-variables v))))
		 (not (every variable=?
			     (closure-base-variables v)
			     (closure-variables v))))
	     (cond
	      (*unabbreviate-executably?*
	       (when quote? (panic "Cannot unabbreviate executably"))
	       (case (length (closure-variables v))
		((0) `(tagged-lambda ,(closure-tags v)
				     ,(closure-base-variables v)
				     (,(closure-variable v))
				     ,(abstract->concrete (closure-body v))))
		((1)
		 `(let ,(map-indexed
			 (lambda (x i)
			  `(,x
			    ,(loop (vector-ref (closure-values v) i) quote?)))
			 (closure-variables v))
		   (tagged-lambda ,(closure-tags v)
				  ,(closure-base-variables v)
				  (,(closure-variable v))
				  ,(abstract->concrete (closure-body v)))))
		(else
		 ;; This really should be a let but since the free variables
		 ;; might include car, cdr, and cons-procedure, shadowing them
		 ;; might break multiple-binding let which structures and
		 ;; destructures with car, cdr, and cons-procedure. Thus we use
		 ;; let* which does no such structuring and destructuring.
		 `(let* ,(map-indexed
			  (lambda (x i)
			   `(,x
			     ,(loop (vector-ref (closure-values v) i) quote?)))
			  (closure-variables v))
		   (tagged-lambda ,(closure-tags v)
				  ,(closure-base-variables v)
				  (,(closure-variable v))
				  ,(abstract->concrete (closure-body v)))))))
	      (*unabbreviate-closures?*
	       `(closure
		 ,(map-indexed
		   (lambda (x i)
		    `(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		   (closure-variables v))
		 (tagged-lambda ,(closure-tags v)
				,(closure-base-variables v)
				(,(closure-variable v))
				,(abstract->concrete (closure-body v)))))
	      (else `(tagged-lambda ,(closure-tags v)
				    ,(closure-base-variables v)
				    (,(closure-variable v))
				    ,(abstract->concrete (closure-body v))))))
	    (else
	     (cond
	      (*unabbreviate-executably?*
	       (when quote? (panic "Cannot unabbreviate executably"))
	       (case (length (closure-variables v))
		((0)
		 `(lambda (,(closure-variable v))
		   ,(abstract->concrete (closure-body v))))
		((1)
		 `(let ,(map-indexed
			 (lambda (x i)
			  `(,x
			    ,(loop (vector-ref (closure-values v) i) quote?)))
			 (closure-variables v))
		   (lambda (,(closure-variable v))
		    ,(abstract->concrete (closure-body v)))))
		(else
		 ;; This really should be a let but since the free variables
		 ;; might include car, cdr, and cons-procedure, shadowing them
		 ;; might break multiple-binding let which structures and
		 ;; destructures with car, cdr, and cons-procedure. Thus we use
		 ;; let* which does no such structuring and destructuring.
		 `(let* ,(map-indexed
			  (lambda (x i)
			   `(,x
			     ,(loop (vector-ref (closure-values v) i) quote?)))
			  (closure-variables v))
		   (lambda (,(closure-variable v))
		    ,(abstract->concrete (closure-body v)))))))
	      (*unabbreviate-closures?*
	       `(closure
		 ,(map-indexed
		   (lambda (x i)
		    `(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		   (closure-variables v))
		 (lambda (,(closure-variable v))
		  ,(abstract->concrete (closure-body v)))))
	      (else `(lambda (,(closure-variable v))
		      ,(abstract->concrete (closure-body v))))))))
	  ((recursive-closure? v)
	   (cond
	    ((or (not (null? (recursive-closure-tags v)))
		 (not (= (length (recursive-closure-base-variables v))
			 (length (recursive-closure-variables v))))
		 (not (every variable=?
			     (recursive-closure-base-variables v)
			     (recursive-closure-variables v))))
	     (cond
	      (*unabbreviate-executably?*
	       (when quote? (panic "Cannot unabbreviate executably"))
	       (case (length (recursive-closure-variables v))
		((0) `(tagged-letrec
		       ,(recursive-closure-tags v)
		       ,(recursive-closure-base-variables v)
		       ,(vector->list
			 (map-vector
			  (lambda (x1 x2 e)
			   `(,x1
			     (lambda (,x2) ,(abstract->concrete e))))
			  (recursive-closure-procedure-variables v)
			  (recursive-closure-argument-variables v)
			  (recursive-closure-bodies v)))
		       ,(vector-ref (recursive-closure-procedure-variables v)
				    (recursive-closure-index v))))
		((1) `(let ,(map-indexed
			     (lambda (x i)
			      `(,x
				,(loop
				  (vector-ref (recursive-closure-values v) i)
				  quote?)))
			     (recursive-closure-variables v))
		       (tagged-letrec
			,(recursive-closure-tags v)
			,(recursive-closure-base-variables v)
			,(vector->list
			  (map-vector
			   (lambda (x1 x2 e)
			    `(,x1
			      (lambda (,x2) ,(abstract->concrete e))))
			   (recursive-closure-procedure-variables v)
			   (recursive-closure-argument-variables v)
			   (recursive-closure-bodies v)))
			,(vector-ref (recursive-closure-procedure-variables v)
				     (recursive-closure-index v)))))
		(else
		 ;; This really should be a let but since the free variables
		 ;; might include car, cdr, and cons-procedure, shadowing them
		 ;; might break multiple-binding let which structures and
		 ;; destructures with car, cdr, and cons-procedure. Thus we use
		 ;; let* which does no such structuring and destructuring.
		 `(let* ,(map-indexed
			  (lambda (x i)
			   `(,x
			     ,(loop
			       (vector-ref (recursive-closure-values v) i)
			       quote?)))
			  (recursive-closure-variables v))
		   (tagged-letrec
		    ,(recursive-closure-tags v)
		    ,(recursive-closure-base-variables v)
		    ,(vector->list
		      (map-vector
		       (lambda (x1 x2 e)
			`(,x1 (lambda (,x2) ,(abstract->concrete e))))
		       (recursive-closure-procedure-variables v)
		       (recursive-closure-argument-variables v)
		       (recursive-closure-bodies v)))
		    ,(vector-ref (recursive-closure-procedure-variables v)
				 (recursive-closure-index v)))))))
	      (*unabbreviate-recursive-closures?*
	       `(tagged-recursive-closure
		 ,(recursive-closure-tags v)
		 ,(recursive-closure-base-variables v)
		 ,(map-indexed
		   (lambda (x i)
		    `(,x
		      ,(loop (vector-ref (recursive-closure-values v) i)
			     quote?)))
		   (recursive-closure-variables v))
		 ,(vector->list
		   (map-vector
		    (lambda (x1 x2 e)
		     `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		    (recursive-closure-procedure-variables v)
		    (recursive-closure-argument-variables v)
		    (recursive-closure-bodies v)))
		 ,(vector-ref (recursive-closure-procedure-variables v)
			      (recursive-closure-index v))))
	      (else (vector-ref (recursive-closure-procedure-variables v)
				(recursive-closure-index v)))))
	    (else
	     (cond
	      (*unabbreviate-executably?*
	       (when quote? (panic "Cannot unabbreviate executably"))
	       (case (length (recursive-closure-variables v))
		((0) `(letrec ,(vector->list
				(map-vector
				 (lambda (x1 x2 e)
				  `(,x1
				    (lambda (,x2) ,(abstract->concrete e))))
				 (recursive-closure-procedure-variables v)
				 (recursive-closure-argument-variables v)
				 (recursive-closure-bodies v)))
		       ,(vector-ref (recursive-closure-procedure-variables v)
				    (recursive-closure-index v))))
		((1) `(let ,(map-indexed
			     (lambda (x i)
			      `(,x
				,(loop
				  (vector-ref (recursive-closure-values v) i)
				  quote?)))
			     (recursive-closure-variables v))
		       (letrec ,(vector->list
				 (map-vector
				  (lambda (x1 x2 e)
				   `(,x1
				     (lambda (,x2) ,(abstract->concrete e))))
				  (recursive-closure-procedure-variables v)
				  (recursive-closure-argument-variables v)
				  (recursive-closure-bodies v)))
			,(vector-ref (recursive-closure-procedure-variables v)
				     (recursive-closure-index v)))))
		(else
		 ;; This really should be a let but since the free variables
		 ;; might include car, cdr, and cons-procedure, shadowing them
		 ;; might break multiple-binding let which structures and
		 ;; destructures with car, cdr, and cons-procedure. Thus we use
		 ;; let* which does no such structuring and destructuring.
		 `(let* ,(map-indexed
			  (lambda (x i)
			   `(,x
			     ,(loop
			       (vector-ref (recursive-closure-values v) i)
			       quote?)))
			  (recursive-closure-variables v))
		   (letrec ,(vector->list
			     (map-vector
			      (lambda (x1 x2 e)
			       `(,x1 (lambda (,x2) ,(abstract->concrete e))))
			      (recursive-closure-procedure-variables v)
			      (recursive-closure-argument-variables v)
			      (recursive-closure-bodies v)))
		    ,(vector-ref (recursive-closure-procedure-variables v)
				 (recursive-closure-index v)))))))
	      (*unabbreviate-recursive-closures?*
	       `(recursive-closure
		 ,(map-indexed
		   (lambda (x i)
		    `(,x
		      ,(loop (vector-ref (recursive-closure-values v) i)
			     quote?)))
		   (recursive-closure-variables v))
		 ,(vector->list
		   (map-vector
		    (lambda (x1 x2 e)
		     `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		    (recursive-closure-procedure-variables v)
		    (recursive-closure-argument-variables v)
		    (recursive-closure-bodies v)))
		 ,(vector-ref (recursive-closure-procedure-variables v)
			      (recursive-closure-index v))))
	      (else (vector-ref (recursive-closure-procedure-variables v)
				(recursive-closure-index v)))))))
	  ((forward-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond (*unabbreviate-executably?*
		  (when quote? (panic "Cannot unabbreviate executably"))
		  `(forward-conjoin ,(loop (forward-value-primal v) quote?)
				    ,(loop (forward-value-adjoint v) quote?)))
		 (else `(forward ,(loop (forward-value-primal v) quote?)
				 ,(loop (forward-value-adjoint v) quote?)))))
	  ((reverse-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond (*unabbreviate-executably?*
		  (when quote? (panic "Cannot unabbreviate executably"))
		  `(reverse-j ,(loop (reverse-value-primal v) quote?)))
		 (else `(reverse ,(loop (reverse-value-primal v) quote?)))))
	  (else (fuck-up))))))
  (if *unabbreviate-executably?*
      `(let* ,(map (lambda (x)
		    `(,(string->symbol
			(string-append (symbol->string x)
				       (symbol->string '-primitive)))
		      ,x))
		   *basis-constants*)
	,v)
      v)))

;;; Evaluator

(define (with-write-level n thunk)
 (let ((m (write-level)))
  (set-write-level! n)
  (thunk)
  (set-write-level! m)))

(define (with-write-length n thunk)
 (let ((m (write-level)))
  (set-write-length! n)
  (thunk)
  (set-write-length! m)))

(define (run-time-error message . vs)
 (format #t "Stack trace~%")
 (for-each (lambda (record)
	    (display "Procedure: ")
	    ((if *pp?* pp write) (externalize (first record)))
	    (newline)
	    (display "Argument: ")
	    ((if *pp?* pp write) (externalize (second record)))
	    (newline)
	    (newline))
	   *stack*)
 (newline)
 (for-each (lambda (v) ((if *pp?* pp write) (externalize v)) (newline)) vs)
 (panic message))

(define (tag-check? tags v)
 (or (null? tags)
     (case (first tags)
      ((forward)
       (and (vlad-forward? v) (tag-check? (rest tags) (forward-primal v))))
      ((reverse)
       (and (vlad-reverse? v) (tag-check? (rest tags) (reverse-primal v))))
      (else (fuck-up)))))

;;; needs work: This evaluator is not tail recursive.

(define (call callee argument)
 (let ((callee (dereference callee)))
  (unless (or (vlad-pair? callee '()) (vlad-procedure? callee))
   (run-time-error "Target is not a procedure" callee))
  (when *anal?*
   (unless (tag-check?
	    (cond ((primitive-procedure? callee) '())
		  ((closure? callee) (closure-tags callee))
		  ((recursive-closure? callee) (recursive-closure-tags callee))
		  (else (fuck-up)))
	    argument)
    (run-time-error "Argument has wrong type for target" callee argument)))
  (set! *stack* (cons (list callee argument) *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((closure? callee) *trace-closures?*)
	      ((recursive-closure? callee) *trace-recursive-closures?*)
	      (else (fuck-up)))
   (if *trace-argument/result?*
       (format #t "~aentering ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize callee)
	       (externalize argument))
       (format #t "~aentering ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize callee)))
   (set! *trace-level* (+ *trace-level* 1)))
  (when (and *metered?* (primitive-procedure? callee))
   (set-primitive-procedure-meter!
    callee (+ (primitive-procedure-meter callee) 1)))
  (let ((result
	 (cond
	  ((primitive-procedure? callee)
	   ((primitive-procedure-procedure callee) argument))
	  ((closure? callee)
	   (evaluate (closure-body callee) argument (closure-values callee)))
	  ((recursive-closure? callee)
	   (evaluate
	    (vector-ref (recursive-closure-bodies callee)
			(recursive-closure-index callee))
	    argument
	    (vector-append
	     (map-n-vector
	      (lambda (i)
	       (if (= i (recursive-closure-index callee))
		   ;; to preserve eq?ness
		   callee
		   (create-recursive-closure
		    (recursive-closure-tags callee)
		    (recursive-closure-base-variables callee)
		    (recursive-closure-variables callee)
		    (recursive-closure-values callee)
		    (recursive-closure-procedure-variables callee)
		    (recursive-closure-argument-variables callee)
		    (recursive-closure-bodies callee)
		    i)))
	      (vector-length (recursive-closure-bodies callee)))
	     (recursive-closure-values callee))))
	  (else (fuck-up)))))
   (set! *stack* (rest *stack*))
   (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	       ((closure? callee) *trace-closures?*)
	       ((recursive-closure? callee) *trace-recursive-closures?*)
	       (else (fuck-up)))
    (set! *trace-level* (- *trace-level* 1))
    (if *trace-argument/result?*
	(format #t "~aexiting ~s ~s~%"
		(make-string *trace-level* #\space)
		(externalize callee)
		(externalize result))
	(format #t "~aexiting ~s~%"
		(make-string *trace-level* #\space)
		(externalize callee))))
   result)))

(define (evaluate e v vs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (cond ((variable-access-expression? e)
	(lookup (variable-access-expression-index e)))
       ((lambda-expression? e)
	(create-closure
	 (lambda-expression-tags e)
	 (lambda-expression-base-free-variables e)
	 (lambda-expression-free-variables e)
	 (map-vector lookup (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
       ((application? e)
	;; This LET* is to specify the evaluation order.
	(let* ((callee (evaluate (application-callee e) v vs))
	       (argument (evaluate (application-argument e) v vs)))
	 (call callee argument)))
       ((let*-expression? e)
	(let ((x?
	       (and *x*
		    (variable=? (first (let*-expression-variables e)) *x*))))
	 (let loop ((es (let*-expression-expressions e))
		    (xs (let*-expression-variables e))
		    (vs vs))
	  (if (null? es)
	      (evaluate (let*-expression-body e) v vs)
	      (loop (rest es)
		    (rest xs)
		    ;; needs work: This is not safe-for-space because we don't
		    ;;             remove unused elements of vs.
		    (let ((v (evaluate (first es) v vs)))
		     (when x?
		      (format #t "~s=" (first xs))
		      ((if *pp?* pp write) (externalize v))
		      (newline))
		     (vector-append vs (vector v))))))))
       ((letrec-expression? e)
	(evaluate
	 (letrec-expression-body e)
	 v
	 (vector-append
	  (let ((vs (map-vector
		     lookup
		     (letrec-expression-bodies-free-variable-indices e)))
		(xs0 (list->vector (letrec-expression-procedure-variables e)))
		(xs1 (list->vector (letrec-expression-argument-variables e)))
		(es (list->vector (letrec-expression-bodies e))))
	   (map-n-vector
	    (lambda (i)
	     (create-recursive-closure
	      (letrec-expression-tags e)
	      (letrec-expression-bodies-base-free-variables e)
	      (letrec-expression-bodies-free-variables e)
	      vs
	      xs0
	      xs1
	      es
	      i))
	    (vector-length es)))
	  (map-vector lookup
		      (letrec-expression-body-free-variable-indices e)))))
       (else (fuck-up))))

;;; Primitives

(define (divide x1 x2)
 ;; An approximation of IEEE since Scheme->C hides it. Doesn't handle positive
 ;; vs. negative zero x2.
 (if (zero? x2)
     (cond ((positive? x1) infinity)
	   ((negative? x1) minus-infinity)
	   ;; Both zeros and nan.
	   (else nan))
     (/ x1 x2)))

(define (unary f s) (lambda (x) (f (dereference x))))

(define (unary-real f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x))))

(define (binary f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (vlad-pair? x '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f (vlad-car x '()) (vlad-cdr x '())))))

(define (binary-real f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (vlad-pair? x '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (dereference (vlad-car x '())))
	 (x2 (dereference (vlad-cdr x '()))))
    (unless (and (real? x1) (real? x2))
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (f x1 x2)))))

(define (ternary f s)
 (lambda (x)
  (let ((x123 (dereference x)))
   (unless (vlad-pair? x123 '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (vlad-car x123 '())) (x23 (dereference (vlad-cdr x123 '()))))
    (unless (vlad-pair? x23 '())
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (f x1 (vlad-car x23 '()) (vlad-cdr x23 '()))))))

(define (define-primitive-procedure x procedure forward reverse)
 (set! *basis-constants* (cons x *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding x (new-variable-access-expression x))
	     *variable-bindings*))
 (set! *value-bindings*
       (cons (make-value-binding
	      x (make-primitive-procedure x procedure forward reverse 0))
	     *value-bindings*)))

(define (evaluate-in-top-level-environment e)
 (let ((e (standard-prelude e)))
  (syntax-check-expression! e)
  (let ((result (concrete->abstract-expression e)))
   (evaluate (first result) 'unspecified (list->vector (second result))))))

(define (initialize-forwards-and-reverses!)
 (for-each (lambda (b)
	    (set-primitive-procedure-forward!
	     (value-binding-value b)
	     (forwardize
	      (evaluate-in-top-level-environment
	       (primitive-procedure-forward (value-binding-value b)))))
	    (set-primitive-procedure-reverse!
	     (value-binding-value b)
	     (reversize
	      (evaluate-in-top-level-environment
	       (primitive-procedure-reverse (value-binding-value b))))))
	   *value-bindings*))

(define (initialize-basis!)
 (define-primitive-procedure '+
  (binary-real + "+")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2))
	   (forward-adjoint (forward x))))
     (forward-conjoin (+ x1 x2) (+ (perturbation x1) (perturbation x2)))))
  '(letrec (((reverse +)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (+ x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse +))
			    (cons (sensitivity y) (sensitivity y)))))))))
    (reverse +)))
 (define-primitive-procedure '-
  (binary-real - "-")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2))
	   (forward-adjoint (forward x))))
     (forward-conjoin (- x1 x2) (- (perturbation x1) (perturbation x2)))))
  '(letrec (((reverse -)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (- x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse -))
			    (cons (sensitivity y) (- 0 (sensitivity y))))))))))
    (reverse -)))
 (define-primitive-procedure '*
  (binary-real * "*")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2))
	   (forward-adjoint (forward x))))
     (forward-conjoin (* x1 x2)
		      (+ (* x2 (perturbation x1)) (* x1 (perturbation x2))))))
  '(letrec (((reverse *)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (* x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse *))
			    (cons (* x2 (sensitivity y))
				  (* x1 (sensitivity y))))))))))
    (reverse *)))
 (define-primitive-procedure '/
  (binary-real divide "/")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2))
	   (forward-adjoint (forward x))))
     (forward-conjoin
      (/ x1 x2)
      (/ (- (* x2 (perturbation x1)) (* x1 (perturbation x2))) (* x2 x2)))))
  '(letrec (((reverse /)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons
		(reverse-j (/ x1 x2))
		(lambda ((sensitivity y))
		 (cons (reverse-zero (reverse /))
		       (cons (/ (sensitivity y) x2)
			     (- 0 (/ (* x1 (sensitivity y)) (* x2 x2)))))))))))
    (reverse /)))
 (define-primitive-procedure 'sqrt
  (unary-real sqrt "sqrt")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (sqrt x) (/ (perturbation x) (* 2 (sqrt x))))))
  '(letrec (((reverse sqrt)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (sqrt x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse sqrt))
			    (/ (sensitivity y) (* 2 (sqrt x))))))))))
    (reverse sqrt)))
 (define-primitive-procedure 'exp
  (unary-real exp "exp")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (exp x) (* (exp x) (perturbation x)))))
  '(letrec (((reverse exp) (lambda ((reverse x))
			    (let ((x (reverse-primal (reverse x))))
			     (cons (reverse-j (exp x))
				   (lambda ((sensitivity y))
				    (cons (reverse-zero (reverse exp))
					  (* (exp x) (sensitivity y)))))))))
    (reverse exp)))
 (define-primitive-procedure 'log
  (unary-real log "log")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (log x) (/ (perturbation x) x))))
  '(letrec (((reverse log) (lambda ((reverse x))
			    (let ((x (reverse-primal (reverse x))))
			     (cons (reverse-j (log x))
				   (lambda ((sensitivity y))
				    (cons (reverse-zero (reverse log))
					  (/ (sensitivity y) x))))))))
    (reverse log)))
 (define-primitive-procedure 'sin
  (unary-real sin "sin")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (sin x) (* (cos x) (perturbation x)))))
  '(letrec (((reverse sin) (lambda ((reverse x))
			    (let ((x (reverse-primal (reverse x))))
			     (cons (reverse-j (sin x))
				   (lambda ((sensitivity y))
				    (cons (reverse-zero (reverse sin))
					  (* (cos x) (sensitivity y)))))))))
    (reverse sin)))
 (define-primitive-procedure 'cos
  (unary-real cos "cos")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (cos x) (- 0 (* (sin x) (perturbation x))))))
  '(letrec (((reverse cos)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (cos x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse cos))
			    (- 0 (* (sin x) (sensitivity y))))))))))
    (reverse cos)))
 (define-primitive-procedure 'atan
  (binary-real atan "atan")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2))
	   (forward-adjoint (forward x))))
     (forward-conjoin (atan x2 x1)
		      (/ (- (* x1 (perturbation x2)) (* x2 (perturbation x1)))
			 (+ (* x1 x1) (* x2 x2))))))
  '(letrec (((reverse atan)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (atan x2 x1))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse atan))
			    (cons (- 0
				     (/ (* x2 (sensitivity y))
					(+ (* x1 x1) (* x2 x2))))
				  (/ (* x1 (sensitivity y))
				     (+ (* x1 x1) (* x2 x2)))))))))))
    (reverse atan)))
 (define-primitive-procedure '=
  (binary-real = "=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x))))
     (forward-conjoin (= x1 x2) '())))
  '(letrec (((reverse =)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (= x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse =))
			    (cons (reverse-zero (reverse-j x1))
				  (reverse-zero (reverse-j x2))))))))))
    (reverse =)))
 (define-primitive-procedure '<
  (binary-real < "<")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x))))
     (forward-conjoin (< x1 x2) '())))
  '(letrec (((reverse <)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (< x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse <))
			    (cons (reverse-zero (reverse-j x1))
				  (reverse-zero (reverse-j x2))))))))))
    (reverse <)))
 (define-primitive-procedure '>
  (binary-real > ">")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x))))
     (forward-conjoin (> x1 x2) '())))
  '(letrec (((reverse >)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (> x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse >))
			    (cons (reverse-zero (reverse-j x1))
				  (reverse-zero (reverse-j x2))))))))))
    (reverse >)))
 (define-primitive-procedure '<=
  (binary-real <= "<=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x))))
     (forward-conjoin (<= x1 x2) '())))
  '(letrec (((reverse <=)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (<= x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse <=))
			    (cons (reverse-zero (reverse-j x1))
				  (reverse-zero (reverse-j x2))))))))))
    (reverse <=)))
 (define-primitive-procedure '>=
  (binary-real >= ">=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (forward-primal (forward x))))
     (forward-conjoin (>= x1 x2) '())))
  '(letrec (((reverse >=)
	     (lambda ((reverse x))
	      (let (((cons x1 x2) (reverse-primal (reverse x))))
	       (cons (reverse-j (>= x1 x2))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse >=))
			    (cons (reverse-zero (reverse-j x1))
				  (reverse-zero (reverse-j x2))))))))))
    (reverse >=)))
 (define-primitive-procedure 'zero?
  (unary-real zero? "zero?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))) (forward-conjoin (zero? x) '())))
  '(letrec (((reverse zero?) (lambda ((reverse x))
			      (let ((x (reverse-primal (reverse x))))
			       (cons (reverse-j (zero? x))
				     (lambda ((sensitivity y))
				      (cons (reverse-zero (reverse zero?))
					    (reverse-zero (reverse-j x)))))))))
    (reverse zero?)))
 (define-primitive-procedure 'positive?
  (unary-real positive? "positive?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (positive? x) '())))
  '(letrec (((reverse positive?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (positive? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse positive?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse positive?)))
 (define-primitive-procedure 'negative?
  (unary-real negative? "negative?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (negative? x) '())))
  '(letrec (((reverse negative?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (negative? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse negative?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse negative?)))
 (define-primitive-procedure 'null?
  (unary null? "null?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))) (forward-conjoin (null? x) '())))
  '(letrec (((reverse null?) (lambda ((reverse x))
			      (let ((x (reverse-primal (reverse x))))
			       (cons (reverse-j (null? x))
				     (lambda ((sensitivity y))
				      (cons (reverse-zero (reverse null?))
					    (reverse-zero (reverse-j x)))))))))
    (reverse null?)))
 (define-primitive-procedure 'boolean?
  (unary boolean? "boolean?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (boolean? x) '())))
  '(letrec (((reverse boolean?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (boolean? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse boolean?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse boolean?)))
 (define-primitive-procedure 'real?
  (unary real? "real?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))) (forward-conjoin (real? x) '())))
  '(letrec (((reverse real?) (lambda ((reverse x))
			      (let ((x (reverse-primal (reverse x))))
			       (cons (reverse-j (real? x))
				     (lambda ((sensitivity y))
				      (cons (reverse-zero (reverse real?))
					    (reverse-zero (reverse-j x)))))))))
    (reverse real?)))
 (define-primitive-procedure 'pair?
  (unary (lambda (x) (vlad-pair? x '())) "pair?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))) (forward-conjoin (pair? x) '())))
  '(letrec (((reverse pair?) (lambda ((reverse x))
			      (let ((x (reverse-primal (reverse x))))
			       (cons (reverse-j (pair? x))
				     (lambda ((sensitivity y))
				      (cons (reverse-zero (reverse pair?))
					    (reverse-zero (reverse-j x)))))))))
    (reverse pair?)))
 (define-primitive-procedure 'procedure?
  (unary vlad-procedure? "procedure?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (procedure? x) '())))
  '(letrec (((reverse procedure?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (procedure? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse procedure?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse procedure?)))
 (define-primitive-procedure 'forward?
  (unary vlad-forward? "forward?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (forward? x) '())))
  '(letrec (((reverse forward?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (forward? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse forward?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse forward?)))
 (define-primitive-procedure 'reverse?
  (unary vlad-reverse? "reverse?")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x))))
     (forward-conjoin (reverse? x) '())))
  '(letrec (((reverse reverse?)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (reverse? x))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse reverse?))
			    (reverse-zero (reverse-j x)))))))))
    (reverse reverse?)))
 (define-primitive-procedure 'if-procedure
  (ternary (lambda (x1 x2 x3) (if (dereference x1) x2 x3)) "if-procedure")
  '(lambda ((forward x))
    (let (((cons* x1 x2 x3) (forward-primal (forward x)))
	  ((cons* (perturbation x1) (perturbation x2) (perturbation x3))
	   (forward-adjoint (forward x))))
     (if-procedure x1
		   (forward-conjoin x2 (perturbation x2))
		   (forward-conjoin x3 (perturbation x3)))))
  '(letrec (((reverse if-procedure)
	     (lambda ((reverse x))
	      (let (((cons* x1 x2 x3) (reverse-primal (reverse x))))
	       (if-procedure
		x1
		(cons (reverse-j x2)
		      (lambda ((sensitivity y))
		       (cons (reverse-zero (reverse if-procedure))
			     (cons* (reverse-zero (reverse-j x1))
				    (sensitivity y)
				    (reverse-zero (reverse-j x3))))))
		(cons (reverse-j x3)
		      (lambda ((sensitivity y))
		       (cons (reverse-zero (reverse if-procedure))
			     (cons* (reverse-zero (reverse-j x1))
				    (reverse-zero (reverse-j x2))
				    (sensitivity y))))))))))
    (reverse if-procedure)))
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
 	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (write x) (perturbation x))))
  '(letrec (((reverse write)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons
		(reverse-j (write x))
		(lambda ((sensitivity y))
		 (cons (reverse-zero (reverse write)) (sensitivity y))))))))
    (reverse write)))
 (define-primitive-procedure 'forward-primal
  (unary forward-primal "forward-primal")
  '(lambda ((forward (forward x)))
    (let (((forward x) (forward-primal (forward (forward x))))
	  ((perturbation (forward x)) (forward-adjoint (forward (forward x)))))
     (forward-conjoin (forward-primal (forward x))
		      (forward-primal (perturbation (forward x))))))
  '(letrec (((reverse forward-primal)
	     (lambda ((reverse (forward x)))
	      (let (((forward x) (reverse-primal (reverse (forward x)))))
	       (cons (reverse-j (forward-primal (forward x)))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse forward-primal))
			    (forward-j (sensitivity y)))))))))
    (reverse forward-primal)))
 (define-primitive-procedure 'forward-adjoint
  (unary forward-adjoint "forward-adjoint")
  '(lambda ((forward (forward x)))
    (let (((forward x) (forward-primal (forward (forward x))))
	  ((perturbation (forward x)) (forward-adjoint (forward (forward x)))))
     (forward-conjoin (forward-adjoint (forward x))
		      (forward-adjoint (perturbation (forward x))))))
  '(letrec (((reverse forward-adjoint)
	     (lambda ((reverse (forward x)))
	      (let (((forward x) (reverse-primal (reverse (forward x)))))
	       (cons
		(reverse-j (forward-adjoint (forward x)))
		(lambda ((sensitivity (perturbation y)))
		 (cons (reverse-zero (reverse forward-adjoint))
		       (forward-conjoin
			;; This is a way of getting a zero of type
			;; (sensitivity tau).
			(reverse-zero (reverse-j (forward-primal (forward x))))
			(sensitivity (perturbation y))))))))))
    (reverse forward-adjoint)))
 (define-primitive-procedure 'forward-conjoin
  (binary forward-conjoin "forward-conjoin")
  '(lambda ((forward x))
    (let (((cons x1 (perturbation x2)) (forward-primal (forward x)))
	  ((cons (perturbation x1) (perturbation (perturbation x2)))
	   (forward-adjoint (forward x))))
     (forward-conjoin
      (forward-conjoin x1 (perturbation x2))
      (forward-conjoin (perturbation x1) (perturbation (perturbation x2))))))
  '(letrec (((reverse forward-conjoin)
	     (lambda ((reverse x))
	      (let (((cons x1 (perturbation x2)) (reverse-primal (reverse x))))
	       (cons (reverse-j (forward-conjoin x1 (perturbation x2)))
		     (lambda ((sensitivity (forward y)))
		      (cons (reverse-zero (reverse forward-conjoin))
			    ;; There is vagueness here between pair of
			    ;; sensitivities and sensitivity of pair.
			    (cons (forward-primal
				   (sensitivity (forward y)))
				  ;; (perturbation (sensitivity tau)) ->
				  ;; (sensitivity (perturbation tau))
				  (forward-adjoint
				   (sensitivity (forward y)))))))))))
    (reverse forward-conjoin)))
 (define-primitive-procedure 'forward-j
  (unary forward-j "forward-j")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (forward-j x) (forward-j (perturbation x)))))
  '(letrec (((reverse forward-j)
	     (lambda ((reverse x))
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (forward-j x))
		     (lambda ((sensitivity (forward y)))
		      (cons (reverse-zero (reverse forward-j))
			    (forward-primal (sensitivity (forward y))))))))))
    (reverse forward-j)))
 (define-primitive-procedure 'reverse-zero
  (unary reverse-zero "reverse-zero")
  '(lambda ((forward (reverse x)))
    (let (((reverse x) (forward-primal (forward (reverse x))))
	  ((perturbation (reverse x)) (forward-adjoint (forward (reverse x)))))
     (forward-conjoin (reverse-zero (reverse x))
		      (reverse-zero (perturbation (reverse x))))))
  '(letrec (((reverse reverse-zero)
	     (lambda ((reverse (reverse x)))
	      (let (((reverse x) (reverse-primal (reverse (reverse x)))))
	       (cons (reverse-j (reverse-zero (reverse x)))
		     (lambda ((sensitivity (sensitivity y)))
		      (cons (reverse-zero (reverse reverse-zero))
			    (reverse-zero (reverse (reverse x))))))))))
    (reverse reverse-zero)))
 (define-primitive-procedure 'reverse-plus
  (binary reverse-plus "reverse-plus")
  ;; There is naming vagueness here between pair of sensitivities and
  ;; sensitivity of pair.
  '(lambda ((forward (sensitivity x)))
    (let (((cons (sensitivity x1) (sensitivity x2))
	   (forward-primal (forward (sensitivity x))))
	  ((cons (perturbation (sensitivity x1))
		 (perturbation (sensitivity x2)))
	   (forward-adjoint (forward (sensitivity x)))))
     (forward-conjoin (reverse-plus (sensitivity x1) (sensitivity x2))
		      ;; (sensitivity (perturbation tau)) ->
		      ;; (perturbation (sensitivity tau))
		      (reverse-plus
		       ;; (perturbation (sensitivity tau)) ->
		       ;; (sensitivity (perturbation tau))
		       (perturbation (sensitivity x1))
		       ;; (perturbation (sensitivity tau)) ->
		       ;; (sensitivity (perturbation tau))
		       (perturbation (sensitivity x2))))))
  '(letrec (((reverse reverse-plus)
	     (lambda ((reverse (sensitivity x)))
	      ;; There is naming vagueness here between pair of sensitivities
	      ;; and sensitivity of pair.
	      (let (((cons (sensitivity x1) (sensitivity x2))
		     (reverse-primal (reverse (sensitivity x)))))
	       (cons
		(reverse-j (reverse-plus (sensitivity x1) (sensitivity x2)))
		(lambda ((sensitivity (sensitivity y)))
		 (cons (reverse-zero (reverse reverse-plus))
		       ;; There is naming vagueness here between pair of
		       ;; sensitivities and sensitivity of pair.
		       (cons (sensitivity (sensitivity y))
			     (sensitivity (sensitivity y))))))))))
    (reverse reverse-plus)))
 (define-primitive-procedure 'reverse-primal
  (unary reverse-primal "reverse-primal")
  '(lambda ((forward (reverse x)))
    (let (((reverse x) (forward-primal (forward (reverse x))))
	  ((perturbation (reverse x)) (forward-adjoint (forward (reverse x)))))
     (forward-conjoin (reverse-primal (reverse x))
		      (reverse-primal (perturbation (reverse x))))))
  '(letrec (((reverse reverse-primal)
	     (lambda ((reverse (reverse x)))
	      (let (((reverse x) (reverse-primal (reverse (reverse x)))))
	       ;; The reverse-j composed with reverse-primal could be optimized
	       ;; away.
	       (cons (reverse-j (reverse-primal (reverse x)))
		     (lambda ((sensitivity y))
		      (cons (reverse-zero (reverse reverse-primal))
			    (reverse-j (sensitivity y)))))))))
    (reverse reverse-primal)))
 (define-primitive-procedure 'reverse-j
  (unary reverse-j "reverse-j")
  '(lambda ((forward x))
    (let ((x (forward-primal (forward x)))
	  ((perturbation x) (forward-adjoint (forward x))))
     (forward-conjoin (reverse-j x) (reverse-j (perturbation x)))))
  '(letrec (((reverse reverse-j)
	     (lambda ((reverse x))
	      ;; The reverse-j composed with reverse-primal could be optimized
	      ;; away.
	      (let ((x (reverse-primal (reverse x))))
	       (cons (reverse-j (reverse-j x))
		     (lambda ((sensitivity (reverse y)))
		      (cons (reverse-zero (reverse reverse-j))
			    (reverse-primal (sensitivity (reverse y))))))))))
    (reverse reverse-j)))
 (initialize-forwards-and-reverses!))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
