(MODULE MAP-CLOSURELIB-STUFF)
;;; LaHaShem HaAretz U'Mloah
;;; $Id$

;;; Map-Closure 0.4
;;; Copyright 2006 Purdue University. All rights reserved.

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
;;;    Lafayette IN 47907-2035 USA
;;;    voice: +1 765 496-3197
;;;    FAX:   +1 765 494-6440
;;;    qobi@purdue.edu
;;;    ftp://ftp.ecn.purdue.edu/qobi
;;;    http://www.ece.purdue.edu/~qobi
;;;             and
;;;    Barak A. Pearlmutter
;;;    Hamilton Institute
;;;    National University of Ireland Maynooth
;;;    Co. Kildare
;;;    Ireland
;;;    voice: +353 1 7086100
;;;    FAX:   +353 1 7086269
;;;    barak@cs.nuim.ie
;;;    http://www.bcl.hamilton.ie/~barak/

(include "QobiScheme.sch")
(include "map-closurelib-stuff.sch")

;;; Macros

;;; Structures

(define-structure constant-expression value)

(define-structure variable-access-expression variable index)

(define-structure name-expression variable index)

(define-structure lambda-expression
 free-variables
 free-variable-indices			;vector
 variable
 body)

(define-structure application callee argument)

(define-structure letrec-expression
 bodies-free-variables
 bodies-free-variable-indices		;vector
 body-free-variables
 body-free-variable-indices		;vector
 procedure-variables
 argument-variables
 bodies
 body)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure name procedure meter)

(define-structure nonrecursive-closure
 variables
 values					;vector
 variable
 body)

(define-structure recursive-closure
 variables
 values					;vector
 procedure-variables			;vector
 argument-variables			;vector
 bodies					;vector
 index)

(define-structure name variable)

;;; dummy slot is needed because of a bug in QobiScheme
(define-structure done-continuation dummy)

(define-structure argument-continuation c e v vs x xs)

(define-structure call-continuation c v)

(define-structure map-closure-continuation c v1 v2 xs vs1 vs2)

(define-structure promise-continuation c v x vs)

(define-structure cps-promise vs1 v2 v? v)

;;; Variables

(define *gensym* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *alpha* 0)

;;; Parameters

(define *include-path* '())

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-nonrecursive-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-nonrecursive-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *letrec-as-y?* #f)

(define *cps-converted?* #f)

(define *closure-converted?* #f)

;;; Procedures

;;; VLAD datastructures

(define vlad-true #t)

(define vlad-false #f)

(define (vlad-true? v) (eq? v #t))

(define (vlad-false? v) (eq? v #f))

(define (vlad-boolean? v) (or (vlad-true? v) (vlad-false? v)))

(define (vlad-pair? v) (pair? v))

(define (vlad-car v)
 (unless (vlad-pair? v)
  (run-time-error "Attempt to take vlad-car of a non-pair" v))
 (car v))

(define (vlad-cdr v)
 (unless (vlad-pair? v)
  (run-time-error "Attempt to take vlad-cdr of a non-pair" v))
 (cdr v))

(define (vlad-cons v1 v2) (cons v1 v2))

(define (vlad-procedure? v)
 (or (primitive-procedure? v)
     (nonrecursive-closure? v)
     (recursive-closure? v)
     (done-continuation? v)
     (argument-continuation? v)
     (call-continuation? v)
     (map-closure-continuation? v)
     (promise-continuation? v)))

(define (vlad-equal? v1 v2)
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (or (and (vlad-true? v1) (vlad-true? v2))
	 (and (vlad-false? v1) (vlad-false? v2)))
     (and (real? v1) (real? v2) (= v1 v2))
     (and (name? v1)
	  (name? v2)
	  (variable=? (name-variable v1) (name-variable v2)))
     (and (vlad-pair? v1)
	  (vlad-pair? v2)
	  (vlad-equal? (vlad-car v1) (vlad-car v2))
	  (vlad-equal? (vlad-cdr v1) (vlad-cdr v2)))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (= (vector-length (nonrecursive-closure-values v1))
	     (vector-length (nonrecursive-closure-values v2)))
	  (alpha-equivalent? (nonrecursive-closure-body v1)
			     (nonrecursive-closure-body v2)
			     (cons (nonrecursive-closure-variable v1)
				   (nonrecursive-closure-variables v1))
			     (cons (nonrecursive-closure-variable v2)
				   (nonrecursive-closure-variables v2)))
	  (every-vector vlad-equal?
			(nonrecursive-closure-values v1)
			(nonrecursive-closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
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
			(recursive-closure-values v2)))))

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (alpha x)
 (set! *alpha* (- *alpha* 1))
 `(alpha ,x ,*alpha*))

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
			 set!
			 either
			 all-values
			 local-set!
			 ignore
			 consvar
			 alpha))))
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
	  (not (negative? (third x))))))

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
	      (else (fuck-up)))
	     (not (not (memq (first x2)
			     (memq (first x1) '(ignore consvar)))))))))

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

;;; Expression constructors

(define (new-variable-access-expression x)
 (make-variable-access-expression x #f))

(define (new-name-expression x) (make-name-expression x #f))

(define (new-lambda-expression x e)
 (make-lambda-expression (removep variable=? x (free-variables e)) #f x e))

(define (new-application e1 e2) (make-application e1 e2))

(define (new-let* xs es e)
 (if (null? xs)
     e
     (new-application
      (new-lambda-expression (first xs) (new-let* (rest xs) (rest es) e))
      (first es))))

(define (new-letrec-expression xs1 xs2 es e)
 (if (null? xs1)
     e
     (make-letrec-expression
      (letrec-recursive-closure-variables xs1 xs2 es)
      #f
      (sort-variables
       (set-differencep
	variable=?
	(union-variables
	 (reduce
	  union-variables
	  (map (lambda (x e) (removep variable=? x (free-variables e))) xs2 es)
	  '())
	 (free-variables e))
	xs1))
      #f
      xs1
      xs2
      es
      e)))

(define (reference-graph xs1 xs2 es e)
 ;; needs work: Should have structure instead of list.
 (list (map (lambda (x1 x2 e)
	     (list
	      x1
	      (intersectionp
	       variable=? xs1 (free-variables (new-lambda-expression x2 e)))))
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

;;; LET*

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))))

;;; needs work: The counterparts of these used to be constant-time but are no
;;;             longer so. This has implications for vestigial
;;;             let*-expressions.

(define (let*? e)
 ;; This is a stronger check than:
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 (and (application? e)
      (lambda-expression? (application-callee e))
      (not (contains-letrec? (lambda-expression-body (application-callee e))))
      (not (contains-letrec? (application-argument e)))))

(define (let*-variables e)
 (if (let*? e)
     (cons (lambda-expression-variable (application-callee e))
	   (let*-variables (lambda-expression-body (application-callee e))))
     '()))

(define (let*-expressions e)
 (if (let*? e)
     (cons (application-argument e)
	   (let*-expressions (lambda-expression-body (application-callee e))))
     '()))

(define (let*-body e)
 (if (let*? e) (let*-body (lambda-expression-body (application-callee e))) e))

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
 `(let* (,@(if *letrec-as-y?*
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
	     (panic (format #f "Invalid definition: ~s" d))))
	   ds)
 (standard-prelude
  `(letrec ,(map (lambda (d)
		  `(,(definens-name (second d))
		    ,(definens-expression (second d) (third d))))
		 ds)
    ,e)))

;;; Alpha equivalence

(define (alpha-equivalent? e1 e2 xs1 xs2)
 (or
  (and (variable-access-expression? e1)
       (variable-access-expression? e2)
       (= (positionp variable=? (variable-access-expression-variable e1) xs1)
	  (positionp variable=? (variable-access-expression-variable e2) xs2)))
  (and (name-expression? e1)
       (name-expression? e2)
       (= (positionp variable=? (name-expression-variable e1) xs1)
	  (positionp variable=? (name-expression-variable e2) xs2)))
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

;;; Conversion

(define (new-let xs es e) (new-let* xs es e))

;;; CPS conversion

(define (cps-car e)
 (new-application (new-variable-access-expression 'cps-car) e))

(define (cps-cdr e)
 (new-application (new-variable-access-expression 'cps-cdr) e))

(define (cps-cons e1 e2)
 (new-application
  (new-application (new-variable-access-expression 'cps-cons-procedure) e1)
  e2))

(define (cps-cons* es)
 (cond ((null? es) (make-constant-expression '()))
       ((null? (rest es)) (first es))
       (else (cps-cons (first es) (cps-cons* (rest es))))))

(define (cps-application e . es) (new-application e (cps-cons* es)))

(define (cps-convert e)
 (new-let
  '(cps-car cps-cdr cps-cons-procedure)
  (list (new-variable-access-expression 'car)
	(new-variable-access-expression 'cdr)
	(new-variable-access-expression 'cons-procedure))
  (new-let
   (free-variables e)
   (map (lambda (x)
	 ;; This assumes that all of the free variables in the top-level
	 ;; expression are basis variables and these are bound to procedures.
	 ;; This implies that CPS conversion must come before constant
	 ;; conversion.
	 (cond ((variable=? x 'call-with-current-continuation)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-cdr x)
		    ((cps-cons-procedure (cps-car x))
		     (lambda (y) ((cps-car x) (cps-cdr y))))))))
	       ((variable=? x 'cons-procedure)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-car x)
		    (lambda (y)
		     ((cps-car y)
		      ((cps-cons-procedure (cps-cdr x)) (cps-cdr y))))))))
	       ((variable=? x 'map-closure)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-car x)
		    (map-closure
		     ((cps-cons-procedure
		       (lambda (y)
			((cps-car (cps-cdr x))
			 ((cps-cons-procedure (lambda (x) x)) y))))
		      (cps-cdr (cps-cdr x))))))))
	       ((some (lambda (b) (variable=? x (value-binding-variable b)))
		      *value-bindings*)
		(let ((x1 (gensym)))
		 (new-lambda-expression
		  x1
		  (new-application
		   (cps-car (new-variable-access-expression x1))
		   (new-application
		    (new-variable-access-expression x)
		    (cps-cdr (new-variable-access-expression x1)))))))
	       ;; This happens when the above assumption is violated.
	       (else (fuck-up))))
	(free-variables e))
   (let loop ((e1 (new-lambda-expression
		   'x (new-variable-access-expression 'x)))
	      (e2 e))
    (cond ((constant-expression? e2) (new-application e1 e2))
	  ((variable-access-expression? e2) (new-application e1 e2))
	  ((name-expression? e2) (new-application e1 e2))
	  ((lambda-expression? e2)
	   (let ((x (gensym)))
	    (new-application
	     e1
	     (new-lambda-expression
	      x
	      (new-let* (list (lambda-expression-variable e2))
			(list (cps-cdr (new-variable-access-expression x)))
			(loop (cps-car (new-variable-access-expression x))
			      (lambda-expression-body e2)))))))
	  ((application? e2)
	   (let ((x1 (gensym)) (x2 (gensym)))
	    (loop
	     (new-lambda-expression
	      x1
	      (loop (new-lambda-expression
		     x2
		     (cps-application (new-variable-access-expression x1)
				      e1
				      (new-variable-access-expression x2)))
		    (application-argument e2)))
	     (application-callee e2))))
	  ((letrec-expression? e2)
	   (panic
	    "CPS conversion on letrec expressions is not (yet) implemented"))
	  (else (fuck-up)))))))

;;; Closure conversion

(define (closure-car e)
 (new-application (new-variable-access-expression 'closure-car) e))

(define (closure-cdr e)
 (new-application (new-variable-access-expression 'closure-cdr) e))

(define (closure-cons e1 e2)
 (new-application
  (new-application (new-variable-access-expression 'closure-cons-procedure) e1)
  e2))

(define (closure-cons* es)
 (cond ((null? es) (make-constant-expression '()))
       ((null? (rest es)) (first es))
       (else (closure-cons (first es) (closure-cons* (rest es))))))

(define (closure-list es)
 (if (null? es)
     (make-constant-expression '())
     (closure-cons (first es) (closure-list (rest es)))))

(define (closure-application e . es) (new-application e (closure-cons* es)))

(define (closure-convert e)
 (new-let
  '(closure-car
    closure-cdr
    closure-cons-procedure
    closure-if-procedure
    closure-pair?
    closure-procedure?)
  (list (new-variable-access-expression 'car)
	(new-variable-access-expression 'cdr)
	(new-variable-access-expression 'cons-procedure)
	(new-variable-access-expression 'if-procedure)
	(new-variable-access-expression 'pair?)
	(new-variable-access-expression 'procedure?))
  (let ((x (gensym)))
   (new-let
    (free-variables e)
    (map (lambda (x)
	  ;; This assumes that all of the free variables in the top-level
	  ;; expression that are basis variables are bound to procedures with
	  ;; no free variables.
	  (cond
	   ((variable=? x 'pair?)
	    (closure-cons
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-if-procedure
		  ((closure-cons-procedure (closure-pair? (closure-cdr x)))
		   ((closure-cons-procedure
		     (lambda (y)
		      ((closure-if-procedure
			((closure-cons-procedure
			  (closure-procedure? (closure-car (closure-cdr x))))
			 ((closure-cons-procedure (lambda (y) #f))
			  (lambda (y) #t))))
		       '())))
		    (lambda (y) #f))))
		 '())))
	     (make-constant-expression '())))
	   ((variable=? x 'procedure?)
	    (closure-cons
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-if-procedure
		  ((closure-cons-procedure (closure-pair? (closure-cdr x)))
		   ((closure-cons-procedure
		     (lambda (y)
		      (closure-procedure? (closure-car (closure-cdr x)))))
		    (lambda (y) #f))))
		 '())))
	     (make-constant-expression '())))
	   ((variable=? x 'map-closure)
	    (closure-cons
	     (concrete->abstract-expression
	      '(let* ((y (lambda (f)
			  ((lambda (g) (lambda (x) ((f (g g)) x)))
			   (lambda (g) (lambda (x) ((f (g g)) x))))))
		      (map
		       (lambda (f)
			(y (lambda (map)
			    (lambda (l)
			     ((closure-if-procedure
			       ((closure-cons-procedure (null? l))
				((closure-cons-procedure (lambda (x) l))
				 (lambda (x)
				  ((closure-cons-procedure (f (closure-car l)))
				   (map (closure-cdr l)))))))
			      '())))))))
		(lambda (x)
		 ((closure-cons-procedure
		   (closure-car (closure-cdr (closure-cdr x))))
		  ((map (lambda (y)
			 ((closure-cons-procedure (closure-car y))
			  ((closure-car (closure-car (closure-cdr x)))
			   ((closure-cons-procedure
			     (closure-cdr (closure-car (closure-cdr x))))
			    y)))))
		   (closure-cdr (closure-cdr (closure-cdr x))))))))
	     (make-constant-expression '())))
	   ((variable=? x 'cons-procedure)
	    (closure-cons
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-cons-procedure
		  (lambda (y)
		   ((closure-cons-procedure (closure-cdr x)) (closure-cdr y))))
		 '())))
	     (make-constant-expression '())))
	   ((some (lambda (b) (variable=? x (value-binding-variable b)))
		  *value-bindings*)
	    (let ((x1 (gensym)))
	     (closure-cons
	      (new-lambda-expression
	       x1
	       (new-application
		(new-variable-access-expression x)
		(closure-cdr (new-variable-access-expression x1))))
	      (make-constant-expression '()))))
	   ;; This assumes that all of the free variables in the top-level
	   ;; expression that are not basis variables are bound to values
	   ;; generated by constant conversion (which are not procedures and
	   ;; have no nested procedures).
	   (else (new-variable-access-expression x))))
	 (free-variables e))
    (new-let
     (list x)
     (list (closure-list
	    (map (lambda (x)
		  (closure-cons (new-name-expression x)
				(new-variable-access-expression x)))
		 (free-variables e))))
     (let loop ((x1 x) (e e))
      (cond
       ((constant-expression? e) e)
       ((variable-access-expression? e)
	(closure-application
	 (new-variable-access-expression 'lookup)
	 (new-name-expression (variable-access-expression-variable e))
	 (new-variable-access-expression x1)))
       ((name-expression? e) e)
       ((lambda-expression? e)
	(let ((x2 (gensym)) (x3 (gensym)) (x4 (gensym)))
	 (closure-cons
	  (new-lambda-expression
	   x2
	   (new-let*
	    (list x3 (lambda-expression-variable e) x4)
	    (list
	     (closure-car (new-variable-access-expression x2))
	     (closure-cdr (new-variable-access-expression x2))
	     (closure-cons
	      (closure-cons
	       (new-name-expression (lambda-expression-variable e))
	       (new-variable-access-expression (lambda-expression-variable e)))
	      (new-variable-access-expression x3)))
	    (loop x4 (lambda-expression-body e))))
	  (closure-list
	   (map (lambda (x)
		 (closure-cons (new-name-expression x)
			       (loop x1 (new-variable-access-expression x))))
		(free-variables e))))))
       ((application? e)
	(let ((x2 (gensym)))
	 (new-let (list x2)
		  (list (loop x1 (application-callee e)))
		  (closure-application
		   (closure-car (new-variable-access-expression x2))
		   (closure-cdr (new-variable-access-expression x2))
		   (loop x1 (application-argument e))))))
       ((letrec-expression? e)
	(panic
	 "Closure conversion on letrec expressions is not (yet) implemented"))
       (else (fuck-up)))))))))

;;; Constant conversion

(define (constants-in e)
 (cond ((constant-expression? e) (list (constant-expression-value e)))
       ((variable-access-expression? e) '())
       ((name-expression? e) '())
       ((lambda-expression? e) (constants-in (lambda-expression-body e)))
       ((application? e)
	(unionp vlad-equal?
		(constants-in (application-callee e))
		(constants-in (application-argument e))))
       ((letrec-expression? e)
	(unionp vlad-equal?
		(reduce (lambda (vs1 vs2) (unionp vlad-equal? vs1 vs2))
			(map constants-in (letrec-expression-bodies e))
			'())
		(constants-in (letrec-expression-body e))))
       (else (fuck-up))))

(define (constant-convert bs e)
 (cond ((constant-expression? e)
	(new-variable-access-expression
	 (value-binding-variable
	  (find-if (lambda (b)
		    (vlad-equal? (value-binding-value b)
				 (constant-expression-value e)))
		   bs))))
       ((variable-access-expression? e) e)
       ((name-expression? e) e)
       ((lambda-expression? e)
	(new-lambda-expression
	 (lambda-expression-variable e)
	 (constant-convert bs (lambda-expression-body e))))
       ((application? e)
	(new-application (constant-convert bs (application-callee e))
			 (constant-convert bs (application-argument e))))
       ((letrec-expression? e)
	(new-letrec-expression
	 (letrec-expression-procedure-variables e)
	 (letrec-expression-argument-variables e)
	 (map (lambda (e) (constant-convert bs e))
	      (letrec-expression-bodies e))
	 (constant-convert bs (letrec-expression-body e))))
       (else (fuck-up))))

;;; Free variables

(define (letrec-recursive-closure-variables xs1 xs2 es)
 (sort-variables
  (set-differencep
   variable=?
   (reduce
    union-variables
    (map (lambda (x e) (removep variable=? x (free-variables e))) xs2 es)
    '())
   xs1)))

(define (free-variables e)
 (sort-variables
  (let loop ((e e))
   (cond ((constant-expression? e) '())
	 ((variable-access-expression? e)
	  (list (variable-access-expression-variable e)))
	 ((name-expression? e) (list (name-expression-variable e)))
	 ((lambda-expression? e) (lambda-expression-free-variables e))
	 ((application? e)
	  (union-variables (loop (application-callee e))
			   (loop (application-argument e))))
	 ((letrec-expression? e) (letrec-expression-body-free-variables e))
	 (else (fuck-up))))))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (variable=? x-prime x) (memp variable=? x-prime xs)) (fuck-up))
  (if (memp variable=? x-prime xs) (positionp variable=? x-prime xs) -1))
 (cond
  ((variable-access-expression? e)
   (make-variable-access-expression
    (variable-access-expression-variable e)
    (lookup (variable-access-expression-variable e))))
  ((name-expression? e)
   (make-name-expression
    (name-expression-variable e) (lookup (name-expression-variable e))))
  ((lambda-expression? e)
   (let ((xs (free-variables e)))
    (make-lambda-expression
     xs
     (list->vector (map lookup xs))
     (lambda-expression-variable e)
     (index (lambda-expression-variable e) xs (lambda-expression-body e)))))
  ((application? e)
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))))
  ((letrec-expression? e)
   (make-letrec-expression
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

;;; Concrete->abstract

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (internalize v)
 (cond ((null? v) v)
       ((boolean? v) (if v vlad-true vlad-false))
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
   (if (null? (second e))
       ;; This allows removing the standard prelude for debugging purposes.
       (third e)
       `(let (((list ,@(map first (second e)))
	       (ys (list ,@(map (lambda (b)
				 `(lambda ((list ,@(map first (second e))))
				   ,(second b)))
				(second e))))))
	 ,(third e))))
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
  ((if)
   (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
   `((if-procedure
      ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e)))))
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
  ((set!)
   (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
   `(set (name ,(second e)) ,(third e)))
  ((either)
   (if (null? (rest e))
       '(fail)
       `(if (a-boolean) ,(second e) (either ,@(rest (rest e))))))
  ((all-values)
   (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
   `(all-values-thunk (lambda () ,(second e))))
  ((local-set!)
   (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
   `(local-set (name ,(second e)) ,(third e)))
  (else (case (length (rest e))
	 ((0) `(,(first e) (cons* ,@(rest e))))
	 ((1) e)
	 (else `(,(first e) (cons* ,@(rest e))))))))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs (map value-binding-variable *value-bindings*)))
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
     ((name) (unless (and (= (length e) 2) (variable? (second e)))
	      (panic (format #f "Invalid expression: ~s" e)))
	     (unless (memp variable=? (second e) xs)
	      (panic (format #f "Unbound variable: ~s" e)))
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
     ((set!) (loop (macro-expand e) xs))
     ((either) (loop (macro-expand e) xs))
     ((all-values) (loop (macro-expand e) xs))
     ((local-set!) (loop (macro-expand e) xs))
     (else (case (length (rest e))
	    ((0) (loop (macro-expand e) xs))
	    ((1) (loop (first e) xs)
		 (loop (second e) xs))
	    (else (loop (macro-expand e) xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (concrete->abstract-expression e)
 (cond
  ((boolean? e) (concrete->abstract-expression `',e))
  ((real? e) (concrete->abstract-expression `',e))
  ((variable? e) (new-variable-access-expression e))
  ((list? e)
   (case (first e)
    ((quote) (make-constant-expression (internalize (second e))))
    ((name) (new-name-expression (second e)))
    ((lambda)
     (case (length (second e))
      ((0) (concrete->abstract-expression (macro-expand e)))
      ((1) (if (variable? (first (second e)))
	       (new-lambda-expression
		(first (second e)) (concrete->abstract-expression (third e)))
	       (concrete->abstract-expression (macro-expand e))))
      (else (concrete->abstract-expression (macro-expand e)))))
    ((letrec)
     (if *letrec-as-y?*
	 (concrete->abstract-expression (macro-expand e))
	 (let ((es (map (lambda (b)
			 (concrete->abstract-expression
			  (macro-expand (second b))))
			(second e))))
	  (new-lightweight-letrec-expression
	   (map first (second e))
	   (map lambda-expression-variable es)
	   (map lambda-expression-body es)
	   (concrete->abstract-expression (third e))))))
    ((let) (concrete->abstract-expression (macro-expand e)))
    ((let*) (concrete->abstract-expression (macro-expand e)))
    ((if) (concrete->abstract-expression (macro-expand e)))
    ((cons) (concrete->abstract-expression (macro-expand e)))
    ((cons*) (concrete->abstract-expression (macro-expand e)))
    ((list) (concrete->abstract-expression (macro-expand e)))
    ((cond) (concrete->abstract-expression (macro-expand e)))
    ((and) (concrete->abstract-expression (macro-expand e)))
    ((or) (concrete->abstract-expression (macro-expand e)))
    ((set!) (concrete->abstract-expression (macro-expand e)))
    ((either) (concrete->abstract-expression (macro-expand e)))
    ((all-values) (concrete->abstract-expression (macro-expand e)))
    ((local-set!) (concrete->abstract-expression (macro-expand e)))
    (else (case (length (rest e))
	   ((0) (concrete->abstract-expression (macro-expand e)))
	   ((1) (new-application (concrete->abstract-expression (first e))
				 (concrete->abstract-expression (second e))))
	   (else (concrete->abstract-expression (macro-expand e)))))))
  (else (fuck-up))))

(define (parse e)
 ;; In stalingrad, we alpha convert. We don't do so here since we need to
 ;; alpha convert in the evaluator and that obviates alpha conversion here.
 (let* ((e (concrete->abstract-expression e))
	;; We don't perform constant conversion before CPS conversion because
	;; that would break the assumption in CPS conversion that all free
	;; variables are bound to primitive procedures.
	(e (if *cps-converted?* (cps-convert e) e))
	;; Constant conversion must be done before closure conversion to make
	;; constants visible to map-closure.
	(bs0 (map (lambda (v) (make-value-binding (gensym) v))
		  (constants-in e)))
	(e (constant-convert bs0 e))
	(e (if *closure-converted?* (closure-convert e) e))
	;; Constant conversion must also be done after closure conversion since
	;; closure conversion introduces constants. (I believe that the only
	;; constant currently introduced is the empty list.)
	(bs1 (map (lambda (v) (make-value-binding (gensym) v))
		  (constants-in e)))
	(e (constant-convert bs1 e))
	(xs (free-variables e))
	(bs (append bs0 bs1 *value-bindings*)))
  (list
   (index #f xs e)
   xs
   (map (lambda (x)
	 (value-binding-value
	  (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs)))
	xs))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (abstract->concrete e)
 (cond
  ((let*? e)
   (let loop ((xs (let*-variables e)) (es (let*-expressions e)) (bs '()))
    (if (null? xs)
	(case (length bs)
	 ((0) (fuck-up))
	 ((1) `(let ,bs ,(abstract->concrete (let*-body e))))
	 (else `(let* ,(reverse bs) ,(abstract->concrete (let*-body e)))))
	(loop (rest xs)
	      (rest es)
	      (cons `(,(first xs) ,(abstract->concrete (first es))) bs)))))
  ((constant-expression? e)
   `',(externalize (constant-expression-value e)))
  ((variable-access-expression? e)
   (let* ((x (variable-access-expression-variable e))
	  (x (if (primitive-procedure? x)
		 (primitive-procedure-name x)
		 x)))
    (if *show-access-indices?*
	`(access ,x ,(variable-access-expression-index e))
	x)))
  ((name-expression? e)
   (if *show-access-indices?*
       `(name ,(name-expression-variable e)
	      ,(name-expression-index e))
       `(name ,(name-expression-variable e))))
  ((lambda-expression? e)
   `(lambda (,(lambda-expression-variable e))
     ,(abstract->concrete (lambda-expression-body e))))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((letrec-expression? e)
   `(letrec ,(map (lambda (x1 x2 e)
		   `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		  (letrec-expression-procedure-variables e)
		  (letrec-expression-argument-variables e)
		  (letrec-expression-bodies e))
     ,(abstract->concrete (letrec-expression-body e))))
  (else (fuck-up))))

(define (quotable? v)
 (cond ((null? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((real? v) #t)
       ((name? v) #t)
       ((vlad-pair? v) (and (quotable? (vlad-car v)) (quotable? (vlad-cdr v))))
       ((primitive-procedure? v) #f)
       ((nonrecursive-closure? v) #f)
       ((recursive-closure? v) #f)
       (else (fuck-up))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((null? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((vlad-true? v) #t)
	  ((vlad-false? v) #f)
	  ((real? v) v)
	  ((name? v) `(name ,(name-variable v)))
	  ((vlad-pair? v)
	   (if (and *unabbreviate-executably?* (not quote?))
	       (if (quotable? v)
		   `',(cons (loop (vlad-car v) #t) (loop (vlad-cdr v) #t))
		   `(cons ,(loop (vlad-car v) #f) ,(loop (vlad-cdr v) #f)))
	       (cons (loop (vlad-car v) quote?) (loop (vlad-cdr v) quote?))))
	  ((primitive-procedure? v)
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  (string->symbol
		   (string-append (symbol->string (primitive-procedure-name v))
				  (symbol->string '-primitive))))
		 (else (primitive-procedure-name v))))
	  ((nonrecursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (fuck-up))
	     (case (length (nonrecursive-closure-variables v))
	      ((0)
	       `(lambda (,(nonrecursive-closure-variable v))
		 ,(abstract->concrete (nonrecursive-closure-body v))))
	      ((1)
	       `(let ,(map-indexed
		       (lambda (x i)
			`(,x
			  ,(loop (vector-ref (nonrecursive-closure-values v) i)
				 quote?)))
		       (nonrecursive-closure-variables v))
		 (lambda (,(nonrecursive-closure-variable v))
		  ,(abstract->concrete (nonrecursive-closure-body v)))))
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
			     (vector-ref (nonrecursive-closure-values v) i)
			     quote?)))
			(nonrecursive-closure-variables v))
		 (lambda (,(nonrecursive-closure-variable v))
		  ,(abstract->concrete (nonrecursive-closure-body v)))))))
	    (*unabbreviate-nonrecursive-closures?*
	     `(nonrecursive-closure
	       ,(map-indexed
		 (lambda (x i)
		  `(,x
		    ,(loop (vector-ref (nonrecursive-closure-values v) i)
			   quote?)))
		 (nonrecursive-closure-variables v))
	       (lambda (,(nonrecursive-closure-variable v))
		,(abstract->concrete (nonrecursive-closure-body v)))))
	    (else `(lambda (,(nonrecursive-closure-variable v))
		    ,(abstract->concrete (nonrecursive-closure-body v))))))
	  ((recursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (fuck-up))
	     (case (length (recursive-closure-variables v))
	      ((0) `(letrec ,(vector->list
			      (map-vector
			       (lambda (x1 x2 e)
				`(,x1 (lambda (,x2) ,(abstract->concrete e))))
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
				 `(,x1 (lambda (,x2) ,(abstract->concrete e))))
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
			   ,(loop (vector-ref (recursive-closure-values v) i)
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
			      (recursive-closure-index v)))))
	  ((cps-promise? v)
	   ;; needs work: I haven't thought through quote? and cps-promise.
	   (when *unabbreviate-executably?*
	    (panic "Cannot unabbreviate promises executably"))
	   (if (cps-promise-v? v)
	       `(promise ,(loop (cps-promise-v v) quote?))
	       `(promise ,(map (lambda (v) (loop v quote?))
			       (cps-promise-vs1 v))
			 ,(loop (cps-promise-v2 v) quote?))))
	  (else (fuck-up))))))
  (if *unabbreviate-executably?*
      `(let* ,(map (lambda (b)
		    (let ((x (value-binding-variable b)))
		     `(,(string->symbol
			 (string-append (symbol->string x)
					(symbol->string '-primitive)))
		       ,x)))
		   *value-bindings*)
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

(define (call callee argument)
 (unless (vlad-procedure? callee)
  (run-time-error "Target is not a procedure" callee))
 (set! *stack* (cons (list callee argument) *stack*))
 (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	     ((nonrecursive-closure? callee) *trace-nonrecursive-closures?*)
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
	 ((nonrecursive-closure? callee)
	  (evaluate (nonrecursive-closure-body callee)
		    argument
		    (nonrecursive-closure-values callee)
		    (alpha (nonrecursive-closure-variable callee))
		    (list->vector (nonrecursive-closure-variables callee))))
	 ((recursive-closure? callee)
	  (evaluate
	   (vector-ref (recursive-closure-bodies callee)
		       (recursive-closure-index callee))
	   argument
	   (vector-append (map-n-vector
			   (lambda (i)
			    (if (= i (recursive-closure-index callee))
				;; to preserve eq?ness
				callee
				(make-recursive-closure
				 (recursive-closure-variables callee)
				 (recursive-closure-values callee)
				 (recursive-closure-procedure-variables callee)
				 (recursive-closure-argument-variables callee)
				 (recursive-closure-bodies callee)
				 i)))
			   (vector-length (recursive-closure-bodies callee)))
			  (recursive-closure-values callee))
	   (alpha (vector-ref (recursive-closure-argument-variables callee)
			      (recursive-closure-index callee)))
	   (vector-append
	    (recursive-closure-procedure-variables callee)
	    (list->vector (recursive-closure-variables callee)))))
	 (else (fuck-up)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((nonrecursive-closure? callee) *trace-nonrecursive-closures?*)
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
  result))

(define (evaluate e v vs x xs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (define (lookup-name i) (if (= i -1) x (vector-ref xs i)))
 (cond ((variable-access-expression? e)
	(lookup (variable-access-expression-index e)))
       ((name-expression? e)
	(make-name (lookup-name (name-expression-index e))))
       ((lambda-expression? e)
	(make-nonrecursive-closure
	 (map lookup-name
	      (vector->list (lambda-expression-free-variable-indices e)))
	 (map-vector lookup (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
       ((application? e)
	;; This LET* is to specify the evaluation order.
	(let* ((callee (evaluate (application-callee e) v vs x xs))
	       (argument (evaluate (application-argument e) v vs x xs)))
	 (call callee argument)))
       ((letrec-expression? e)
	(evaluate
	 (letrec-expression-body e)
	 v
	 (vector-append
	  (let ((vs (map-vector
		     lookup
		     (letrec-expression-bodies-free-variable-indices e)))
		;; We don't alpha-rename the procedure variables since, with
		;; the current implementation, map-closure won't see them.
		(xs0 (list->vector (letrec-expression-procedure-variables e)))
		(xs1 (list->vector (letrec-expression-argument-variables e)))
		(es (list->vector (letrec-expression-bodies e))))
	   (map-n-vector
	    (lambda (i)
	     (make-recursive-closure
	      (letrec-expression-bodies-free-variables e) vs xs0 xs1 es i))
	    (vector-length es)))
	  (map-vector lookup
		      (letrec-expression-body-free-variable-indices e)))
	 x
	 (vector-append
	  ;; We don't alpha-rename the procedure variables since, with
	  ;; the current implementation, map-closure won't see them.
	  (list->vector (letrec-expression-procedure-variables e))
	  (map-vector lookup-name
		      (letrec-expression-body-free-variable-indices e)))))
       (else (fuck-up))))

;;; This encapsulation and the resulting hair is needed to get tail recursion
;;; in Scheme->C.
(define (cps-evaluate lazy-map-closure? e v vs x xs)
 (define (cps-call-continuation c argument)
  (cond
   ((done-continuation? c) argument)
   ((argument-continuation? c)
    (cps-evaluate (make-call-continuation (argument-continuation-c c) argument)
		  (argument-continuation-e c)
		  (argument-continuation-v c)
		  (argument-continuation-vs c)
		  (argument-continuation-x c)
		  (argument-continuation-xs c)))
   ((call-continuation? c)
    (cps-call (call-continuation-c c) (call-continuation-v c) argument))
   ((map-closure-continuation? c)
    (if (null? (map-closure-continuation-xs c))
	(cps-call-continuation
	 (map-closure-continuation-c c)
	 (let ((vs (reverse (cons argument (map-closure-continuation-vs2 c))))
	       (v2 (map-closure-continuation-v2 c)))
	  (cond
	   ((nonrecursive-closure? v2)
	    (make-nonrecursive-closure (nonrecursive-closure-variables v2)
				       (list->vector vs)
				       (nonrecursive-closure-variable v2)
				       (nonrecursive-closure-body v2)))
	   ((recursive-closure? v2)
	    ;; Native map-closure (when you don't specify -closure-converted)
	    ;; has a different semantics when using native letrec (when you
	    ;; don't specify -letrec-as-y). It doesn't map over the
	    ;; procedure-variable slots.
	    (make-recursive-closure (recursive-closure-variables v2)
				    (list->vector vs)
				    (recursive-closure-procedure-variables v2)
				    (recursive-closure-argument-variables v2)
				    (recursive-closure-bodies v2)
				    (recursive-closure-index v2)))
	   ((argument-continuation? v2)
	    (make-argument-continuation (first vs)
					(argument-continuation-e v2)
					(second vs)
					(list->vector (rest (rest vs)))
					(argument-continuation-x v2)
					(argument-continuation-xs v2)))
	   ((call-continuation? v2)
	    (make-call-continuation (first vs) (second vs)))
	   ((map-closure-continuation? v2)
	    (make-map-closure-continuation
	     (first vs)
	     (second vs)
	     (third vs)
	     (map-closure-continuation-xs v2)
	     (list->vector
	      (sublist vs 3 (+ (length (map-closure-continuation-vs1 v2)) 3)))
	     (list->vector
	      (sublist vs
		       (+ (length (map-closure-continuation-vs1 v2)) 3)
		       (+ (length (map-closure-continuation-vs1 v2))
			  (length (map-closure-continuation-vs2 v2))
			  3)))))
	   ((promise-continuation? v2)
	    (make-promise-continuation (first vs)
				       (second vs)
				       (promise-continuation-x v2)
				       (rest (rest vs))))
	   (else (fuck-up)))))
	(cps-call
	 (make-map-closure-continuation
	  (map-closure-continuation-c c)
	  (map-closure-continuation-v1 c)
	  (map-closure-continuation-v2 c)
	  (rest (map-closure-continuation-xs c))
	  (rest (map-closure-continuation-vs1 c))
	  (cons argument (map-closure-continuation-vs2 c)))
	 (map-closure-continuation-v1 c)
	 (vlad-cons (make-name (first (map-closure-continuation-xs c)))
		    (first (map-closure-continuation-vs1 c))))))
   ((promise-continuation? c)
    (cond
     ((null? (promise-continuation-vs c))
      (set-cps-promise-v?! (promise-continuation-v c) #t)
      (set-cps-promise-v! (promise-continuation-v c) argument)
      (cps-call-continuation (promise-continuation-c c) argument))
     (else (cps-call
	    (make-promise-continuation (promise-continuation-c c)
				       (promise-continuation-v c)
				       (promise-continuation-x c)
				       (but-last (promise-continuation-vs c)))
	    (last (promise-continuation-vs c))
	    (vlad-cons (make-name (promise-continuation-x c)) argument)))))
   (else (fuck-up))))
 (define (cps-call c callee argument)
  ;; needs work: stack, tracing
  (cond
   ((primitive-procedure? callee)
    (when *metered?*
     (set-primitive-procedure-meter!
      callee (+ (primitive-procedure-meter callee) 1)))
    (case (primitive-procedure-procedure callee)
     ((call-with-current-continuation)
      (when *closure-converted?*
       (run-time-error
	"Cannot (currently) call call-with-current-continuation when you specify -closure-converted together with -cps-evaluator unless you also specify -cps-converted"
	argument))
      (cps-call c argument c))
     ((map-closure)
      (when *cps-converted?*
       (run-time-error
	"Cannot (currently) call map-closure when you specify -cps-converted unless you also specify -closure-converted" argument))
      (unless (vlad-pair? argument)
       (run-time-error "Invalid argument to map-closure" argument))
      (let ((v1 (vlad-car argument))
	    (v2 (vlad-cdr argument)))
       (cond
	((primitive-procedure? v2) (cps-call-continuation c v2))
	((nonrecursive-closure? v2)
	 (if (null? (nonrecursive-closure-variables v2))
	     (cps-call-continuation c v2)
	     (if lazy-map-closure?
		 (cps-call-continuation
		  c
		  (make-nonrecursive-closure
		   (nonrecursive-closure-variables v2)
		   (map-vector
		    (lambda (x v)
		     (if (cps-promise? v)
			 (if (cps-promise-v? v)
			     (make-cps-promise
			      (list v1) (cps-promise-v v) #f #f)
			     (make-cps-promise (cons v1 (cps-promise-vs1 v))
					       (cps-promise-v2 v)
					       #f
					       #f))
			 (make-cps-promise (list v1) v #f #f)))
		    (list->vector (nonrecursive-closure-variables v2))
		    (nonrecursive-closure-values v2))
		   (nonrecursive-closure-variable v2)
		   (nonrecursive-closure-body v2)))
		 (cps-call
		  (make-map-closure-continuation
		   c
		   v1
		   v2
		   (rest (nonrecursive-closure-variables v2))
		   (rest (vector->list (nonrecursive-closure-values v2)))
		   '())
		  v1
		  (vlad-cons
		   (make-name (first (nonrecursive-closure-variables v2)))
		   (vector-ref (nonrecursive-closure-values v2) 0))))))
	((recursive-closure? v2)
	 (if (null? (recursive-closure-variables v2))
	     ;; Native map-closure (when you don't specify -closure-converted)
	     ;; has a different semantics when using native letrec (when you
	     ;; don't specify -letrec-as-y). It doesn't map over the
	     ;; procedure-variable slots.
	     (cps-call-continuation c v2)
	     (if lazy-map-closure?
		 ;; Native map-closure (when you don't specify
		 ;; -closure-converted) has a different semantics when using
		 ;; native letrec (when you don't specify -letrec-as-y). It
		 ;; doesn't map over the procedure-variable slots.
		 (cps-call-continuation
		  c
		  (make-recursive-closure
		   (recursive-closure-variables v2)
		   (map-vector
		    (lambda (x v)
		     (if (cps-promise? v)
			 (if (cps-promise-v? v)
			     (make-cps-promise
			      (list v1) (cps-promise-v v) #f #f)
			     (make-cps-promise (cons v1 (cps-promise-vs1 v))
					       (cps-promise-v2 v)
					       #f
					       #f))
			 (make-cps-promise (list v1) v #f #f)))
		    (list->vector (recursive-closure-variables v2))
		    (recursive-closure-values v2))
		   (recursive-closure-procedure-variables v2)
		   (recursive-closure-argument-variables v2)
		   (recursive-closure-bodies v2)
		   (recursive-closure-index v2)))
		 ;; Native map-closure (when you don't specify
		 ;; -closure-converted) has a different semantics when using
		 ;; native letrec (when you don't specify -letrec-as-y). It
		 ;; doesn't map over the procedure-variable slots.
		 (cps-call
		  (make-map-closure-continuation
		   c
		   v1
		   v2
		   (rest (recursive-closure-variables v2))
		   (rest (vector->list (recursive-closure-values v2)))
		   '())
		  v1
		  (vlad-cons
		   (make-name (first (recursive-closure-variables v2)))
		   (vector-ref (recursive-closure-values v2) 0))))))
	((done-continuation? v2) (cps-call-continuation c v2))
	((argument-continuation? v2)
	 (cps-call (make-map-closure-continuation
		    c
		    v1
		    v2
		    (cons (argument-continuation-x v2)
			  (vector->list (argument-continuation-xs v2)))
		    (cons (argument-continuation-v v2)
			  (vector->list (argument-continuation-vs v2)))
		    '())
		   v1
		   ;; This gives the continuation an anonymous name.
		   (vlad-cons (make-name #f) (argument-continuation-c v2))))
	((call-continuation? v2)
	 (cps-call (make-map-closure-continuation
		    ;; This gives the callee value an anonymous name.
		    c v1 v2 '(#f) (list (call-continuation-v v2)) '())
		   v1
		   ;; This gives the continuation an anonymous name.
		   (vlad-cons (make-name #f) (call-continuation-c v2))))
	((map-closure-continuation? v2)
	 (cps-call
	  (make-map-closure-continuation
	   c
	   v1
	   v2
	   ;; This gives the v1, v2, vs1, and vs2 values anonymous names.
	   (map-n (lambda (i) #f)
		  (+ (length (map-closure-continuation-vs1 v2))
		     (length (map-closure-continuation-vs2 v2))
		     2))
	   (cons (map-closure-continuation-v1 v2)
		 (cons (map-closure-continuation-v2 v2)
		       (append (map-closure-continuation-vs1 v2)
			       (map-closure-continuation-vs2 v2))))
	   '())
	  v1
	  ;; This gives the continuation an anonymous name.
	  (vlad-cons (make-name #f) (map-closure-continuation-c v2))))
	((promise-continuation? v2)
	 (cps-call
	  (make-map-closure-continuation
	   c
	   v1
	   v2
	   ;; This gives the v and vs values anonymous names.
	   (map-n (lambda (i) #f) (+ (length (promise-continuation-vs v2)) 1))
	   (cons (promise-continuation-v v2) (promise-continuation-vs v2))
	   '())
	  v1
	  ;; This gives the continuation an anonymous name.
	  (vlad-cons (make-name #f) (promise-continuation-c v2))))
	(else (run-time-error
	       "Invalid argument to map-closure" (vlad-cons v1 v2))))))
     (else (cps-call-continuation
	    c ((primitive-procedure-procedure callee) argument)))))
   ((nonrecursive-closure? callee)
    (cps-evaluate c
		  (nonrecursive-closure-body callee)
		  argument
		  (nonrecursive-closure-values callee)
		  (alpha (nonrecursive-closure-variable callee))
		  (list->vector (nonrecursive-closure-variables callee))))
   ((recursive-closure? callee)
    (cps-evaluate
     c
     (vector-ref (recursive-closure-bodies callee)
		 (recursive-closure-index callee))
     argument
     (vector-append (map-n-vector
		     (lambda (i)
		      (if (= i (recursive-closure-index callee))
			  ;; to preserve eq?ness
			  callee
			  (make-recursive-closure
			   (recursive-closure-variables callee)
			   (recursive-closure-values callee)
			   (recursive-closure-procedure-variables callee)
			   (recursive-closure-argument-variables callee)
			   (recursive-closure-bodies callee)
			   i)))
		     (vector-length (recursive-closure-bodies callee)))
		    (recursive-closure-values callee))
     (alpha (vector-ref (recursive-closure-argument-variables callee)
			(recursive-closure-index callee)))
     (vector-append (recursive-closure-procedure-variables callee)
		    (list->vector (recursive-closure-variables callee)))))
   ((or (done-continuation? callee)
	(argument-continuation? callee)
	(call-continuation? callee)
	(map-closure-continuation? callee)
	(promise-continuation? callee))
    (cps-call-continuation callee argument))
   (else (run-time-error "Target is not a procedure" callee))))
 (define (cps-evaluate c e v vs x xs)
  (define (lookup i) (if (= i -1) v (vector-ref vs i)))
  (define (lookup-name i) (if (= i -1) x (vector-ref xs i)))
  (cond
   ((variable-access-expression? e)
    (let ((v (lookup (variable-access-expression-index e))))
     (if (cps-promise? v)
	 (if (cps-promise-v? v)
	     (cps-call-continuation c (cps-promise-v v))
	     (cps-call
	      (make-promise-continuation
	       c
	       v
	       (make-name (lookup-name (variable-access-expression-index e)))
	       (but-last (cps-promise-vs1 v)))
	      (last (cps-promise-vs1 v))
	      (vlad-cons
	       (make-name (lookup-name (variable-access-expression-index e)))
	       (cps-promise-v2 v))))
	 (cps-call-continuation c v))))
   ((name-expression? e)
    (cps-call-continuation
     c (make-name (lookup-name (name-expression-index e)))))
   ((lambda-expression? e)
    (cps-call-continuation
     c
     (make-nonrecursive-closure
      (map lookup-name
	   (vector->list (lambda-expression-free-variable-indices e)))
      (map-vector lookup (lambda-expression-free-variable-indices e))
      (lambda-expression-variable e)
      (lambda-expression-body e))))
   ((application? e)
    (cps-evaluate
     (make-argument-continuation c (application-argument e) v vs x xs)
     (application-callee e)
     v
     vs
     x
     xs))
   ((letrec-expression? e)
    (cps-evaluate
     c
     (letrec-expression-body e)
     v
     (vector-append
      (let ((vs (map-vector
		 lookup (letrec-expression-bodies-free-variable-indices e)))
	    ;; We don't alpha-rename the procedure variables since, with
	    ;; the current implementation, map-closure won't see them.
	    (xs0 (list->vector (letrec-expression-procedure-variables e)))
	    (xs1 (list->vector (letrec-expression-argument-variables e)))
	    (es (list->vector (letrec-expression-bodies e))))
       (map-n-vector
	(lambda (i)
	 (make-recursive-closure
	  (letrec-expression-bodies-free-variables e) vs xs0 xs1 es i))
	(vector-length es)))
      (map-vector lookup (letrec-expression-body-free-variable-indices e)))
     x
     (vector-append
      ;; We don't alpha-rename the procedure variables since, with
      ;; the current implementation, map-closure won't see them.
      (list->vector (letrec-expression-procedure-variables e))
      (map-vector lookup-name
		  (letrec-expression-body-free-variable-indices e)))))
   (else (fuck-up))))
 (cps-evaluate (make-done-continuation #f) e v vs x xs))

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

(define (unary f s) f)

(define (unary-predicate f s) (lambda (x) (if (f x) vlad-true vlad-false)))

(define (unary-real f s)
 (lambda (x)
  (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f x)))

(define (unary-real-predicate f s)
 (lambda (x)
  (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (if (f x) vlad-true vlad-false)))

(define (binary f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f (vlad-car x) (vlad-cdr x))))

(define (binary-real f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 x2))))

(define (binary-real-predicate f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (f x1 x2) vlad-true vlad-false))))

(define (ternary f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x23 (vlad-cdr x)))
   (unless (vlad-pair? x23)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 (vlad-car x23) (vlad-cdr x23)))))

(define (define-primitive-procedure x procedure)
 (set! *value-bindings*
       (cons (make-value-binding x (make-primitive-procedure x procedure 0))
	     *value-bindings*)))

(define (initialize-basis! cps-evaluator?)
 (define-primitive-procedure '+ (binary-real + "+"))
 (define-primitive-procedure '- (binary-real - "-"))
 (define-primitive-procedure '* (binary-real * "*"))
 (define-primitive-procedure '/ (binary-real divide "/"))
 (define-primitive-procedure 'sqrt (unary-real sqrt "sqrt"))
 (define-primitive-procedure 'exp (unary-real exp "exp"))
 (define-primitive-procedure 'log (unary-real log "log"))
 (define-primitive-procedure 'sin (unary-real sin "sin"))
 (define-primitive-procedure 'cos (unary-real cos "cos"))
 (define-primitive-procedure 'atan (binary-real atan "atan"))
 (define-primitive-procedure '= (binary-real-predicate = "="))
 (define-primitive-procedure '< (binary-real-predicate < "<"))
 (define-primitive-procedure '> (binary-real-predicate > ">"))
 (define-primitive-procedure '<= (binary-real-predicate <= "<="))
 (define-primitive-procedure '>= (binary-real-predicate >= ">="))
 (define-primitive-procedure 'zero? (unary-real-predicate zero? "zero?"))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?"))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?"))
 (define-primitive-procedure 'null? (unary-predicate null? "null?"))
 (define-primitive-procedure 'boolean?
  (unary-predicate vlad-boolean? "boolean?"))
 (define-primitive-procedure 'real? (unary-predicate real? "real?"))
 (define-primitive-procedure 'pair? (unary-predicate vlad-pair? "pair?"))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?"))
 (define-primitive-procedure 'equal?
  (binary (lambda (x1 x2) (if (equal? x1 x2) vlad-true vlad-false)) "equal?"))
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write"))
 (define-primitive-procedure 'car (binary (lambda (x1 x2) x1) "car"))
 (define-primitive-procedure 'cdr (binary (lambda (x1 x2) x2) "cdr"))
 ;; Note that map-closure will not see the closure slot of a partial
 ;; application of cons-procedure.
 (define-primitive-procedure 'cons-procedure
  (unary (lambda (x1)
	  (make-primitive-procedure
	   "cons-procedure" (lambda (x2) (vlad-cons x1 x2)) 0))
	 "cons-procedure"))
 (define-primitive-procedure 'if-procedure
  (ternary (lambda (x1 x2 x3) (if x1 x2 x3)) "if-procedure"))
 ;; These are specific to Map-Closure.
 (define-primitive-procedure 'name? (unary-predicate name? "name?"))
 (define-primitive-procedure 'name=?
  (binary (lambda (x1 x2)
	   (unless (and (name? x1) (name? x2))
	    (run-time-error "Invalid argument to name?" (vlad-cons x1 x2)))
	   (if (variable=? (name-variable x1) (name-variable x2))
	       vlad-true
	       vlad-false))
	  "name=?"))
 (define-primitive-procedure 'call-with-current-continuation
  (if cps-evaluator?
      'call-with-current-continuation
      (unary (lambda (x)
	      (run-time-error
	       "Cannot (currently) call call-with-current-continuation unless you specify -cps-converted or -cps-evaluator"
	       x))
	     "call-with-current-continuation")))
 (define-primitive-procedure 'map-closure
  (if cps-evaluator?
      'map-closure
      (binary
       (lambda (x1 x2)
	(when *cps-converted?*
	 (run-time-error
	  "Cannot (currently) call map-closure when you specify -cps-converted unless you also specify -closure-converted" (vlad-cons x1 x2)))
	(cond
	 ((primitive-procedure? x2) x2)
	 ((nonrecursive-closure? x2)
	  (make-nonrecursive-closure
	   (nonrecursive-closure-variables x2)
	   (map-vector (lambda (x v) (call x1 (vlad-cons (make-name x) v)))
		       (list->vector (nonrecursive-closure-variables x2))
		       (nonrecursive-closure-values x2))
	   (nonrecursive-closure-variable x2)
	   (nonrecursive-closure-body x2)))
	 ((recursive-closure? x2)
	  ;; Native map-closure (when you don't specify -closure-converted) has
	  ;; a different semantics when using native letrec (when you don't
	  ;; specify -letrec-as-y). It doesn't map over the
	  ;; procedure-variable slots.
	  (make-recursive-closure
	   (recursive-closure-variables x2)
	   (map-vector (lambda (x v) (call x1 (vlad-cons (make-name x) v)))
		       (list->vector (recursive-closure-variables x2))
		       (recursive-closure-values x2))
	   (recursive-closure-procedure-variables x2)
	   (recursive-closure-argument-variables x2)
	   (recursive-closure-bodies x2)
	   (recursive-closure-index x2)))
	 (else (run-time-error
		"Invalid argument to map-closure" (vlad-cons x1 x2)))))
       "map-closure")))
 ;; needs work: To implement this natively as part of closure conversion.
 (define-primitive-procedure 'lookup
  (binary (lambda (x1 x2)
	   (unless (name? x1)
	    (run-time-error "Invalid argument to lookup" (vlad-cons x1 x2)))
	   (let loop ((x x2))
	    (when (null? x) (fuck-up))
	    (unless (and (vlad-pair? x)
			 (vlad-pair? (vlad-car x))
			 (name? (vlad-car (vlad-car x))))
	     (run-time-error "Invalid argument to lookup" (vlad-cons x1 x2)))
	    (if (variable=? (name-variable (vlad-car (vlad-car x)))
			    (name-variable x1))
		(vlad-cdr (vlad-car x))
		(loop (vlad-cdr x)))))
	  "lookup")))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
