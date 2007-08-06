(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah
;;; $Id$

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004, 2005, 2006, and 2007 Purdue University. All rights
;;; reserved.

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
;;;    National University of Ireland, Maynooth
;;;    Co. Kildare
;;;    Ireland
;;;    voice: +353 1 7086100
;;;    FAX:   +353 1 7086269
;;;    barak@cs.nuim.ie
;;;    http://www.bcl.hamilton.ie/~barak/

(include "QobiScheme.sch")
(include "c-externals.sc")
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. zero, primal, tangent, bundle, plus, *j, and *j-inverse should be lazy.
;;;  2. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  3. unary -
;;;  4. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  5. chars, ports, eof object, symbols, continuations, strings, vectors

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: concrete or abstract value
;;;  d: definition
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

;;; Structures

(define-structure constant-expression value)

(define-structure variable-access-expression variable)

(define-structure lambda-expression free-variables parameter body)

(define-structure application free-variables callee argument)

(define-structure letrec-expression
 free-variables procedure-variables lambda-expressions body)

(define-structure cons-expression free-variables tags car cdr)

(define-structure variable-binding variable expression)

(define-structure parameter-binding parameter expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 name procedure generator forward reverse meter)

(define-structure nonrecursive-closure values lambda-expression)

(define-structure recursive-closure
 values
 procedure-variables			;vector
 lambda-expressions			;vector
 index)

(define-structure bundle primal tangent)

(define-structure reverse-tagged-value primal)

(define-structure tagged-pair tags car cdr)

(define-structure environment-binding values value)

(define-structure expression-binding expression flow)

;;; Variables

(define *gensym* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *error* #f)

(define *error?* #f)

;;; Parameters

(define *include-path* '())

(define *wizard?* #f)

(define *flow-analysis?* #f)

(define *compile?* #f)

(define *expression-equality* 'structural)

(define *metered?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-nonrecursive-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-transformed?* #t)

(define *unabbreviate-nonrecursive-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *verbose?* #f)

(define *imprecise-inexacts?* #f)

(define *run?* #f)

;;; Procedures

;;; General

(define (duplicates? xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (member (first xs) (rest xs)) (duplicates? (rest xs)))))

(define (duplicatesp? p xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (memp p (first xs) (rest xs)) (duplicatesp? p (rest xs)))))

(define (positionp-vector p x v)
 ;; belongs in QobiScheme
 (let loop ((i 0))
  (cond ((>= i (vector-length v)) #f)
	((p x (vector-ref v i)) i)
	(else (loop (+ i 1))))))

(define (map-reduce g i f l . ls)
 ;; belongs in QobiScheme
 (let loop ((l l) (ls ls) (c i))
  (if (null? l)
      c
      (loop (rest l) (map rest ls) (g (apply f (first l) (map first ls)) c)))))

(define (remove-oneq x l)
 ;; belongs in QobiScheme
 (when (null? l) (internal-error))
 (if (eq? (first l) x)
     (rest l)
     (cons (first l) (remove-oneq x (rest l)))))

;;; Error Handing

(define (compile-time-error message . arguments)
 (apply format stderr-port message arguments)
 (newline stderr-port)
 (exit -1))

(define (run-time-error message . vs)
 (when *error?*
  (display "Nested error: " stderr-port)
  (display message stderr-port)
  (newline stderr-port)
  (display "Error: " stderr-port)
  (display *error* stderr-port)
  (newline stderr-port)
  (exit -1))
 (set! *error* message)
 (set! *error?* #t)
 (when *run?*
  (format stderr-port "Stack trace~%")
  (for-each (lambda (record)
	     (display "Procedure: " stderr-port)
	     ((if *pp?* pp write) (externalize (first record)) stderr-port)
	     (newline stderr-port)
	     (display "Argument: " stderr-port)
	     ((if *pp?* pp write) (externalize (second record)) stderr-port)
	     (newline stderr-port)
	     (newline stderr-port))
	    *stack*)
  (newline stderr-port))
 (for-each (lambda (v)
	    ((if *pp?* pp write) (externalize v) stderr-port)
	    (newline stderr-port))
	   vs)
 (display "Error: " stderr-port)
 (display message stderr-port)
 (newline stderr-port)
 (exit -1))

(define (internal-error . arguments)
 (if (null? arguments)
     (panic "Internal error")
     (apply panic
	    (format #f "Internal error: ~a" (first arguments))
	    (rest arguments))))

(define (unimplemented . arguments)
 (if (null? arguments)
     (panic "Not (yet) implemented")
     (apply panic
	    (format #f "Not (yet) implemented: ~a" (first arguments))
	    (rest arguments))))

;;; Tags

(define (empty-tags) '())

(define (empty-tags? tags) (null? tags))

(define (add-tag tag tags) (cons tag tags))

(define (tagged? tag tags) (and (not (null? tags)) (eq? (first tags) tag)))

(define (remove-tag tag tags)
 (unless (tagged? tag tags) (internal-error))
 (rest tags))

(define (prefix-tags? tags1 tags2)
 (or (null? tags1)
     (and (not (null? tags2))
	  (eq? (first tags1) (first tags2))
	  (prefix-tags? (rest tags1) (rest tags2)))))

(define (equal-tags? tags1 tags2) (equal? tags1 tags2))

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (user-variable? x)
 (and (symbol? x)
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
		     alpha
		     anf
		     forward
		     sensitivity
		     backpropagator
		     reverse)))))

(define (variable? x)
 (or (user-variable? x)
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
	 ((alpha) (variable-anf-max (second x)))
	 ((anf) (second x))
	 ((forward sensitivity backpropagator reverse)
	  (variable-anf-max (second x)))
	 (else (internal-error))))
       (else (internal-error))))

(define (variable=? x1 x2) (equal? x1 x2))

;;; needs work: variable-base, variable-alpha, and base-variable<? are only
;;;             used to implement variable<? which is only used in
;;;             sort-variables. We may eliminate this.
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
	      ((anf) (< (second x1) (second x2)))
	      ((forward sensitivity backpropagator reverse)
	       (variable<? (second x1) (second x2)))
	      (else (internal-error)))
	     (not (not (memq (first x2)
			     (memq (first x1)
				   '(anf
				     forward
				     sensitivity
				     backpropagator
				     reverse)))))))))

(define (variable<? x1 x2)
 (or (base-variable<? (variable-base x1) (variable-base x2))
     (and (variable=? (variable-base x1) (variable-base x2))
	  ((lexicographically<? < =)
	   (reverse (variable-alpha x1)) (reverse (variable-alpha x2))))))

(define (sort-variables xs) (sort xs variable<? identity))

(define (forwardify x) `(forward ,x))

(define (sensitivityify x) `(sensitivity ,x))

(define (backpropagatorify x) `(backpropagator ,x))

(define (reverseify x) `(reverse ,x))

(define (unforwardify x)
 (unless (pair? x) (internal-error))
 (case (first x)
  ((alpha) (internal-error))
  ((forward) (second x))
  ((sensitivity) (internal-error))
  ((reverse) (internal-error))
  (else (internal-error))))

(define (unreverseify x)
 (unless (pair? x) (internal-error))
 (case (first x)
  ((alpha) (internal-error))
  ((forward) (internal-error))
  ((sensitivity) (internal-error))
  ((reverse) (second x))
  (else (internal-error))))

(define (forward-access x) (make-variable-access-expression (forwardify x)))

(define (sensitivity-access x)
 (make-variable-access-expression (sensitivityify x)))

(define (backpropagator-access x)
 (make-variable-access-expression (backpropagatorify x)))

(define (reverse-access x) (make-variable-access-expression (reverseify x)))

(define (unforward-access x)
 (make-variable-access-expression (unforwardify x)))

(define (unreverse-access x)
 (make-variable-access-expression (unreverseify x)))

(define (forwardify-access e)
 (make-variable-access-expression
  (forwardify (variable-access-expression-variable e))))

(define (sensitivityify-access e)
 (make-variable-access-expression
  (sensitivityify (variable-access-expression-variable e))))

(define (backpropagatorify-access e)
 (make-variable-access-expression
  (backpropagatorify (variable-access-expression-variable e))))

(define (reverseify-access e)
 (make-variable-access-expression
  (reverseify (variable-access-expression-variable e))))

(define (unforwardify-access e)
 (make-variable-access-expression
  (unforwardify (variable-access-expression-variable e))))

(define (unreverseify-access e)
 (make-variable-access-expression
  (unreverseify (variable-access-expression-variable e))))

(define (variable-tags x)
 (if (pair? x)
     (case (first x)
      ((alpha) (internal-error))
      ((forward) (add-tag 'forward (variable-tags (second x))))
      ((sensitivity) (variable-tags (second x)))
      ((backpropagator) (variable-tags (second x)))
      ((reverse) (add-tag 'reverse (variable-tags (second x))))
      (else (empty-tags)))
     (empty-tags)))

;;; Parameters

(define (parameter-tags p)
 (cond ((constant-expression? p) (value-tags (constant-expression-value p)))
       ((variable-access-expression? p)
	(variable-tags (variable-access-expression-variable p)))
       ((cons-expression? p) (cons-expression-tags p))
       (else (internal-error))))

(define (lambda-expression-tags e)
 (parameter-tags (lambda-expression-parameter e)))

(define (forward-parameter? p) (tagged? 'forward (parameter-tags p)))

(define (reverse-parameter? p) (tagged? 'reverse (parameter-tags p)))

;;; Free variables

(define (union-variables xs1 xs2) (unionp variable=? xs1 xs2))

(define (free-variables e)
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       ((application? e) (application-free-variables e))
       ((letrec-expression? e) (letrec-expression-free-variables e))
       ((cons-expression? e) (cons-expression-free-variables e))
       (else (internal-error))))

(define (recursive-closure-free-variables xs es)
 (sort-variables
  (set-differencep
   variable=? (map-reduce union-variables '() free-variables es) xs)))

(define (parameter-variables p)
 (cond ((constant-expression? p) '())
       ((variable-access-expression? p)
	(list (variable-access-expression-variable p)))
       ((cons-expression? p)
	(append (parameter-variables (cons-expression-car p))
		(parameter-variables (cons-expression-cdr p))))
       (else (internal-error))))

;;; Expression constructors

(define (new-lambda-expression p e)
 (make-lambda-expression
  (sort-variables
   (set-differencep variable=? (free-variables e) (parameter-variables p)))
  p
  e))

(define (new-application e1 e2)
 (make-application
  (sort-variables (union-variables (free-variables e1) (free-variables e2)))
  e1
  e2))

(define (new-let* ps es e)
 (if (null? ps)
     e
     (new-application
      (new-lambda-expression (first ps) (new-let* (rest ps) (rest es) e))
      (first es))))

(define (create-let* bs e)
 (new-let* (map parameter-binding-parameter bs)
	   (map parameter-binding-expression bs)
	   e))

(define (new-letrec-expression xs es e)
 (if (null? xs)
     e
     (make-letrec-expression
      (sort-variables
       (set-differencep
	variable=?
	(union-variables (map-reduce union-variables '() free-variables es)
			 (free-variables e))
	xs))
      xs
      es
      e)))

(define (reference-graph xs es e)
 ;; needs work: Should have structure instead of list.
 (list
  (map (lambda (x e) (list x (intersectionp variable=? xs (free-variables e))))
       xs
       es)
  (intersectionp variable=? xs (free-variables e))))

(define (transitive-closure arms)
 ;; needs work: Should have structure instead of list.
 (let loop ((arms arms))
  (let ((new-arms
	 (map (lambda (arm)
	       (list (first arm)
		     (union-variables
		      (second arm)
		      (map-reduce
		       union-variables
		       '()
		       (lambda (target) (second (assp variable=? target arms)))
		       (second arm)))))
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

(define (lightweight-letrec-conversion xs es e)
 ;; needs work: Should have structure instead of list.
 (let* ((reference-graph (reference-graph xs es e))
	(arms (first reference-graph))
	(xs1 (second reference-graph))
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
      (some (lambda (x1)
	     (some (lambda (x2)
		    (or (variable=? x2 x1)
			(memp variable=?
			      x2
			      (second (assp variable=? x1 transitive-arms)))))
		   component))
	    xs1))
     (strongly-connected-components arms transitive-arms))))))

(define (create-letrec-expression xs es e)
 (let loop ((clusters (lightweight-letrec-conversion xs es e)))
  (if (null? clusters)
      e
      (let ((cluster (first clusters)))
       (if (second cluster)
	   (new-letrec-expression
	    (first cluster)
	    (map (lambda (x) (list-ref es (positionp variable=? x xs)))
		 (first cluster))
	    (loop (rest clusters)))
	   (let ((x (first (first cluster))))
	    (new-let* (list (make-variable-access-expression x))
		      (list (list-ref es (positionp variable=? x xs)))
		      (loop (rest clusters)))))))))

(define (new-cons-expression tags e1 e2)
 (make-cons-expression
  (sort-variables (union-variables (free-variables e1) (free-variables e2)))
  tags
  e1
  e2))

(define (create-cons-expression e1 e2)
 (new-cons-expression (empty-tags) e1 e2))

;;; LET*

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))
     (and (cons-expression? e)
	  (or (contains-letrec? (cons-expression-car e))
	      (contains-letrec? (cons-expression-cdr e))))))

(define (let*? e)
 ;; This is a stronger check than:
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 (and (application? e)
      (lambda-expression? (application-callee e))
      (not (contains-letrec? (lambda-expression-body (application-callee e))))
      (not (contains-letrec? (application-argument e)))))

(define (let*-parameters e)
 (if (let*? e)
     (cons (lambda-expression-parameter (application-callee e))
	   (let*-parameters (lambda-expression-body (application-callee e))))
     '()))

(define (let*-expressions e)
 (if (let*? e)
     (cons (application-argument e)
	   (let*-expressions (lambda-expression-body (application-callee e))))
     '()))

(define (let*-body e)
 (if (let*? e) (let*-body (lambda-expression-body (application-callee e))) e))

;;; Expression Equivalence

(define (expression-eqv? e1 e2)
 (or
  (and (constant-expression? e1)
       (constant-expression? e2)
       (abstract-value=? (constant-expression-value e1)
			 (constant-expression-value e2)))
  (and (variable-access-expression? e1)
       (variable-access-expression? e2)
       (variable=? (variable-access-expression-variable e1)
		   (variable-access-expression-variable e2)))
  (and (lambda-expression? e1)
       (lambda-expression? e2)
       (expression-eqv? (lambda-expression-parameter e1)
			(lambda-expression-parameter e2))
       (expression-eqv? (lambda-expression-body e1)
			(lambda-expression-body e2)))
  (and (application? e1)
       (application? e2)
       (expression-eqv? (application-callee e1) (application-callee e2))
       (expression-eqv? (application-argument e1)(application-argument e2)))
  (and (letrec-expression? e1)
       (letrec-expression? e2)
       (= (length (letrec-expression-procedure-variables e1))
	  (length (letrec-expression-procedure-variables e2)))
       (every variable=?
	      (letrec-expression-procedure-variables e1)
	      (letrec-expression-procedure-variables e2))
       (every expression-eqv?
	      (letrec-expression-lambda-expressions e1)
	      (letrec-expression-lambda-expressions e2))
       (expression-eqv? (letrec-expression-body e1)
			(letrec-expression-body e2)))
  (and (cons-expression? e1) (cons-expression? e2)
       (equal-tags? (cons-expression-tags e1) (cons-expression-tags e2))
       (expression-eqv? (cons-expression-car e1) (cons-expression-car e2))
       (expression-eqv? (cons-expression-cdr e1) (cons-expression-cdr e2)))))

(define (alpha-equivalent? e1 e2 xs1 xs2)
 ;; This is what Stump calls hypothetical (or contextual) alpha equivalence,
 ;; i.e. whether e1 is alpha-equivalent to e2 in the context where each xs1_i
 ;; is assumed to be equivalent to the corresponding ex2_i.
 (or
  (and (constant-expression? e1)
       (constant-expression? e2)
       (abstract-value=? (constant-expression-value e1)
			 (constant-expression-value e2)))
  (and (variable-access-expression? e1)
       (variable-access-expression? e2)
       (= (positionp variable=? (variable-access-expression-variable e1) xs1)
	  (positionp variable=? (variable-access-expression-variable e2) xs2)))
  (and (lambda-expression? e1)
       (lambda-expression? e2)
       (= (length (parameter-variables (lambda-expression-parameter e1)))
	  (length (parameter-variables (lambda-expression-parameter e2))))
       (alpha-equivalent?
	(lambda-expression-parameter e1)
	(lambda-expression-parameter e2)
	(parameter-variables (lambda-expression-parameter e1))
	(parameter-variables (lambda-expression-parameter e2)))
       (alpha-equivalent?
	(lambda-expression-body e1)
	(lambda-expression-body e2)
	(append (parameter-variables (lambda-expression-parameter e1)) xs1)
	(append (parameter-variables (lambda-expression-parameter e2)) xs2)))
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
       (every (lambda (e3 e4)
	       (alpha-equivalent?
		e3
		e4
		(append (letrec-expression-procedure-variables e1) xs1)
		(append (letrec-expression-procedure-variables e2) xs2)))
	      (letrec-expression-lambda-expressions e1)
	      (letrec-expression-lambda-expressions e2))
       (alpha-equivalent?
	(letrec-expression-body e1)
	(letrec-expression-body e2)
	(append (letrec-expression-procedure-variables e1) xs1)
	(append (letrec-expression-procedure-variables e2) xs2)))
  (and (cons-expression? e1)
       (cons-expression? e2)
       (equal-tags? (cons-expression-tags e1) (cons-expression-tags e2))
       (alpha-equivalent?
	(cons-expression-car e1) (cons-expression-car e2) xs1 xs2)
       (alpha-equivalent?
	(cons-expression-cdr e1) (cons-expression-cdr e2) xs1 xs2))))

(define (expression=? e1 e2)
 ;; Two expressions are equal if they yield equal values in all possible
 ;; environments. (The notion of expression equality depends on the notion of
 ;; value equality.) Expression equality is undecidable. (It is semidecidable
 ;; since a lone environment can witness disequality and environments are
 ;; recursively enumerable. This selects among a hierarchy of more precise
 ;; conservative approximation alternatives. A #t result is precise.
 ((case *expression-equality*
   ((identity) eq?)
   ((structural) expression-eqv?)
   ((alpha) (unimplemented "Alpha equivalence"))
   (else (internal-error)))
  e1 e2))

;;; Values

;;; Empty Lists

(define (vlad-empty-list) '())

(define (vlad-empty-list? v) (null? v))

;;; Booleans

(define (vlad-true) #t)

(define (vlad-false) #f)

(define (vlad-true? v) (eq? v #t))

(define (vlad-false? v) (eq? v #f))

(define (abstract-boolean? v)
 (or (vlad-true? v) (vlad-false? v) (eq? v 'boolean)))

;;; Reals

(define (abstract-real? v) (or (real? v) (eq? v 'real)))

;;; Closures

(define (new-nonrecursive-closure vs e)
 ;; An alternative check would be that the tags of each free variable are
 ;; a prefix of the tags of the value to which it is bound.
 (let ((tags (lambda-expression-tags e)))
  (unless (every (lambda (v) (prefix-tags? tags (value-tags v))) vs)
   (internal-error)))
 (make-nonrecursive-closure vs e))

(define (new-recursive-closure vs xs es i)
 ;; An alternative check would be that the tags of each recursive-closure free
 ;; variable are a prefix of the tags of the value to which it is bound.
 ;; There will always be at least one procedure variable and one lambda
 ;; expression.
 (let ((tags (lambda-expression-tags (first es))))
  (unless (every (lambda (v) (prefix-tags? tags (value-tags v))) vs)
   (internal-error)))
 (make-recursive-closure vs xs es i))

(define (nonrecursive-closure-match? v1 v2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (expression=? (nonrecursive-closure-lambda-expression v1)
		   (nonrecursive-closure-lambda-expression v2))))

(define (recursive-closure-match? v1 v2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (= (recursive-closure-index v1) (recursive-closure-index v2))
	  (= (vector-length (recursive-closure-procedure-variables v1))
	     (vector-length (recursive-closure-procedure-variables v2)))
	  (= (vector-length (recursive-closure-lambda-expressions v1))
	     (vector-length (recursive-closure-lambda-expressions v2)))
	  (every-vector variable=?
			(recursive-closure-procedure-variables v1)
			(recursive-closure-procedure-variables v2))
	  (every-vector expression=?
			(recursive-closure-lambda-expressions v1)
			(recursive-closure-lambda-expressions v2)))))

(define (closure? v) (or (nonrecursive-closure? v) (recursive-closure? v)))

(define (nonrecursive-closure-variables v)
 (free-variables (nonrecursive-closure-lambda-expression v)))

(define (recursive-closure-variables v)
 (recursive-closure-free-variables
  (vector->list (recursive-closure-procedure-variables v))
  (vector->list (recursive-closure-lambda-expressions v))))

(define (closure-variables v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-variables v))
       ((recursive-closure? v) (recursive-closure-variables v))
       (else (internal-error))))

(define (nonrecursive-closure-parameter v)
 (lambda-expression-parameter (nonrecursive-closure-lambda-expression v)))

(define (recursive-closure-parameter v)
 (lambda-expression-parameter
  (vector-ref (recursive-closure-lambda-expressions v)
	      (recursive-closure-index v))))

(define (closure-parameter v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-parameter v))
       ((recursive-closure? v) (recursive-closure-parameter v))
       (else (internal-error))))

(define (nonrecursive-closure-tags v)
 (parameter-tags (nonrecursive-closure-parameter v)))

(define (recursive-closure-tags v)
 (parameter-tags (recursive-closure-parameter v)))

(define (closure-body v)
 (lambda-expression-body
  (cond ((nonrecursive-closure? v) (nonrecursive-closure-lambda-expression v))
	((recursive-closure? v)
	 (vector-ref (recursive-closure-lambda-expressions v)
		     (recursive-closure-index v)))
	(else (internal-error)))))

(define (vlad-procedure? v) (or (primitive-procedure? v) (closure? v)))

;;; Pairs

(define (new-tagged-pair tags v1 v2)
 (unless (and (prefix-tags? tags (value-tags v1))
	      (prefix-tags? tags (value-tags v2)))
  (internal-error))
 (make-tagged-pair tags v1 v2))

(define (vlad-pair? v)
 (and (tagged-pair? v) (empty-tags? (tagged-pair-tags v))))

(define (vlad-car v)
 (unless (vlad-pair? v) (internal-error))
 (tagged-pair-car v))

(define (vlad-cdr v)
 (unless (vlad-pair? v) (internal-error))
 (tagged-pair-cdr v))

(define (vlad-cons v1 v2) (new-tagged-pair (empty-tags) v1 v2))

;;; Generic

(define (vlad-forward? v)
 (or (and (nonrecursive-closure? v)
	  (forward-parameter? (nonrecursive-closure-parameter v)))
     (and (recursive-closure? v)
	  (forward-parameter? (recursive-closure-parameter v)))
     (bundle? v)
     (and (tagged-pair? v) (tagged? 'forward (tagged-pair-tags v)))))

(define (vlad-reverse? v)
 (or (and (nonrecursive-closure? v)
	  (reverse-parameter? (nonrecursive-closure-parameter v)))
     (and (recursive-closure? v)
	  (reverse-parameter? (recursive-closure-parameter v)))
     (reverse-tagged-value? v)
     (and (tagged-pair? v) (tagged? 'reverse (tagged-pair-tags v)))))

(define (scalar-value? v)
 (or (vlad-empty-list? v)
     (abstract-boolean? v)
     (abstract-real? v)
     (primitive-procedure? v)))

(define (aggregate-value-values v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-values v))
       ((recursive-closure? v) (recursive-closure-values v))
       ((bundle? v) (list (bundle-primal v) (bundle-tangent v)))
       ((reverse-tagged-value? v) (list (reverse-tagged-value-primal v)))
       ((tagged-pair? v) (list (tagged-pair-car v) (tagged-pair-cdr v)))
       (else (internal-error))))

(define (value-tags v)
 (cond ((scalar-value? v) '())
       ((nonrecursive-closure? v) (nonrecursive-closure-tags v))
       ((recursive-closure? v) (recursive-closure-tags v))
       ((bundle? v) (add-tag 'forward (value-tags (bundle-primal v))))
       ((reverse-tagged-value? v)
	(add-tag 'reverse (value-tags (reverse-tagged-value-primal v))))
       ((tagged-pair? v) (tagged-pair-tags v))
       (else (internal-error))))

;;; Top

(define (abstract-top? v) (eq? v 'top))

(define (abstract-top) 'top)

;;; Abstract Value Equivalence and Union

(define (abstract-value=? v1 v2)
 (or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
     (and (abstract-boolean? v1)
	  (abstract-boolean? v2)
	  (or (and (vlad-true? v1) (vlad-true? v2))
	      (and (vlad-false? v1) (vlad-false? v2))
	      (and (eq? v1 'boolean) (eq? v2 'boolean))))
     (and (abstract-real? v1)
	  (abstract-real? v2)
	  ;; This was = but then it equates exact values with inexact values
	  ;; and this breaks -imprecise-inexacts.
	  (equal? v1 v2))
     (and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (nonrecursive-closure-match? v1 v2)
	  (abstract-environment=? (nonrecursive-closure-values v1)
				  (nonrecursive-closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (recursive-closure-match? v1 v2)
	  (abstract-environment=? (recursive-closure-values v1)
				  (recursive-closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (abstract-value=? (bundle-primal v1) (bundle-primal v2))
	  (abstract-value=? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (abstract-value=? (reverse-tagged-value-primal v1)
			    (reverse-tagged-value-primal v2)))
     (and (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (abstract-value=? (tagged-pair-car v1) (tagged-pair-car v2))
	  (abstract-value=? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))
     (and (abstract-top? v1) (abstract-top? v2))))

(define (abstract-value-union v1 v2)
 (cond ((and (vlad-empty-list? v1) (vlad-empty-list? v2)) v1)
       ((and (abstract-boolean? v1) (abstract-boolean? v2))
	(if (or (and (vlad-true? v1) (vlad-true? v2))
		(and (vlad-false? v1) (vlad-false? v2)))
	    v1
	    'boolean))
       ((and (abstract-real? v1) (abstract-real? v2))
	(if (equal? v1 v2) v1 'real))
       ((and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
	v1)
       ((and (nonrecursive-closure? v1)
	     (nonrecursive-closure? v2)
	     (nonrecursive-closure-match? v1 v2))
	(let ((vs
	       (abstract-environment-union (nonrecursive-closure-values v1)
					   (nonrecursive-closure-values v2))))
	 (if (some abstract-top? vs)
	     (abstract-top)
	     ;; See the note in abstract-environment=?.
	     (new-nonrecursive-closure
	      vs (nonrecursive-closure-lambda-expression v1)))))
       ((and (recursive-closure? v1)
	     (recursive-closure? v2)
	     (recursive-closure-match? v1 v2))
	(let ((vs (abstract-environment-union (recursive-closure-values v1)
					      (recursive-closure-values v2))))
	 (if (some abstract-top? vs)
	     (abstract-top)
	     ;; See the note in abstract-environment=?.
	     (new-recursive-closure vs
				    (recursive-closure-procedure-variables v1)
				    (recursive-closure-lambda-expressions v1)
				    (recursive-closure-index v1)))))
       ((and (bundle? v1) (bundle? v2))
	(let ((v-primal (abstract-value-union (bundle-primal v1)
					      (bundle-primal v2)))
	      (v-tangent (abstract-value-union (bundle-tangent v1)
					       (bundle-tangent v2))))
	 (if (or (abstract-top? v-primal) (abstract-top? v-tangent))
	     (abstract-top)
	     (make-bundle v-primal v-tangent))))
       ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	(let ((v (abstract-value-union (reverse-tagged-value-primal v1)
				       (reverse-tagged-value-primal v2))))
	 (if (abstract-top? v) (abstract-top) (make-reverse-tagged-value v))))
       ((and (tagged-pair? v1)
	     (tagged-pair? v2)
	     (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
	(let ((v-car (abstract-value-union (tagged-pair-car v1)
					   (tagged-pair-car v2)))
	      (v-cdr (abstract-value-union (tagged-pair-cdr v1)
					   (tagged-pair-cdr v2))))
	 (if (or (abstract-top? v-car) (abstract-top? v-cdr))
	     (abstract-top)
	     (new-tagged-pair (tagged-pair-tags v1) v-car v-cdr))))
       (else (abstract-top))))

;;; Abstract Environment Equivalence and Union

(define (abstract-environment=? vs1 vs2)
 ;; This assumes that the free variables in two alpha-equivalent expressions
 ;; are in the same order. Note that this is a weak notion of equivalence. A
 ;; stronger notion would attempt to find a correspondence between the free
 ;; variables that would allow them to be contextually alpha equivalent.
 (every abstract-value=? vs1 vs2))

(define (abstract-environment-union vs1 vs2)
 (map abstract-value-union vs1 vs2))

;;; Search path

(define (search-include-path-without-extension pathname)
 (cond ((can-open-file-for-input? pathname) pathname)
       ((and (>= (string-length pathname) 1)
	     (char=? (string-ref pathname 0) #\/))
	(compile-time-error "Cannot find: ~a" pathname))
       (else (let loop ((include-path *include-path*))
	      (cond ((null? include-path)
		     (compile-time-error "Cannot find: ~a" pathname))
		    ((can-open-file-for-input?
		      (string-append (first include-path) "/" pathname))
		     (string-append (first include-path) "/" pathname))
		    (else (loop (rest include-path))))))))

(define (search-include-path pathname)
 (search-include-path-without-extension (default-extension pathname "vlad")))

(define (read-source pathname)
 (let ((pathname (default-extension pathname "vlad")))
  (unless (can-open-file-for-input? pathname)
   (compile-time-error "Cannot find: ~a" pathname))
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
 (for-each
  (lambda (d)
   (unless (definition? d) (compile-time-error "Invalid definition: ~s" d)))
  ds)
 `(letrec ,(map (lambda (d)
		 `(,(definens-name (second d))
		   ,(definens-expression (second d) (third d))))
		ds)
   ,e))

;;; Closure conversion

(define (tagged-empty-list tags)
 (if (null? tags)
     (vlad-empty-list)
     (case (first tags)
      ((forward)
       (let ((v (tagged-empty-list (rest tags)))) (bundle v (zero v))))
      ((reverse) (*j (tagged-empty-list (rest tags))))
      (else (internal-error)))))

(define (variables->expression tags xs)
 (if (null? xs)
     (make-constant-expression (tagged-empty-list tags))
     (new-cons-expression tags
			  (make-variable-access-expression (first xs))
			  (variables->expression tags (rest xs)))))

(define (closure-convert e)
 (cond
  ((constant-expression? e) e)
  ((variable-access-expression? e) e)
  ((lambda-expression? e)
   (let ((xs (free-variables e)) (tags (lambda-expression-tags e)))
    (new-cons-expression
     tags
     (variables->expression tags xs)
     (new-lambda-expression
      (new-cons-expression tags
			   (variables->expression tags xs)
			   (lambda-expression-parameter e))
      (closure-convert (lambda-expression-body e))))))
  ((application? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((x1 (gensym)) (x2 (gensym)))
    (new-let* (list (create-cons-expression
		     (make-variable-access-expression x1)
		     (make-variable-access-expression x2)))
	      (list (closure-convert (application-callee e)))
	      (new-application (make-variable-access-expression x2)
			       (create-cons-expression
				(make-variable-access-expression x1)
				(closure-convert (application-argument e)))))))
  ((letrec-expression? e)
   (let ((xs (recursive-closure-free-variables
	      (letrec-expression-procedure-variables e)
	      (letrec-expression-lambda-expressions e))))
    (new-letrec-expression
     (letrec-expression-procedure-variables e)
     (map (lambda (e1)
	   (let ((tags (lambda-expression-tags e1)))
	    (new-lambda-expression
	     (new-cons-expression tags
				  (variables->expression tags xs)
				  (lambda-expression-parameter e1))
	     ;; needs work: This could be a LET.
	     (new-let* (map make-variable-access-expression
			    (letrec-expression-procedure-variables e))
		       (map (lambda (x)
			     (new-cons-expression
			      tags
			      (variables->expression tags xs)
			      (make-variable-access-expression x)))
			    (letrec-expression-procedure-variables e))
		       (closure-convert (lambda-expression-body e1))))))
	  (letrec-expression-lambda-expressions e))
     ;; needs work: This could be a LET.
     (new-let* (map make-variable-access-expression
		    (letrec-expression-procedure-variables e))
	       (map (lambda (x)
		     (let ((tags (variable-tags x)))
		      (new-cons-expression
		       tags
		       (variables->expression tags xs)
		       (make-variable-access-expression x))))
		    (letrec-expression-procedure-variables e))
	       (closure-convert (letrec-expression-body e))))))
  ((cons-expression? e)
   (new-cons-expression (cons-expression-tags e)
			(closure-convert (cons-expression-car e))
			(closure-convert (cons-expression-cdr e))))
  (else (internal-error))))

;;; Alpha conversion

(define (alphaify x xs)
 (if (memp variable=? x xs)
     `(alpha ,x
	     ,(+ (map-reduce max
			     0
			     (lambda (x1)
			      (if (and (list? x1)
				       (eq? (first x1) 'alpha)
				       (variable=? (second x1) x))
				  (third x1)
				  0))
			     xs)
		 1))
     x))

(define (alpha-convert-parameter p xs)
 ;; needs work: Should have structure instead of list.
 (cond ((constant-expression? p) (list xs '() p))
       ((variable-access-expression? p)
	(let ((x (alphaify (variable-access-expression-variable p) xs)))
	 (list
	  (cons x xs)
	  (list (make-alpha-binding (variable-access-expression-variable p) x))
	  (make-variable-access-expression x))))
       ((cons-expression? p)
	(let* ((result1 (alpha-convert-parameter (cons-expression-car p) xs))
	       (result2 (alpha-convert-parameter (cons-expression-cdr p)
						 (first result1))))
	 (list (first result2)
	       (append (second result1) (second result2))
	       (new-cons-expression
		(cons-expression-tags p) (third result1) (third result2)))))
       (else (internal-error))))

(define (alpha-convert-expression e xs)
 ;; needs work: Should have structure instead of list.
 (let outer ((e e) (xs xs) (bs (map make-alpha-binding xs xs)))
  (cond
   ((constant-expression? e) (list xs e))
   ((variable-access-expression? e)
    (list xs
	  (make-variable-access-expression
	   (alpha-binding-variable2
	    (find-if (lambda (b)
		      (variable=? (alpha-binding-variable1 b)
				  (variable-access-expression-variable e)))
		     bs)))))
   ((lambda-expression? e)
    (let* ((result1
	    (alpha-convert-parameter (lambda-expression-parameter e) xs))
	   (result2 (outer (lambda-expression-body e)
			   (first result1)
			   (append (second result1) bs))))
     (list (first result2)
	   (new-lambda-expression (third result1) (second result2)))))
   ((application? e)
    (let* ((result1 (outer (application-callee e) xs bs))
	   (result2 (outer (application-argument e) (first result1) bs)))
     (list (first result2)
	   (new-application (second result1) (second result2)))))
   ((letrec-expression? e)
    (let loop ((xs1 (letrec-expression-procedure-variables e))
	       (xs2 '())
	       (xs xs))
     (if (null? xs1)
	 (let ((bs (append (map make-alpha-binding
				(letrec-expression-procedure-variables e)
				(reverse xs2))
			   bs)))
	  (let inner ((es (letrec-expression-lambda-expressions e))
		      (es1 '())
		      (xs xs))
	   (if (null? es)
	       (let ((result (outer (letrec-expression-body e) xs bs)))
		(list (first result)
		      (new-letrec-expression
		       (reverse xs2) (reverse es1) (second result))))
	       (let ((result (outer (first es) xs bs)))
		(inner (rest es) (cons (second result) es1) (first result))))))
	 (let ((x (alphaify (first xs1) xs)))
	  (loop (rest xs1) (cons x xs2) (cons x xs))))))
   ((cons-expression? e)
    (let* ((result1 (outer (cons-expression-car e) xs bs))
	   (result2 (outer (cons-expression-cdr e) (first result1) bs)))
     (list (first result2)
	   (new-cons-expression
	    (cons-expression-tags e) (second result1) (second result2)))))
   (else (internal-error)))))

;;; ANF conversion

(define (anf-result result)
 ;; needs work: Should have structure instead of list.
 (when (and (not (null? (fourth result)))
	    ;; needs work: to abstract this
	    (not
	     (null?
	      (rest
	       (remove-duplicates
		(map (lambda (b)
		      (lambda-expression-tags (variable-binding-expression b)))
		     (fourth result)))))))
  (internal-error))
 (new-letrec-expression
  (map variable-binding-variable (reverse (fourth result)))
  (map variable-binding-expression (reverse (fourth result)))
  (new-let* (map parameter-binding-parameter (reverse (third result)))
	    (map parameter-binding-expression (reverse (third result)))
	    (second result))))

(define (anf-max e)
 (cond
  ((constant-expression? e) 0)
  ((variable-access-expression? e)
   (variable-anf-max (variable-access-expression-variable e)))
  ((lambda-expression? e)
   (max (anf-max (lambda-expression-parameter e))
	(anf-max (lambda-expression-body e))))
  ((application? e)
   (max (anf-max (application-callee e)) (anf-max (application-argument e))))
  ((letrec-expression? e)
   (max (map-reduce
	 max 0 variable-anf-max (letrec-expression-procedure-variables e))
	(map-reduce max 0 anf-max (letrec-expression-lambda-expressions e))
	(anf-max (letrec-expression-body e))))
  ((cons-expression? e)
   (max (anf-max (cons-expression-car e)) (anf-max (cons-expression-cdr e))))
  (else (internal-error))))

(define (anf-convert e)
 ;; The soundness of our method for ANF conversion relies on two things:
 ;;  1. E must be alpha converted.
 ;;     This allows letrecs to be merged.
 ;;     It also allows let*s in expressions of let*s to be merged.
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 ;; needs work: Should have structure instead of list.
 (anf-result
  (let outer ((i (anf-max e)) (e e) (bs1 '()) (bs2 '()))
   (cond
    ;; needs work: This means that an anf-result can be a constant expression,
    ;;             as well as the RHS of a variable binding, the callee and
    ;;             argument of an application, and the car and cdr of a cons
    ;;             expression.
    ;; result
    ((constant-expression? e) (list i e bs1 bs2))
    ;; result
    ((variable-access-expression? e) (list i e bs1 bs2))
    ((lambda-expression? e)
     (let* ((result (outer i (lambda-expression-body e) '() '()))
	    (i (+ (first result) 1))
	    (p (make-variable-access-expression `(anf ,i))))
      ;; result
      (list i
	    p
	    (cons (make-parameter-binding
		   p
		   (new-lambda-expression
		    (lambda-expression-parameter e) (anf-result result)))
		  bs1)
	    bs2)))
    ((let*? e)
     (let inner ((i i)
		 (ps (let*-parameters e))
		 (es (let*-expressions e))
		 (bs1 bs1)
		 (bs2 bs2))
      (if (null? ps)
	  (outer i (let*-body e) bs1 bs2)
	  (let ((result (outer i (first es) bs1 bs2)))
	   (inner (first result)
		  (rest ps)
		  (rest es)
		  (cons (make-parameter-binding (first ps) (second result))
			(third result))
		  (fourth result))))))
    ((application? e)
     (let* ((result1 (outer i (application-callee e) bs1 bs2))
	    (result2 (outer (first result1)
			    (application-argument e)
			    (third result1)
			    (fourth result1)))
	    (i (+ (first result2) 1))
	    (p (make-variable-access-expression `(anf ,i))))
      ;; result
      (list i
	    p
	    (cons (make-parameter-binding
		   p (new-application (second result1) (second result2)))
		  (third result2))
	    (fourth result2))))
    ((letrec-expression? e)
     (let inner ((i i)
		 (xs (letrec-expression-procedure-variables e))
		 (es (letrec-expression-lambda-expressions e))
		 (bs2 bs2))
      (if (null? xs)
	  (outer i (letrec-expression-body e) bs1 bs2)
	  (let ((result (outer i (lambda-expression-body (first es)) '() '())))
	   (inner (first result)
		  (rest xs)
		  (rest es)
		  (cons (make-variable-binding
			 (first xs)
			 (new-lambda-expression
			  (lambda-expression-parameter (first es))
			  (anf-result result)))
			bs2))))))
    ((cons-expression? e)
     (let* ((result1 (outer i (cons-expression-car e) bs1 bs2))
	    (result2 (outer (first result1)
			    (cons-expression-cdr e)
			    (third result1)
			    (fourth result1)))
	    (i (+ (first result2) 1))
	    (p (make-variable-access-expression `(anf ,i))))
      ;; result
      (list
       i
       p
       (cons (make-parameter-binding
	      p
	      (new-cons-expression
	       (cons-expression-tags e) (second result1) (second result2)))
	     (third result2))
       (fourth result2))))
    (else (internal-error))))))

(define (anf-let*-parameters e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-parameters (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-parameters e) '())))

(define (anf-let*-expressions e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-expressions (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-expressions e) '())))

(define (anf-parameter e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-body (letrec-expression-body e))
	 (letrec-expression-body e))
     (if (let*? e) (let*-body e) e)))

;;; Concrete->Abstract

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (internalize v)
 (cond ((null? v) (vlad-empty-list))
       ((boolean? v) (if v (vlad-true) (vlad-false)))
       ((real? v) v)
       ((pair? v) (vlad-cons (internalize (car v)) (internalize (cdr v))))
       (else (internal-error))))

;;; needs work: to add bundle and *j parameters

(define (syntax-check-parameter! p)
 (cond
  ((boolean? p) (syntax-check-parameter! `',p))
  ((real? p) (syntax-check-parameter! `',p))
  ((variable? p)
   (unless (or (user-variable? p) *wizard?*)
    (compile-time-error "Invalid parameter: ~s" p))
   #f)
  ((and (list? p) (not (null? p)))
   (case (first p)
    ((quote) (unless (and (= (length p) 2) (value? (second p)))
	      (compile-time-error "Invalid parameter: ~s" p))
	     #f)
    ((cons)
     (unless (= (length p) 3) (compile-time-error "Invalid parameter: ~s" p))
     (syntax-check-parameter! (second p))
     (syntax-check-parameter! (third p)))
    ((cons*) (syntax-check-parameter! (macro-expand p)))
    ((list) (syntax-check-parameter! (macro-expand p)))
    (else (compile-time-error "Invalid parameter: ~s" p))))
  (else (compile-time-error "Invalid parameter: ~s" p))))

(define (macro-expand e)
 (if (and (list? e) (not (null? e)))
     (case (first e)
      ((lambda) (unless (and (= (length e) 3) (list? (second e)))
		 (compile-time-error "Invalid expression: ~s" e))
		(case (length (second e))
		 ((0) `(lambda ((cons* ,@(second e))) ,(third e)))
		 ((1) e)
		 (else `(lambda ((cons* ,@(second e))) ,(third e)))))
      ((let) (unless (and (= (length e) 3)
			  (list? (second e))
			  (every (lambda (b) (and (list? b) (= (length b) 2)))
				 (second e)))
	      (compile-time-error "Invalid expression: ~s" e))
	     `((lambda ,(map first (second e)) ,(third e))
	       ,@(map second (second e))))
      ((let*)
       (unless (and (= (length e) 3)
		    (list? (second e))
		    (every (lambda (b) (and (list? b) (= (length b) 2)))
			   (second e)))
	(compile-time-error "Invalid expression: ~s" e))
       (case (length (second e))
	((0) (third e))
	((1) `(let ,(second e) ,(third e)))
	(else
	 `(let (,(first (second e))) (let* ,(rest (second e)) ,(third e))))))
      ((if)
       (unless (= (length e) 4)
	(compile-time-error "Invalid expression: ~s" e))
       ;; needs work: to ensure that you don't shadow if-procedure
       `(if-procedure
	 ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))
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
	       (compile-time-error "Invalid expression: ~s" e))
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
	     (else
	      (let ((x (gensym)))
	       `(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e)))))))))
      (else (case (length (rest e))
	     ((0) `(,(first e) (cons* ,@(rest e))))
	     ((1) e)
	     (else `(,(first e) (cons* ,@(rest e)))))))
     e))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs (map value-binding-variable *value-bindings*)))
  (cond
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((variable? e)
    (unless (memp variable=? e xs)
     (compile-time-error "Unbound variable: ~s" e))
    #f)
   ((and (list? e) (not (null? e)))
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (compile-time-error "Invalid expression: ~s" e))
	      #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (compile-time-error "Invalid expression: ~s" e))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (syntax-check-parameter! (first (second e)))
	    (let ((xs0 (parameter-variables
			(concrete->abstract (first (second e))))))
	     (when (duplicatesp? variable=? xs0)
	      (compile-time-error "Duplicate variables: ~s" e))
	     (loop (third e) (append xs0 xs))))
       (else (loop (macro-expand e) xs))))
     ((letrec)
      (unless (and (= (length e) 3)
		   (list? (second e))
		   (every
		    (lambda (b)
		     (and (list? b) (= (length b) 2) (variable? (first b))))
		    (second e)))
       (compile-time-error "Invalid expression: ~s" e))
      (let ((xs0 (map first (second e))))
       (when (duplicatesp? variable=? xs0)
	(compile-time-error "Duplicate variables: ~s" e))
       (for-each
	(lambda (b)
	 (let ((e1 (macro-expand (second b))))
	  (unless (and (list? e1) (= (length e1) 3) (eq? (first e1) 'lambda))
	   (compile-time-error "Invalid expression: ~s" e))
	  (loop e1 (append xs0 xs))))
	(second e))
       (loop (third e) (append xs0 xs))))
     ((let) (loop (macro-expand e) xs))
     ((let*) (loop (macro-expand e) xs))
     ((if) (loop (macro-expand e) xs))
     ((cons)
      (unless (= (length e) 3) (compile-time-error "Invalid expression: ~s" e))
      (loop (second e) xs)
      (loop (third e) xs))
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
   (else (compile-time-error "Invalid expression: ~s" e)))))

(define (concrete->abstract e)
 (cond
  ((boolean? e) (concrete->abstract `',e))
  ((real? e) (concrete->abstract `',e))
  ((variable? e) (make-variable-access-expression e))
  ((and (list? e) (not (null? e)))
   (case (first e)
    ((quote) (make-constant-expression (internalize (second e))))
    ((lambda)
     (case (length (second e))
      ((0) (concrete->abstract (macro-expand e)))
      ((1) (new-lambda-expression (concrete->abstract (first (second e)))
				  (concrete->abstract (third e))))
      (else (concrete->abstract (macro-expand e)))))
    ((letrec) (create-letrec-expression
	       (map first (second e))
	       (map (lambda (b) (concrete->abstract (macro-expand (second b))))
		    (second e))
	       (concrete->abstract (third e))))
    ((let) (concrete->abstract (macro-expand e)))
    ((let*) (concrete->abstract (macro-expand e)))
    ((if) (concrete->abstract (macro-expand e)))
    ((cons) (create-cons-expression (concrete->abstract (second e))
				    (concrete->abstract (third e))))
    ((cons*) (concrete->abstract (macro-expand e)))
    ((list) (concrete->abstract (macro-expand e)))
    ((cond) (concrete->abstract (macro-expand e)))
    ((and) (concrete->abstract (macro-expand e)))
    ((or) (concrete->abstract (macro-expand e)))
    (else (case (length (rest e))
	   ((0) (concrete->abstract (macro-expand e)))
	   ((1) (new-application (concrete->abstract (first e))
				 (concrete->abstract (second e))))
	   (else (concrete->abstract (macro-expand e)))))))
  (else (internal-error))))

(define (parse e)
 (let* ((e (concrete->abstract e))
	(e (closure-convert e))
	(e (if #f			;debugging
	       (anf-convert
		(second (alpha-convert-expression e (free-variables e))))
	       e)))
  (list e
	(map (lambda (x)
	      (find-if (lambda (b) (variable=? x (value-binding-variable b)))
		       *value-bindings*))
	     (free-variables e)))))

;;; AD

(define (zero v)
 (cond ((vlad-empty-list? v) v)
       ((abstract-boolean? v) v)
       ((abstract-real? v) 0)
       ((primitive-procedure? v) v)
       ((nonrecursive-closure? v)
	;; See the note in abstract-environment=?.
	(new-nonrecursive-closure (map zero (nonrecursive-closure-values v))
				  (nonrecursive-closure-lambda-expression v)))
       ((recursive-closure? v)
	;; See the note in abstract-environment=?.
	(new-recursive-closure (map zero (recursive-closure-values v))
			       (recursive-closure-procedure-variables v)
			       (recursive-closure-lambda-expressions v)
			       (recursive-closure-index v)))
       ((bundle? v)
	(make-bundle (zero (bundle-primal v)) (zero (bundle-tangent v))))
       ((reverse-tagged-value? v)
	(make-reverse-tagged-value (zero (reverse-tagged-value-primal v))))
       ((tagged-pair? v)
	(new-tagged-pair (tagged-pair-tags v)
			 (zero (tagged-pair-car v))
			 (zero (tagged-pair-cdr v))))
       (else (internal-error))))

;;; Forward Mode

(define (forward-transform e)
 (cond ((constant-expression? e)
	(make-constant-expression
	 (bundle (constant-expression-value e)
		 (zero (constant-expression-value e)))))
       ((variable-access-expression? e) (forwardify-access e))
       ((lambda-expression? e)
	(new-lambda-expression
	 (forward-transform (lambda-expression-parameter e))
	 (forward-transform (lambda-expression-body e))))
       ((application? e)
	(new-application (forward-transform (application-callee e))
			 (forward-transform (application-argument e))))
       ((letrec-expression? e)
	(new-letrec-expression
	 (map forwardify (letrec-expression-procedure-variables e))
	 (map forward-transform (letrec-expression-lambda-expressions e))
	 (forward-transform (letrec-expression-body e))))
       ((cons-expression? e)
	(new-cons-expression (add-tag 'forward (cons-expression-tags e))
			     (forward-transform (cons-expression-car e))
			     (forward-transform (cons-expression-cdr e))))
       (else (internal-error))))

(define (forward-transform-inverse e)
 (cond
  ((constant-expression? e)
   (make-constant-expression (primal (constant-expression-value e))))
  ((variable-access-expression? e) (unforwardify-access e))
  ((lambda-expression? e)
   (new-lambda-expression
    (forward-transform-inverse (lambda-expression-parameter e))
    (forward-transform-inverse (lambda-expression-body e))))
  ((application? e)
   (new-application (forward-transform-inverse (application-callee e))
		    (forward-transform-inverse (application-argument e))))
  ((letrec-expression? e)
   (new-letrec-expression
    (map unforwardify (letrec-expression-procedure-variables e))
    (map forward-transform-inverse (letrec-expression-lambda-expressions e))
    (forward-transform-inverse (letrec-expression-body e))))
  ((cons-expression? e)
   (unless (tagged? 'forward (cons-expression-tags e)) (internal-error))
   (new-cons-expression (remove-tag 'forward (cons-expression-tags e))
			(forward-transform-inverse (cons-expression-car e))
			(forward-transform-inverse (cons-expression-cdr e))))
  (else (internal-error))))

(define (primal v-forward)
 (let ((b (find-if (lambda (b)
		    (abstract-value=? v-forward
				      (primitive-procedure-forward
				       (vlad-cdr (value-binding-value b)))))
		   *value-bindings*)))
  (if b
      (value-binding-value b)
      (cond
       ((vlad-empty-list? v-forward)
	(run-time-error
	 "Attempt to take primal of a non-forward value" v-forward))
       ((abstract-boolean? v-forward)
	(run-time-error
	 "Attempt to take primal of a non-forward value" v-forward))
       ((abstract-real? v-forward)
	(run-time-error
	 "Attempt to take primal of a non-forward value" v-forward))
       ((primitive-procedure? v-forward)
	(run-time-error
	 "Attempt to take primal of a non-forward value" v-forward))
       ((nonrecursive-closure? v-forward)
	(unless (forward-parameter? (nonrecursive-closure-parameter v-forward))
	 (run-time-error
	  "Attempt to take primal of a non-forward value" v-forward))
	;; See the note in abstract-environment=?.
	(new-nonrecursive-closure
	 (map primal (nonrecursive-closure-values v-forward))
	 (forward-transform-inverse
	  (nonrecursive-closure-lambda-expression v-forward))))
       ((recursive-closure? v-forward)
	(unless (forward-parameter? (recursive-closure-parameter v-forward))
	 (run-time-error
	  "Attempt to take primal of a non-forward value" v-forward))
	;; See the note in abstract-environment=?.
	(new-recursive-closure
	 (map primal (recursive-closure-values v-forward))
	 (map-vector unforwardify
		     (recursive-closure-procedure-variables v-forward))
	 (map-vector forward-transform-inverse
		     (recursive-closure-lambda-expressions v-forward))
	 (recursive-closure-index v-forward)))
       ((bundle? v-forward) (bundle-primal v-forward))
       ((reverse-tagged-value? v-forward)
	(run-time-error
	 "Attempt to take primal of a non-forward value" v-forward))
       ((tagged-pair? v-forward)
	(unless (tagged? 'forward (tagged-pair-tags v-forward))
	 (run-time-error
	  "Attempt to take primal of a non-forward value" v-forward))
	(new-tagged-pair (remove-tag 'forward (tagged-pair-tags v-forward))
			 (primal (tagged-pair-car v-forward))
			 (primal (tagged-pair-cdr v-forward))))
       (else (internal-error))))))

(define (tangent v-forward)
 (let ((b (find-if (lambda (b)
		    (abstract-value=? v-forward
				      (primitive-procedure-forward
				       (vlad-cdr (value-binding-value b)))))
		   *value-bindings*)))
  (if b
      (value-binding-value b)
      (cond
       ((vlad-empty-list? v-forward)
	(run-time-error
	 "Attempt to take tangent of a non-forward value" v-forward))
       ((abstract-boolean? v-forward)
	(run-time-error
	 "Attempt to take tangent of a non-forward value" v-forward))
       ((abstract-real? v-forward)
	(run-time-error
	 "Attempt to take tangent of a non-forward value" v-forward))
       ((primitive-procedure? v-forward)
	(run-time-error
	 "Attempt to take tangent of a non-forward value" v-forward))
       ((nonrecursive-closure? v-forward)
	(unless (forward-parameter? (nonrecursive-closure-parameter v-forward))
	 (run-time-error
	  "Attempt to take tangent of a non-forward value" v-forward))
	;; See the note in abstract-environment=?.
	(new-nonrecursive-closure
	 (map tangent (nonrecursive-closure-values v-forward))
	 (forward-transform-inverse
	  (nonrecursive-closure-lambda-expression v-forward))))
       ((recursive-closure? v-forward)
	(unless (forward-parameter? (recursive-closure-parameter v-forward))
	 (run-time-error
	  "Attempt to take tangent of a non-forward value" v-forward))
	;; See the note in abstract-environment=?.
	(new-recursive-closure
	 (map tangent (recursive-closure-values v-forward))
	 (map-vector unforwardify
		     (recursive-closure-procedure-variables v-forward))
	 (map-vector forward-transform-inverse
		     (recursive-closure-lambda-expressions v-forward))
	 (recursive-closure-index v-forward)))
       ((bundle? v-forward) (bundle-tangent v-forward))
       ((reverse-tagged-value? v-forward)
	(run-time-error
	 "Attempt to take tangent of a non-forward value" v-forward))
       ((tagged-pair? v-forward)
	(unless (tagged? 'forward (tagged-pair-tags v-forward))
	 (run-time-error
	  "Attempt to take tangent of a non-forward value" v-forward))
	(new-tagged-pair (remove-tag 'forward (tagged-pair-tags v-forward))
			 (tangent (tagged-pair-car v-forward))
			 (tangent (tagged-pair-cdr v-forward))))
       (else (internal-error))))))

(define (legitimate? v v-perturbation)
 (or (and (vlad-empty-list? v) (vlad-empty-list? v-perturbation))
     ;; It might not be legitimate if one or both arguments is B.
     (and (abstract-boolean? v)
	  (abstract-boolean? v-perturbation)
	  (or (eq? v 'boolean)
	      (eq? v-perturbation 'boolean)
	      (and (vlad-true? v) (vlad-true? v-perturbation))
	      (and (vlad-false? v) (vlad-false? v-perturbation))))
     (and (abstract-real? v) (abstract-real? v-perturbation))
     (and (primitive-procedure? v)
	  (primitive-procedure? v-perturbation)
	  (eq? v v-perturbation))
     (and (nonrecursive-closure? v)
	  (nonrecursive-closure? v-perturbation)
	  (nonrecursive-closure-match? v v-perturbation)
	  ;; See the note in abstract-environment=?.
	  (every legitimate?
		 (nonrecursive-closure-values v)
		 (nonrecursive-closure-values v-perturbation)))
     (and (recursive-closure? v)
	  (recursive-closure? v-perturbation)
	  (recursive-closure-match? v v-perturbation)
	  ;; See the note in abstract-environment=?.
	  (every legitimate?
		 (recursive-closure-values v)
		 (recursive-closure-values v-perturbation)))
     (and (bundle? v)
	  (bundle? v-perturbation)
	  (legitimate? (bundle-primal v) (bundle-primal v-perturbation))
	  (legitimate? (bundle-tangent v) (bundle-tangent v-perturbation)))
     (and (reverse-tagged-value? v)
	  (reverse-tagged-value? v-perturbation)
	  (legitimate? (reverse-tagged-value-primal v)
		       (reverse-tagged-value-primal v-perturbation)))
     (and (tagged-pair? v)
	  (tagged-pair? v-perturbation)
	  (equal-tags? (tagged-pair-tags v) (tagged-pair-tags v-perturbation))
	  (legitimate? (tagged-pair-car v) (tagged-pair-car v-perturbation))
	  (legitimate? (tagged-pair-cdr v) (tagged-pair-cdr v-perturbation)))))

(define (bundle-internal v v-perturbation)
 (let ((b (find-if (lambda (b) (abstract-value=? v (value-binding-value b)))
		   *value-bindings*)))
  (if b
      (primitive-procedure-forward (vlad-cdr (value-binding-value b)))
      (cond
       ((vlad-empty-list? v) (make-bundle v v-perturbation))
       ((abstract-boolean? v) (make-bundle v v-perturbation))
       ((abstract-real? v) (make-bundle v v-perturbation))
       ((primitive-procedure? v) (internal-error))
       ((nonrecursive-closure? v)
	;; See the note in abstract-environment=?.
	(new-nonrecursive-closure
	 (map bundle-internal
	      (nonrecursive-closure-values v)
	      (nonrecursive-closure-values v-perturbation))
	 (forward-transform (nonrecursive-closure-lambda-expression v))))
       ((recursive-closure? v)
	;; See the note in abstract-environment=?.
	(new-recursive-closure
	 (map bundle-internal
	      (recursive-closure-values v)
	      (recursive-closure-values v-perturbation))
	 (map-vector forwardify (recursive-closure-procedure-variables v))
	 (map-vector forward-transform
		     (recursive-closure-lambda-expressions v))
	 (recursive-closure-index v)))
       ((bundle? v) (make-bundle v v-perturbation))
       ((reverse-tagged-value? v) (make-bundle v v-perturbation))
       ((tagged-pair? v)
	(new-tagged-pair
	 (add-tag 'forward (tagged-pair-tags v))
	 (bundle-internal (tagged-pair-car v) (tagged-pair-car v-perturbation))
	 (bundle-internal
	  (tagged-pair-cdr v) (tagged-pair-cdr v-perturbation))))
       (else (internal-error))))))

(define (bundle v v-perturbation)
 (unless (legitimate? v v-perturbation)
  (run-time-error "The arguments to bundle are illegitimate" v v-perturbation))
 (bundle-internal v v-perturbation))

;;; Reverse Mode

(define (added-variable x)
 (make-constant-expression
  (value-binding-value
   (find-if (lambda (b) (variable=? x (value-binding-variable b)))
	    *value-bindings*))))

;;; needs work: closure conversion of primitives
(define (make-zero e) (new-application (added-variable 'zero) e))

;;; needs work: closure conversion of primitives
(define (make-plus e1 e2)
 (new-application (added-variable 'plus) (create-cons-expression e1 e2)))

(define (make-plus-binding p e) (make-parameter-binding p (make-plus p e)))

;;; needs work: closure conversion of primitives
(define (make-*j-inverse e) (new-application (added-variable '*j-inverse) e))

(define (reverse-transform e gs zs)
 ;; e  is a lambda expression. Its body is in anf. Its body is a letrec
 ;;    expression, unless it has been optimized away.
 ;; fs is the procedure variables of the body of e, when it is a letrec
 ;;    expression. Otherwise it is empty.
 ;; ws is the recursive closure free variables of the body of e, when it is a
 ;;    letrec expression. Otherwise it is empty.
 ;; gs is the surrounding procedure variables when e is a letrec expression
 ;;    lambda expression or a recursive closure lambda expression. Otherwise
 ;;    it is empty.
 ;; zs is the surrounding recursive closure free variables if e is a letrec
 ;;    expression lambda expression or a recursive closure lambda expression.
 ;;    Otherwise it is the free variables.
 (let* ((tags (lambda-expression-tags e))
	(p (lambda-expression-parameter e))
	(e1 (lambda-expression-body e))
	(fs (if (letrec-expression? e1)
		(letrec-expression-procedure-variables e1)
		'()))
	(ws (if (letrec-expression? e1)
		(recursive-closure-free-variables
		 (letrec-expression-procedure-variables e1)
		 (letrec-expression-lambda-expressions e1))
		'())))
  (new-lambda-expression
   ;; needs work: p might not be a variable access parameter
   (reverseify-access p)
   (new-letrec-expression
    (map reverseify fs)
    (map (lambda (e) (reverse-transform e fs ws))
	 (if (letrec-expression? e1)
	     (letrec-expression-lambda-expressions e1)
	     '()))
    (create-let*
     ;; These are the bindings for the forward phase that come from the primal.
     (map
      (lambda (p e)
       (cond
	((constant-expression? e) 'needs-work) ;needs work
	;;            /   /
	;;            _   _
	;; p = e -~-> p = e
	((variable-access-expression? e)
	 (make-parameter-binding (reverseify-access p) (reverseify-access e)))
	;;                /   /
	;;                _   ______
	;; p = \ x e -~-> p = \ x e
	((lambda-expression? e)
	 (make-parameter-binding
	  (reverseify-access p) (reverse-transform e '() (free-variables e))))
	;;                /      /  /
	;;                _  _   __ __
	;; p = x1 x2 -~-> p, p = x1 x2
	((application? e)
	 (make-parameter-binding
	  (create-cons-expression (reverseify-access p)
				  (backpropagatorify-access p))
	  (new-application (reverseify-access (application-callee e))
			   (reverseify-access (application-argument e)))))
	;;                /   /  / /
	;;                _   __ _ __
	;; p = x1,x2 -~-> p = x1 , x2
	((cons-expression? e)
	 (make-parameter-binding
	  (reverseify-access p)
	  (new-cons-expression (add-tag 'reverse (cons-expression-tags e))
			       (reverseify-access (cons-expression-car e))
			       (reverseify-access (cons-expression-cdr e)))))
	(else (internal-error))))
      (anf-let*-parameters e1)
      (anf-let*-expressions e1))
     ;; This conses the result of the forward phase with the backpropagator.
     (create-cons-expression
      ;; This is the result of the forward phase.
      (reverseify-access (anf-parameter e1))
      ;; This is the backpropagator.
      (new-lambda-expression
       (sensitivityify-access (anf-parameter e1))
       (create-let*
	(append
	 ;; These are the zeroing bindings for the reverse phase.
	 (map
	  (lambda (x)
	   (make-parameter-binding
	    (sensitivity-access x)
	    (make-zero (make-*j-inverse (reverse-access x)))))
	  (removep
	   variable=?
	   (variable-access-expression-variable (anf-parameter e1))
	   ;; needs work: p might not be a variable access parameter
	   (cons (variable-access-expression-variable p)
		 (append (map variable-access-expression-variable
			      (anf-let*-parameters e1))
			 fs
			 gs
			 zs))))
	 ;; These are the bindings for the reverse phase that come from the
	 ;; primal.
	 (map
	  (lambda (p e)
	   (cond
	    ((constant-expression? e) 'needs-work) ;needs work
	    ;;            _    _
	    ;;            \    \
	    ;; p = e -~-> e += p
	    ((variable-access-expression? e)
	     ;; needs work: only create binding if e is needed
	     (make-plus-binding
	      (sensitivityify-access e) (sensitivityify-access p)))
	    ;;                _____    _
	    ;;                \        \
	    ;; p = \ x e -~-> \ x e += p
	    ((lambda-expression? e)
	     ;; needs work: only create bindings for those free variables of
	     ;;             e, i.e. \ x e that are needed
	     (make-plus-binding
	      ;; needs work: sensitivity transform
	      (sensitivity-transform e) (sensitivityify-access p)))
	    ;;                __ _ __    _ _
	    ;;                \  \ \       \
	    ;; p = x1 x2 -~-> x1 , x2 += p p
	    ;; We want the x1,x2 inside the sensitivity so that the aggregate
	    ;; is a sensitivity that can be added by plus, since for type
	    ;; correctness, plus adds only sensitivities.
	    ((application? e)
	     ;; needs work: only create bindings for x1 and/or x2 if they are
	     ;;             needed
	     (make-plus-binding
	      (new-cons-expression
	       (add-tag 'sensitivity (empty-tags))
	       (sensitivityify-access (application-callee e))
	       (sensitivityify-access (application-argument e)))
	      (new-application (backpropagatorify-access p)
			       (sensitivityify-access p))))
	    ;;                __ _ __    _
	    ;;                \  \ \     \
	    ;; p = x1,x2 -~-> x1 , x2 += p
	    ;; We want the x1,x2 inside the sensitivity so that the aggregate
	    ;; is a sensitivity that can be added by plus, since for type
	    ;; correctness, plus adds only sensitivities.
	    ((cons-expression? e)
	     ;; needs work: only create bindings for x1 and/or x2 if they are
	     ;;             needed
	     (make-plus-binding
	      (new-cons-expression
	       (add-tag 'sensitivity (cons-expression-tags e))
	       (sensitivityify-access (cons-expression-car e))
	       (sensitivityify-access (cons-expression-cdr e)))
	      (sensitivityify-access p)))
	    (else (internal-error))))
	  (reverse (anf-let*-parameters e1))
	  (reverse (anf-let*-expressions e1)))
	 ;; needs work: I don't remember what this is.
	 ;; here I am
	 (make-list-bindings
	  tags
	  ;; needs work: ws
	  (map sensitivityify ws)
	  ;; needs work: fs, ws
	  (let loop ((fs fs))
	   (if (null? fs)
	       (make-list-invocation tags (map sensitivity-access ws))
	       (make-plus (sensitivity-access (first fs)) (loop (rest fs)))))))
	;; This conses the sensitivity to the target with the sensitivity to
	;; the argument.
	(new-cons-expression
	 (add-tag 'sensitivity (empty-tags))
	 ;; This is the sensitivity to the target.
	 ;; here I am
	 ;; needs work: gs, zs
	 (let loop ((gs gs))
	  (if (null? gs)
	      ;; needs work: This is not a list anymore.
	      (make-list-invocation tags (map sensitivity-access zs))
	      (make-plus (sensitivity-access (first gs)) (loop (rest gs)))))
	 ;; This is the sensitivity to the argument.
	 ;; needs work: p might not be a variable access parameter
	 (sensitivityify-access p))))))))))

;;; here I am

(define (result-cons-expression? x1 x2 e1 e2 e)
 ;; x1=(lambda ...)
 ;; x2=cons xa x1
 ;; in x2 end
 ;; ----------------------------------------------------------------
 ;; in xa end
 (and
  ;; We don't check that this lambda expression is the proper backpropagator
  ;; for the primal.
  (lambda-expression? e1)
  (cons-expression? e2)
  (empty-tags? (cons-expression-tags e2))
  ;; Technically not needed since in ANF.
  (variable-access-expression? (cons-expression-car e2))
  ;; Technically not needed since in ANF.
  (variable-access-expression? (cons-expression-cdr e2))
  (variable=?
   (variable-access-expression-variable (cons-expression-cdr e2)) x1)
  ;; Technically not needed since in ANF.
  (variable-access-expression? e)
  (variable=? (variable-access-expression-variable e) x2)))

(define (reverse-transform-inverse-internal e)
 (unless (let*? e) (internal-error))
 (let loop ((xs (let*-parameters e))
	    (es (let*-expressions e))
	    (xs0 '())
	    (es0 '()))
  (cond
   ((null? xs) (internal-error))
   ((and (= (length xs) 2)
	 (result-cons-expression?
	  (first xs) (second xs) (first es) (second es) (let*-body e)))
    (if (null? xs0)
	(unreverseify-access (cons-expression-car (second es)))
	(new-let* (reverse xs0)
		  (reverse es0)
		  (unreverseify-access (cons-expression-car (second es))))))
   ((constant-expression? (first es)) 'needs-work) ;needs work
   ((variable-access-expression? (first es))
    (loop (rest xs)
	  (rest es)
	  (cons (unreverseify (first xs)) xs0)
	  (cons (unreverseify-access (first es)) es0)))
   ((lambda-expression? (first es))
    (loop (rest xs)
	  (rest es)
	  (cons (unreverseify (first xs)) xs0)
	  (cons (reverse-transform-inverse (first es)) es0)))
   ((cons-expression? (first es))
    (loop (rest xs)
	  (rest es)
	  (cons (unreverseify (first xs)) xs0)
	  (cons (new-cons-expression
		 (remove-tag 'reverse (cons-expression-tags (first es)))
		 (unreverseify-access (cons-expression-car (first es)))
		 (unreverseify-access (cons-expression-cdr (first es))))
		es0)))
   (else (internal-error)))))

(define (reverse-transform-inverse e)
 (new-lambda-expression
  (reverse-transform-inverse (lambda-expression-parameter e))
  (let ((e (lambda-expression-body e)))
   (if (letrec-expression? e)
       (new-letrec-expression
	(map unreverseify (letrec-expression-procedure-variables e))
	(map reverse-transform-inverse
	     (letrec-expression-lambda-expressions e))
	(reverse-transform-inverse-internal (letrec-expression-body e)))
       (reverse-transform-inverse-internal e)))))

(define (conform? v1 v2)
 (or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
     ;; It might not conform if one or both arguments is B.
     (and (abstract-boolean? v1)
	  (abstract-boolean? v1)
	  (or (eq? v1 'boolean)
	      (eq? v2 'boolean)
	      (and (vlad-true? v1) (vlad-true? v2))
	      (and (vlad-false? v1) (vlad-false? v2))))
     (and (abstract-real? v1) (abstract-real? v2))
     (and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (nonrecursive-closure-match? v1 v2)
	  ;; See the note in abstract-environment=?.
	  (every conform?
		 (nonrecursive-closure-values v1)
		 (nonrecursive-closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (recursive-closure-match? v1 v2)
	  ;; See the note in abstract-environment=?.
	  (every conform?
		 (recursive-closure-values v1)
		 (recursive-closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (conform? (bundle-primal v1) (bundle-primal v2))
	  (conform? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (conform? (reverse-tagged-value-primal v1)
		    (reverse-tagged-value-primal v2)))
     (and (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (conform? (tagged-pair-car v1) (tagged-pair-car v2))
	  (conform? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))))

(define (plus-internal v1 v2)
 (cond ((vlad-empty-list? v1) v1)
       ((abstract-boolean? v1) (if (eq? v1 'boolean) v2 v1))
       ((eq? v1 'real) 'real)
       ((eq? v2 'real) 'real)
       ((abstract-real? v1) (+ v1 v2))
       ((primitive-procedure? v1) v1)
       ((nonrecursive-closure? v1)
	;; See the note in abstract-environment=?.
	(new-nonrecursive-closure
	 (map plus-internal
	      (nonrecursive-closure-values v1)
	      (nonrecursive-closure-values v2))
	 (nonrecursive-closure-lambda-expression v1)))
       ((recursive-closure? v1)
	;; See the note in abstract-environment=?.
	(new-recursive-closure
	 (map plus-internal
	      (recursive-closure-values v1)
	      (recursive-closure-values v2))
	 (recursive-closure-procedure-variables v1)
	 (recursive-closure-lambda-expressions v1)
	 (recursive-closure-index v1)))
       ((bundle? v1)
	(make-bundle (plus-internal (bundle-primal v1) (bundle-primal v2))
		     (plus-internal (bundle-tangent v1) (bundle-tangent v2))))
       ((reverse-tagged-value? v1)
	(make-reverse-tagged-value
	 (plus-internal (reverse-tagged-value-primal v1)
			(reverse-tagged-value-primal v2))))
       ((tagged-pair? v1)
	(new-tagged-pair
	 (tagged-pair-tags v1)
	 (plus-internal (tagged-pair-car v1) (tagged-pair-car v2))
	 (plus-internal (tagged-pair-cdr v1) (tagged-pair-cdr v2))))
       (else (internal-error))))

(define (plus v1 v2)
 (unless (conform? v1 v2)
  (run-time-error "The arguments to plus are nonconformant" v1 v2))
 (plus-internal v1 v2))

(define (*j v)
 (let ((b (find-if (lambda (b) (abstract-value=? v (value-binding-value b)))
		   *value-bindings*)))
  (if b
      (primitive-procedure-reverse (vlad-cdr (value-binding-value b)))
      (cond ((vlad-empty-list? v) (make-reverse-tagged-value v))
	    ((abstract-boolean? v) (make-reverse-tagged-value v))
	    ((abstract-real? v) (make-reverse-tagged-value v))
	    ((primitive-procedure? v) (internal-error))
	    ((nonrecursive-closure? v)
	     ;; See the note in abstract-environment=?.
	     (new-nonrecursive-closure
	      (map *j (nonrecursive-closure-values v))
	      (let ((e (reverse-transform
			(nonrecursive-closure-lambda-expression v)
			'()
			(nonrecursive-closure-variables v))))
	       (anf-convert
		(second (alpha-convert-expression e (free-variables e)))))))
	    ((recursive-closure? v)
	     ;; See the note in abstract-environment=?.
	     (new-recursive-closure
	      (map *j (recursive-closure-values v))
	      (map-vector reverseify (recursive-closure-procedure-variables v))
	      (let* ((es (map-vector
			  (lambda (e)
			   (reverse-transform
			    e
			    (vector->list
			     (recursive-closure-procedure-variables v))
			    (recursive-closure-variables v)))
			  (recursive-closure-lambda-expressions v)))
		     (xs (map-reduce union-variables
				     '()
				     free-variables
				     (vector->list es))))
	       (map-vector
		(lambda (e)
		 (anf-convert (second (alpha-convert-expression e xs))))
		es))
	      (recursive-closure-index v)))
	    ((bundle? v) (make-reverse-tagged-value v))
	    ((reverse-tagged-value? v) (make-reverse-tagged-value v))
	    ((tagged-pair? v)
	     (new-tagged-pair (add-tag 'reverse (tagged-pair-tags v))
			      (*j (tagged-pair-car v))
			      (*j (tagged-pair-cdr v))))
	    (else (internal-error))))))

(define (*j-inverse v-reverse)
 (let ((b (find-if (lambda (b)
		    (abstract-value=? v-reverse
				      (primitive-procedure-reverse
				       (vlad-cdr (value-binding-value b)))))
		   *value-bindings*)))
  (if b
      (value-binding-value b)
      (cond ((vlad-empty-list? v-reverse)
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	    ((abstract-boolean? v-reverse)
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	    ((abstract-real? v-reverse)
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	    ((primitive-procedure? v-reverse)
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	    ((nonrecursive-closure? v-reverse)
	     (unless (tagged? 'reverse (nonrecursive-closure-tags v-reverse))
	      (run-time-error
	       "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	     ;; See the note in abstract-environment=?.
	     (new-nonrecursive-closure
	      (map *j-inverse (nonrecursive-closure-values v-reverse))
	      (reverse-transform-inverse
	       (nonrecursive-closure-lambda-expression v-reverse))))
	    ((recursive-closure? v-reverse)
	     (unless (tagged? 'reverse (recursive-closure-tags v-reverse))
	      (run-time-error
	       "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	     ;; See the note in abstract-environment=?.
	     (new-recursive-closure
	      (map *j-inverse (recursive-closure-values v-reverse))
	      (map-vector unreverseify
			  (recursive-closure-procedure-variables v-reverse))
	      (map-vector reverse-transform-inverse
			  (recursive-closure-lambda-expressions v-reverse))
	      (recursive-closure-index v-reverse)))
	    ((bundle? v-reverse)
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" v-reverse))
	    ((reverse-tagged-value? v-reverse)
	     (reverse-tagged-value-primal v-reverse))
	    ((tagged-pair? v-reverse)
	     (unless (tagged? 'reverse (tagged-pair-tags v-reverse))
	      (run-time-error
	       "Attempt to take primal of a non-reverse value" v-reverse))
	     (new-tagged-pair
	      (remove-tag 'reverse (tagged-pair-tags v-reverse))
	      (*j-inverse (tagged-pair-car v-reverse))
	      (*j-inverse (tagged-pair-cdr v-reverse))))
	    (else (internal-error))))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (abstract->concrete e)
 (cond
  ((let*? e)
   (let loop ((ps (let*-parameters e)) (es (let*-expressions e)) (bs '()))
    (if (null? ps)
	(case (length bs)
	 ((0) (internal-error))
	 ((1) `(let ,bs ,(abstract->concrete (let*-body e))))
	 (else `(let* ,(reverse bs) ,(abstract->concrete (let*-body e)))))
	(loop (rest ps)
	      (rest es)
	      (cons `(,(abstract->concrete(first ps))
		      ,(abstract->concrete (first es)))
		    bs)))))
  ;; needs work: This doesn't work for transformed values.
  ((constant-expression? e) `',(externalize (constant-expression-value e)))
  ((variable-access-expression? e) (variable-access-expression-variable e))
  ((lambda-expression? e)
   `(lambda (,(abstract->concrete (lambda-expression-parameter e)))
     ,(abstract->concrete (lambda-expression-body e))))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((letrec-expression? e)
   `(letrec ,(map (lambda (x e) `(,x ,(abstract->concrete e)))
		  (letrec-expression-procedure-variables e)
		  (letrec-expression-lambda-expressions e))
     ,(abstract->concrete (letrec-expression-body e))))
  ((cons-expression? e)
   (if (empty-tags? (cons-expression-tags e))
       `(cons ,(abstract->concrete (cons-expression-car e))
	      ,(abstract->concrete (cons-expression-cdr e)))
       `(cons ,(cons-expression-tags e)
	      ,(abstract->concrete (cons-expression-car e))
	      ,(abstract->concrete (cons-expression-cdr e)))))
  (else (internal-error))))

(define (quotable? v)
 (cond ((and (not *unabbreviate-transformed?*) (vlad-forward? v)) #f)
       ((and (not *unabbreviate-transformed?*) (vlad-reverse? v)) #f)
       ((vlad-empty-list? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((eq? v 'boolean) #f)
       ((real? v) #t)
       ((eq? v 'real) #f)
       ((vlad-pair? v) (and (quotable? (vlad-car v)) (quotable? (vlad-cdr v))))
       ((primitive-procedure? v) #f)
       ((closure? v) #f)
       ((bundle? v) #f)
       ((reverse-tagged-value? v) #f)
       ((abstract-top? v) #f)
       (else (internal-error))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(bundle ,(loop (primal v) quote?)
			   ,(loop (tangent v) quote?)))
		 (else `(forward ,(loop (primal v) quote?)
				 ,(loop (tangent v) quote?)))))
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(vlad-reverse? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(*j ,(loop (*j-inverse v) quote?)))
		 (else `(reverse ,(loop (*j-inverse v) quote?)))))
	  ((vlad-empty-list? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((vlad-true? v) #t)
	  ((vlad-false? v) #f)
	  ((eq? v 'boolean)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   'boolean)
	  ((real? v) v)
	  ((eq? v 'real)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   'real)
	  ((vlad-pair? v)
	   (if (and *unabbreviate-executably?* (not quote?))
	       (if (quotable? v)
		   `',(cons (loop (vlad-car v) #t) (loop (vlad-cdr v) #t))
		   `(cons ,(loop (vlad-car v) #f) ,(loop (vlad-cdr v) #f)))
	       (cons (loop (vlad-car v) quote?) (loop (vlad-cdr v) quote?))))
	  ((primitive-procedure? v)
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  (string->symbol
		   (string-append (symbol->string (primitive-procedure-name v))
				  (symbol->string '-primitive))))
		 (else (primitive-procedure-name v))))
	  ((nonrecursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (internal-error))
	     (case (length (nonrecursive-closure-variables v))
	      ((0)
	       (abstract->concrete (nonrecursive-closure-lambda-expression v)))
	      ((1) `(let ,(map (lambda (x v) `(,x ,(loop v quote?)))
			       (nonrecursive-closure-variables v)
			       (nonrecursive-closure-values v))
		     ,(abstract->concrete
		       (nonrecursive-closure-lambda-expression v))))
	      (else `(let ,(map (lambda (x v) `(,x ,(loop v quote?)))
				(nonrecursive-closure-variables v)
				(nonrecursive-closure-values v))
		      ,(abstract->concrete
			(nonrecursive-closure-lambda-expression v))))))
	    (*unabbreviate-nonrecursive-closures?*
	     `(nonrecursive-closure
	       ,(map (lambda (x v) `(,x ,(loop v quote?)))
		     (nonrecursive-closure-variables v)
		     (nonrecursive-closure-values v))
	       ,(abstract->concrete
		 (nonrecursive-closure-lambda-expression v))))
	    (else (abstract->concrete
		   (nonrecursive-closure-lambda-expression v)))))
	  ((recursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (internal-error))
	     (case (length (recursive-closure-variables v))
	      ((0) `(letrec ,(vector->list
			      (map-vector
			       (lambda (x e) `(,x ,(abstract->concrete e)))
			       (recursive-closure-procedure-variables v)
			       (recursive-closure-lambda-expressions v)))
		     ,(vector-ref (recursive-closure-procedure-variables v)
				  (recursive-closure-index v))))
	      ((1) `(let ,(map (lambda (x v) `(,x ,(loop v quote?)))
			       (recursive-closure-variables v)
			       (recursive-closure-values v))
		     (letrec ,(vector->list
			       (map-vector
				(lambda (x e) `(,x ,(abstract->concrete e)))
				(recursive-closure-procedure-variables v)
				(recursive-closure-lambda-expressions v)))
		      ,(vector-ref (recursive-closure-procedure-variables v)
				   (recursive-closure-index v)))))
	      (else `(let ,(map (lambda (x i) `(,x ,(loop v quote?)))
				(recursive-closure-variables v)
				(recursive-closure-values v))
		      (letrec ,(vector->list
				(map-vector
				 (lambda (x e) `(,x ,(abstract->concrete e)))
				 (recursive-closure-procedure-variables v)
				 (recursive-closure-lambda-expressions v)))
		       ,(vector-ref (recursive-closure-procedure-variables v)
				    (recursive-closure-index v)))))))
	    (*unabbreviate-recursive-closures?*
	     `(recursive-closure
	       ,(map (lambda (x i) `(,x ,(loop v quote?)))
		     (recursive-closure-variables v)
		     (recursive-closure-values v))
	       ,(vector->list
		 (map-vector (lambda (x e) `(,x ,(abstract->concrete e)))
			     (recursive-closure-procedure-variables v)
			     (recursive-closure-lambda-expressions v)))
	       ,(vector-ref (recursive-closure-procedure-variables v)
			    (recursive-closure-index v))))
	    (else (vector-ref (recursive-closure-procedure-variables v)
			      (recursive-closure-index v)))))
	  ((bundle? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(bundle ,(loop (bundle-primal v) quote?)
			   ,(loop (bundle-tangent v) quote?)))
		 (else `(forward ,(loop (bundle-primal v) quote?)
				 ,(loop (bundle-tangent v) quote?)))))
	  ((reverse-tagged-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (internal-error))
	     `(*j ,(loop (reverse-tagged-value-primal v) quote?)))
	    (else `(reverse ,(loop (reverse-tagged-value-primal v) quote?)))))
	  ((abstract-top? v)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   'top)
	  (else (internal-error))))))
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

(define (externalize-environment xs vs)
 (unless (and (list? vs) (= (length xs) (length vs)))
  (internal-error "Not an environment"))
 (map (lambda (x v) (list x (externalize v))) xs vs))

(define (externalize-environment-binding xs b)
 (unless (environment-binding? b)
  (internal-error "Not an environment binding"))
 (list (externalize-environment xs (environment-binding-values b))
       (externalize (environment-binding-value b))))

(define (externalize-flow xs bs)
 (unless (and (list? bs) (every environment-binding? bs))
  (internal-error "Not a flow"))
 (map (lambda (b) (externalize-environment-binding xs b)) bs))

(define (externalize-expression-binding b)
 (unless (expression-binding? b) (internal-error "Not an expression binding"))
 (list (abstract->concrete (expression-binding-expression b))
       (externalize-flow (free-variables (expression-binding-expression b))
			 (expression-binding-flow b))))

(define (externalize-analysis bs)
 (unless (and (list? bs) (every expression-binding? bs))
  (internal-error "Not an analysis"))
 (map externalize-expression-binding bs))

;;; Concrete Evaluator

(define (with-write-level n thunk)
 (let ((m (write-level)))
  (set-write-level! n)
  (thunk)
  (set-write-level! m)))

(define (with-write-length n thunk)
 (let ((m (write-length)))
  (set-write-length! n)
  (thunk)
  (set-write-length! m)))

(define (tag-check? v1 v2) (prefix-tags? (value-tags v1) (value-tags v2)))

;;; Environment Restriction/Construction

(define (restrict-environment vs e f)
 (map (lambda (x) (list-ref vs (positionp variable=? x (free-variables e))))
      (free-variables (f e))))

(define (letrec-restrict-environment vs e)
 (map (lambda (x) (list-ref vs (positionp variable=? x (free-variables e))))
      (recursive-closure-free-variables
       (letrec-expression-procedure-variables e)
       (letrec-expression-lambda-expressions e))))

(define (letrec-nested-environment vs e)
 (map (lambda (x)
       (if (memp variable=? x (letrec-expression-procedure-variables e))
	   (new-recursive-closure
	    (letrec-restrict-environment vs e)
	    (list->vector (letrec-expression-procedure-variables e))
	    (list->vector (letrec-expression-lambda-expressions e))
	    (positionp variable=? x (letrec-expression-procedure-variables e)))
	   (list-ref vs (positionp variable=? x (free-variables e)))))
      (free-variables (letrec-expression-body e))))

(define (destructure p v)
 (cond ((constant-expression? p)
	(unless (abstract-value=? (constant-expression-value p) v)
	 (run-time-error
	  "Argument is not a matching value" (constant-expression-value p) v))
	'())
       ((variable-access-expression? p)
	(list (cons (variable-access-expression-variable p) v)))
       ((cons-expression? p)
	(unless (and (tagged-pair? v)
		     (prefix-tags? (cons-expression-tags p)
				   (tagged-pair-tags v)))
	 (when #f			;debugging
	  (run-time-error
	   (format #f "Argument is not a matching tagged pair with tags ~s"
		   (cons-expression-tags p))
	   v)))
	(append (destructure (cons-expression-car p) (tagged-pair-car v))
		(destructure (cons-expression-cdr p) (tagged-pair-cdr v))))
       (else (internal-error))))

(define (construct-nonrecursive-environment v1 v2)
 (let ((alist (destructure (nonrecursive-closure-parameter v1) v2)))
  (map
   (lambda (x)
    (let ((result (assp variable=? x alist)))
     (if result
	 (cdr result)
	 (list-ref
	  (nonrecursive-closure-values v1)
	  (positionp variable=? x (nonrecursive-closure-variables v1))))))
   (free-variables
    (lambda-expression-body (nonrecursive-closure-lambda-expression v1))))))

(define (construct-recursive-environment v1 v2)
 (let ((alist (destructure (recursive-closure-parameter v1) v2)))
  (map (lambda (x)
	(let ((result (assp variable=? x alist)))
	 (cond
	  (result (cdr result))
	  ((some-vector (lambda (x1) (variable=? x x1))
			(recursive-closure-procedure-variables v1))
	   (new-recursive-closure
	    (recursive-closure-values v1)
	    (recursive-closure-procedure-variables v1)
	    (recursive-closure-lambda-expressions v1)
	    (positionp-vector
	     variable=? x (recursive-closure-procedure-variables v1))))
	  (else (list-ref
		 (recursive-closure-values v1)
		 (positionp variable=? x (recursive-closure-variables v1)))))))
       (free-variables (lambda-expression-body
			(vector-ref (recursive-closure-lambda-expressions v1)
				    (recursive-closure-index v1)))))))

;;; needs work: This evaluator is not tail recursive.

(define (concrete-apply v1 v2)
 (unless (vlad-procedure? v1) (run-time-error "Target is not a procedure" v1))
 (when #f				;debugging
  (unless (tag-check? v1 v2)
   (run-time-error "Argument has wrong type for target" v1 v2)))
 (set! *stack* (cons (list v1 v2) *stack*))
 (when (cond ((primitive-procedure? v1) *trace-primitive-procedures?*)
	     ((nonrecursive-closure? v1) *trace-nonrecursive-closures?*)
	     ((recursive-closure? v1) *trace-recursive-closures?*)
	     (else (internal-error)))
  (if *trace-argument/result?*
      (format #t "~aentering ~s ~s~%"
	      (make-string *trace-level* #\space)
	      (externalize v1)
	      (externalize v2))
      (format #t "~aentering ~s~%"
	      (make-string *trace-level* #\space)
	      (externalize v1)))
  (set! *trace-level* (+ *trace-level* 1)))
 (when (and *metered?* (primitive-procedure? v1))
  (set-primitive-procedure-meter!
   v1 (+ (primitive-procedure-meter v1) 1)))
 (let ((result
	(cond
	 ((primitive-procedure? v1) ((primitive-procedure-procedure v1) v2 #f))
	 ((nonrecursive-closure? v1)
	  (concrete-eval
	   (lambda-expression-body (nonrecursive-closure-lambda-expression v1))
	   (construct-nonrecursive-environment v1 v2)))
	 ((recursive-closure? v1)
	  (concrete-eval (lambda-expression-body
			  (vector-ref (recursive-closure-lambda-expressions v1)
				      (recursive-closure-index v1)))
			 (construct-recursive-environment v1 v2)))
	 (else (internal-error)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? v1) *trace-primitive-procedures?*)
	      ((nonrecursive-closure? v1) *trace-nonrecursive-closures?*)
	      ((recursive-closure? v1) *trace-recursive-closures?*)
	      (else (internal-error)))
   (set! *trace-level* (- *trace-level* 1))
   (if *trace-argument/result?*
       (format #t "~aexiting ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize v1)
	       (externalize result))
       (format #t "~aexiting ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize v1))))
  result))

(define (concrete-eval e vs)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e) (first vs))
  ((lambda-expression? e) (new-nonrecursive-closure vs e))
  ((application? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((v1 (concrete-eval (application-callee e)
			     (restrict-environment vs e application-callee)))
	  (v2 (concrete-eval
	       (application-argument e)
	       (restrict-environment vs e application-argument))))
    (concrete-apply v1 v2)))
  ((letrec-expression? e)
   (concrete-eval (letrec-expression-body e) (letrec-nested-environment vs e)))
  ((cons-expression? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((v1 (concrete-eval (cons-expression-car e)
			     (restrict-environment vs e cons-expression-car)))
	  (v2 (concrete-eval (cons-expression-cdr e)
			     (restrict-environment vs e cons-expression-cdr))))
    (when #f				;debugging
     (unless (prefix-tags? (cons-expression-tags e) (value-tags v1))
      (run-time-error
       (format #f "CAR argument has wrong type for target with tags ~s"
	       (cons-expression-tags e))
       v1))
     (unless (prefix-tags? (cons-expression-tags e) (value-tags v2))
      (run-time-error
       (format #f "CDR argument has wrong type for target with tags ~s"
	       (cons-expression-tags e))
       v2)))
    (new-tagged-pair (cons-expression-tags e) v1 v2)))
  (else (internal-error))))

;;; Flow Analysis

;;; Abstract Values

(define (potentially-imprecise-vlad-value->abstract-value v)
 ;; needs work: This needs to be done differently now that constant conversion
 ;;             has been eliminated.
 (cond ((scalar-value? v)
	(if (and *imprecise-inexacts?* (real? v) (inexact? v)) 'real v))
       ((nonrecursive-closure? v)
	(new-nonrecursive-closure
	 (map potentially-imprecise-vlad-value->abstract-value
	      (nonrecursive-closure-values v))
	 (nonrecursive-closure-lambda-expression v)))
       ((recursive-closure? v)
	(new-recursive-closure
	 (map potentially-imprecise-vlad-value->abstract-value
	      (recursive-closure-values v))
	 (recursive-closure-procedure-variables v)
	 (recursive-closure-lambda-expressions v)
	 (recursive-closure-index v)))
       ((bundle? v)
	(make-bundle (potentially-imprecise-vlad-value->abstract-value
		      (bundle-primal v))
		     (potentially-imprecise-vlad-value->abstract-value
		      (bundle-tangent v))))
       ((reverse-tagged-value? v)
	(make-reverse-tagged-value
	 (potentially-imprecise-vlad-value->abstract-value
	  (reverse-tagged-value-primal v))))
       ((tagged-pair? v)
	(new-tagged-pair (tagged-pair-tags v)
			 (potentially-imprecise-vlad-value->abstract-value
			  (tagged-pair-car v))
			 (potentially-imprecise-vlad-value->abstract-value
			  (tagged-pair-cdr v))))
       (else (internal-error))))

;;; Abstract Flows

(define (environment-binding=? b1 b2)
 (and (abstract-environment=? (environment-binding-values b1)
			      (environment-binding-values b2))
      (abstract-value=? (environment-binding-value b1)
			(environment-binding-value b2))))

(define (abstract-flow=? bs1 bs2)
 ;; This is a conservative approximation. A #t result is precise.
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp? environment-binding=? bs1 bs2))

(define (abstract-flow-union bs1 bs2) (unionp environment-binding=? bs1 bs2))

;;; Abstract Analyses
;;; It's possible that the order of expressions in abstract analyses (for the
;;;   whole program) never changes.  There will be abstract analyses (lists of
;;;   abstract expression bindings) which result from the procedure
;;;   update-abstract-analysis-domains which don't have entries for each
;;;   expression (and may not be properly ordered).  However, the analysis for
;;;   the whole program's order doesn't change, I think.

(define (empty-abstract-analysis) '())

(define (abstract-analysis=? bs1 bs2)
 ;; This is a conservative approximation. A #t result is precise.
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp? (lambda (b1 b2)
	       (and (expression=? (expression-binding-expression b1)
				  (expression-binding-expression b2))
		    (abstract-flow=? (expression-binding-flow b1)
				     (expression-binding-flow b2))))
	      bs1
	      bs2))

(define (lookup-expression-binding e bs)
 (find-if (lambda (b) (expression=? e (expression-binding-expression b))) bs))

(define (abstract-analysis-union bs1 bs2)
 (if (null? bs1)
     bs2
     (let ((b2 (lookup-expression-binding
		(expression-binding-expression (first bs1)) bs2)))
      (abstract-analysis-union
       (rest bs1)
       (if b2
	   (cons (make-expression-binding
		  (expression-binding-expression (first bs1))
		  (abstract-flow-union (expression-binding-flow (first bs1))
				       (expression-binding-flow b2)))
		 (removeq b2 bs2))
	   (cons (first bs1) bs2))))))

;;; Abstract Evaluator

(define (make-abstract-analysis e vs)
 (unless (= (length vs) (length (free-variables e))) (internal-error))
 (list (make-expression-binding
	e (list (make-environment-binding vs (abstract-top))))))

(define (initial-abstract-analysis e bs)
 ;; This (like update-analysis-domains) only makes domains.
 (make-abstract-analysis
  e
  (map
   (lambda (x)
    (potentially-imprecise-vlad-value->abstract-value
     (value-binding-value
      (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))))
   (free-variables e))))

(define (abstract-eval1 e vs bs)
 (let ((b (lookup-expression-binding e bs)))
  (if b
      (let ((b (find-if
		(lambda (b)
		 (abstract-environment=? vs (environment-binding-values b)))
		(expression-binding-flow b))))
       (if b (environment-binding-value b) (abstract-top)))
      (abstract-top))))

(define (abstract-apply-closure p v1 v2)
 (cond ((nonrecursive-closure? v1)
	(p (lambda-expression-body (nonrecursive-closure-lambda-expression v1))
	   (construct-nonrecursive-environment v1 v2)))
       ((recursive-closure? v1)
	(p (lambda-expression-body
	    (vector-ref (recursive-closure-lambda-expressions v1)
			(recursive-closure-index v1)))
	   (construct-recursive-environment v1 v2)))
       (else (internal-error))))

(define (abstract-apply v1 v2 bs)
 (cond
  ((or (abstract-top? v1) (abstract-top? v2)) (abstract-top))
  (else
   (unless (vlad-procedure? v1)
    (run-time-error "Target is not a procedure" v1))
   (unless (tag-check? v1 v2)
    (run-time-error "Argument has wrong type for target" v1 v2))
   (cond
    ((primitive-procedure? v1) ((primitive-procedure-procedure v1) v2 bs))
    ((closure? v1)
     (abstract-apply-closure (lambda (e vs) (abstract-eval1 e vs bs)) v1 v2))
    (else (internal-error))))))

(define (abstract-eval e vs bs)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e) (first vs))
  ((lambda-expression? e) (new-nonrecursive-closure vs e))
  ((application? e)
   (abstract-apply
    (abstract-eval1 (application-callee e)
		    (restrict-environment vs e application-callee)
		    bs)
    (abstract-eval1 (application-argument e)
		    (restrict-environment vs e application-argument)
		    bs)
    bs))
  ((letrec-expression? e)
   (abstract-eval1
    (letrec-expression-body e) (letrec-nested-environment vs e) bs))
  ((cons-expression? e)
   (let ((v1 (abstract-eval1 (cons-expression-car e)
			     (restrict-environment vs e cons-expression-car)
			     bs))
	 (v2 (abstract-eval1 (cons-expression-cdr e)
			     (restrict-environment vs e cons-expression-cdr)
			     bs)))
    (cond
     ((or (abstract-top? v1) (abstract-top? v2)) (abstract-top))
     (else (unless (prefix-tags? (cons-expression-tags e) (value-tags v1))
	    (run-time-error
	     (format #f "CAR argument has wrong type for target with tags ~s"
		     (cons-expression-tags e))
	     v1))
	   (unless (prefix-tags? (cons-expression-tags e) (value-tags v2))
	    (run-time-error
	     (format #f "CDR argument has wrong type for target with tags ~s"
		     (cons-expression-tags e))
	     v2))
	   (new-tagged-pair (cons-expression-tags e) v1 v2)))))
  (else (internal-error))))

(define (abstract-eval1-prime e vs bs)
 (let ((b (lookup-expression-binding e bs)))
  (if (and b
	   (some (lambda (b)
		  (abstract-environment=? vs (environment-binding-values b)))
		 (expression-binding-flow b)))
      (empty-abstract-analysis)
      (make-abstract-analysis e vs))))

(define (abstract-apply-prime v1 v2 bs)
 (cond ((or (abstract-top? v1) (abstract-top? v2)) (empty-abstract-analysis))
       (else
	(unless (vlad-procedure? v1)
	 (run-time-error "Target is not a procedure" v1))
	(unless (tag-check? v1 v2)
	 (run-time-error "Argument has wrong type for target" v1 v2))
	(cond
	 ((primitive-procedure? v1)
	  ;; needs work: should put this into slots of the primitive procedures
	  (if (eq? (primitive-procedure-name v1) 'if-procedure)
	      ((ternary
		(lambda (v1 v2 v3 bs)
		 (unimplemented "abstract evaluator for if-procedure")
		 (cond ((eq? v1 'boolean)
			(abstract-analysis-union
			 (abstract-apply-closure
			  (lambda (e vs) (abstract-eval1-prime e vs bs))
			  v2
			  (vlad-empty-list))
			 (abstract-apply-closure
			  (lambda (e vs) (abstract-eval1-prime e vs bs))
			  v3
			  (vlad-empty-list))))
		       ((vlad-false? v1)
			(abstract-apply-closure
			 (lambda (e vs) (abstract-eval1-prime e vs bs))
			 v3
			 (vlad-empty-list)))
		       (else (abstract-apply-closure
			      (lambda (e vs) (abstract-eval1-prime e vs bs))
			      v2
			      (vlad-empty-list)))))
		"if-procedure")
	       v2
	       bs)
	      (empty-abstract-analysis)))
	 ((closure? v1)
	  (abstract-apply-closure
	   (lambda (e vs) (abstract-eval1-prime e vs bs)) v1 v2))
	 (else (internal-error))))))

(define (abstract-eval-prime e vs bs)
 (cond
  ((constant-expression? e) (empty-abstract-analysis))
  ((variable-access-expression? e) (empty-abstract-analysis))
  ((lambda-expression? e) (empty-abstract-analysis))
  ((application? e)
   (abstract-analysis-union
    (abstract-analysis-union
     (abstract-eval1-prime (application-callee e)
			   (restrict-environment vs e application-callee)
			   bs)
     (abstract-eval1-prime (application-argument e)
			   (restrict-environment vs e application-argument)
			   bs))
    (abstract-apply-prime
     (abstract-eval1 (application-callee e)
		     (restrict-environment vs e application-callee)
		     bs)
     (abstract-eval1 (application-argument e)
		     (restrict-environment vs e application-argument)
		     bs)
     bs)))
  ((letrec-expression? e)
   (abstract-eval1-prime
    (letrec-expression-body e) (letrec-nested-environment vs e) bs))
  ((cons-expression? e)
   (abstract-analysis-union
    (abstract-eval1-prime (cons-expression-car e)
			  (restrict-environment vs e cons-expression-car)
			  bs)
    (abstract-eval1-prime (cons-expression-cdr e)
			  (restrict-environment vs e cons-expression-cdr)
			  bs)))
  (else (internal-error))))

(define (update-analysis-ranges bs)
 (map (lambda (b1)
       (make-expression-binding
	(expression-binding-expression b1)
	(map (lambda (b2)
	      (make-environment-binding
	       (environment-binding-values b2)
	       (abstract-eval (expression-binding-expression b1)
			      (environment-binding-values b2)
			      bs)))
	     (expression-binding-flow b1))))
      bs))

(define (update-analysis-domains bs)
 (map-reduce abstract-analysis-union
	     (empty-abstract-analysis)
	     (lambda (b1)
	      (map-reduce abstract-analysis-union
			  (empty-abstract-analysis)
			  (lambda (b2)
			   (abstract-eval-prime
			    (expression-binding-expression b1)
			    (environment-binding-values b2)
			    bs))
			  (expression-binding-flow b1)))
	     bs))

(define (concrete-reals-in v)
 (cond
  ((real? v) (list v))
  ((scalar-value? v) '())
  ((abstract-top? v) '())
  (else (map-reduce unionv '() concrete-reals-in (aggregate-value-values v)))))

(define (flow-analysis e bs)
 (let loop ((bs (initial-abstract-analysis e bs)) (i 0))
  (when *verbose?* (format #t "~s: " i))
  (let ((bs1 (if *verbose?*
		 (time
		  "~a, "
		  (lambda ()
		   (abstract-analysis-union (update-analysis-ranges bs)
					    (update-analysis-domains bs))))
		 (abstract-analysis-union (update-analysis-ranges bs)
					  (update-analysis-domains bs)))))
   (when *verbose?*
    (format #t "|analysis|=~s~%"
	    (map-reduce
	     + 0 (lambda (b) (length (expression-binding-flow b))) bs1)))
   (when *verbose?*
    (format #t "expressions: ~s, max flow size: ~s, tops: ~s, concrete reals: ~s~%"
	    (length bs)
	    (map-reduce max
			minus-infinity
			(lambda (b) (length (expression-binding-flow b)))
			bs)
	    (map-reduce
	     +
	     0
	     (lambda (b)
	      (count-if
	       (lambda (b) (abstract-top? (environment-binding-value b)))
	       (expression-binding-flow b)))
	     bs)
	    (map-reduce
	     unionv
	     '()
	     (lambda (b)
	      (map-reduce
	       unionv
	       '()
	       (lambda (b)
		(unionv
		 (map-reduce
		  unionv '() concrete-reals-in (environment-binding-values b))
		 (concrete-reals-in (environment-binding-value b))))
	       (expression-binding-flow b)))
	     bs)))
   (if (abstract-analysis=? bs1 bs) bs (loop bs1 (+ i 1))))))

;;; Code Generator

;;; Identifiers
;;; x  argument for add#, minus#, times#, divide#, atantwo#, eq#, lt#
;;;    gt#, le#, ge#, iszero#, positive#, negative#, if_procedure#,
;;;    real#, write_real, write#, zero#, primal#, tangent#, and bundle#
;;; x  result value in read_real
;;; x# variable name; # is index in xs
;;; x# variable slot of closure struct; # is index in xs
;;; x# letrec binding; # is index in xs
;;; s# struct name; # is index in vs
;;; p  primal slot of bundle struct
;;; t  tangent slot of bundle struct
;;; a  car slot of pair struct
;;; d  cdr slot of pair struct
;;; f# function name; # is index in v1v2s of function and argument value
;;; m# constructor name; # is index in vs of value being constructed
;;; r  result value in constructor definition
;;; c  environment argument for f#
;;; The following are primitive names; # is index of argument in vs
;;; add#
;;; minus#
;;; times#
;;; divide#
;;; atantwo#
;;; eq#
;;; lt#
;;; gt#
;;; le#
;;; ge#
;;; iszero#
;;; positive#
;;; negative#
;;; if_procedure#
;;; read_real
;;; real#
;;; write_real
;;; write#
;;; zero#
;;; primal#
;;; tangent#
;;; bundle#
;;; main

(define (real-pair) (vlad-cons '(real) '(real)))

(define (void? v)
 (and (not (eq? v 'boolean))
      (not (eq? v 'real))
      (or (scalar-value? v) (every void? (aggregate-value-values v)))))

(define (all-variables-in-expression e)
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e)
	(adjoinp variable=?
		 ;; needs work
		 (lambda-expression-parameter e)
		 (all-variables-in-expression (lambda-expression-body e))))
       ((application? e)
	(unionp variable=?
		(all-variables-in-expression (application-callee e))
		(all-variables-in-expression (application-argument e))))
       ((letrec-expression? e)
	(unionp
	 variable=?
	 (letrec-expression-procedure-variables e)
	 (unionp variable=?
		 (map-reduce (lambda (xs1 xs2) (unionp variable=? xs1 xs2))
			     '()
			     all-variables-in-expression
			     (letrec-expression-lambda-expressions e))
		 (all-variables-in-expression (letrec-expression-body e)))))
       ((cons-expression? e)
	(unionp variable=?
		(all-variables-in-expression (cons-expression-car e))
		(all-variables-in-expression (cons-expression-cdr e))))
       (else (internal-error))))

(define (all-variables bs)
 (map-reduce
  (lambda (xs1 xs2) (unionp variable=? xs1 xs2))
  '()
  (lambda (b) (all-variables-in-expression (expression-binding-expression b)))
  bs))

(define (generate-variable-name x xs)
 (let ((i (positionp variable=? x xs)))
  (unless i (internal-error))
  (list "x" i)))

(define (generate-specifier v vs)
 (when (void? v) (internal-error))
 (cond ((abstract-boolean? v) "int")
       ((abstract-real? v) "double")
       (else (let ((i (positionp abstract-value=? v vs)))
	      (unless i (internal-error))
	      (list "struct s" i)))))

(define (generate-slot-names v xs)
 (cond ((nonrecursive-closure? v)
	(map (lambda (x) (generate-variable-name x xs))
	     (nonrecursive-closure-variables v)))
       ((recursive-closure? v)
	(map (lambda (x) (generate-variable-name x xs))
	     (recursive-closure-variables v)))
       ((bundle? v) '("p" "t"))
       ((tagged-pair? v) '("a" "d"))
       (else (internal-error))))

(define (generate-struct-declarations xs vs)
 (map (lambda (v)
       (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
	   '()
	   (list (generate-specifier v vs)
		 "{"
		 (map (lambda (s v)
		       (if (void? v)
			   '()
			   (list (generate-specifier v vs) " " s ";")))
		      (generate-slot-names v xs)
		      (aggregate-value-values v))
		 "};"
		 #\newline)))
      vs))

(define (all-abstract-values bs)
 (map-reduce
  (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
  '()
  (lambda (b)
   (map-reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
	       '()
	       (lambda (b)
		(remove-duplicatesp abstract-value=?
				    (cons (environment-binding-value b)
					  (environment-binding-values b))))
	       (expression-binding-flow b)))
  bs))

(define (all-abstract-subvalues v)
 (cons v
       (if (scalar-value? v)
	   '()
	   (map-reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		       '()
		       all-abstract-subvalues
		       (aggregate-value-values v)))))

(define (all-abstract-subvalues-for-bundle v v-perturbation)
 (cons (vlad-cons v v-perturbation)
       (if (or (and (void? v) (void? v-perturbation))
	       (and (abstract-boolean? v) (abstract-boolean? v-perturbation))
	       (and (abstract-real? v) (abstract-real? v-perturbation)))
	   '()
	   (map-reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		       '()
		       all-abstract-subvalues-for-bundle
		       (aggregate-value-values v)
		       (aggregate-value-values v-perturbation)))))

(define (component*? v1 v2)
 (or (abstract-value=? v1 v2)
     (and (not (scalar-value? v2))
	  (memp component*? v1 (aggregate-value-values v2)))))

(define (component? v1 v2)
 (and (not (scalar-value? v2))
      (memp abstract-value=? v1 (aggregate-value-values v2))))

(define (components-before v2)
 (if (scalar-value? v2) '() (aggregate-value-values v2)))

(define (cached-topological-sort p l)
 ;; A list of pairs (x1 x2) where x1 must come before x2.
 (let ((graph (map-reduce append
			  '()
			  (lambda (x1)
			   (map-reduce append
				       '()
				       (lambda (x2)
					(if (and (not (eq? x1 x2)) (p x1 x2))
					    (list (list x1 x2))
					    '()))
				       l))
			  l)))
  (let loop ((l l) (c '()) (graph graph))
   (if (null? l)
       (reverse c)
       (let ((xs (set-differenceq l (map second graph))))
	(when (null? xs) (internal-error))
	(loop (set-differenceq l xs)
	      (append xs c)
	      (remove-if (lambda (edge) (memq (first edge) xs)) graph)))))))

(define (feedback-cached-topological-sort p l)
 ;; A list of pairs (x1 x2) where x1 must come before x2.
 (let ((graph (map-reduce append
			  '()
			  (lambda (x1)
			   (map-reduce append
				       '()
				       (lambda (x2)
					(if (and (not (eq? x1 x2)) (p x1 x2))
					    (list (list x1 x2))
					    '()))
				       l))
			  l)))
  (let loop ((l l) (c1 '()) (c2 '()) (graph graph))
   (if (null? l)
       (list (reverse c1) c2)
       (let ((xs (set-differenceq l (map second graph))))
	(if (null? xs)
	    (let ((x (find-if
		      (lambda (x)
		       (and (eq? (first x) 'function)
			    (recursive-closure? (first (second x)))))
		      l)))
	     (unless x (internal-error))
	     (loop (removeq x l)
		   c1
		   (cons x c2)
		   (remove-if (lambda (edge)
			       (or (eq? (first edge) x) (eq? (second edge) x)))
			      graph)))
	    (loop
	     (set-differenceq l xs)
	     (append xs c1)
	     c2
	     (remove-if (lambda (edge) (memq (first edge) xs)) graph))))))))

(define (all-nested-abstract-values bs)
 (cached-topological-sort
  component?
  (unionp abstract-value=?
	  (all-bundles bs)
	  (map-reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		      '()
		      all-abstract-subvalues
		      (all-abstract-values bs)))))

(define (abstract-value-pair=? v1v2a v1v2b)
 (and (abstract-value=? (first v1v2a) (first v1v2b))
      (abstract-value=? (second v1v2a) (second v1v2b))))

(define (all-subwidenings v1 v2)
 (cond ((or (void? v2) (abstract-value=? v1 v2)) '())
       ((scalar-value? v2) (list (list v1 v2)))
       (else (cons (list v1 v2)
		   (map-reduce (lambda (v1v2sa v2v2sb)
				(unionp abstract-value-pair=? v1v2sa v2v2sb))
			       '()
			       all-subwidenings
			       (aggregate-value-values v1)
			       (aggregate-value-values v2))))))

(define (all-widenings bs)
 (cached-topological-sort
  (lambda (v1v2a v1v2b)
   (or (component? (first v1v2a) (first v1v2b))
       (component? (second v1v2a) (second v1v2b))))
  (map-reduce
   (lambda (v1v2sa v2v2sb) (unionp abstract-value-pair=? v1v2sa v2v2sb))
   '()
   (lambda (b)
    (let ((e (expression-binding-expression b)))
     (if (application? e)
	 (map-reduce
	  (lambda (v1v2sa v2v2sb) (unionp abstract-value-pair=? v1v2sa v2v2sb))
	  '()
	  (lambda (b)
	   (let ((v1 (abstract-eval1 (application-callee e)
				     (restrict-environment
				      (environment-binding-values b)
				      e
				      application-callee)
				     bs)))
	    (if (and (primitive-procedure? v1)
		     (eq? (primitive-procedure-name v1) 'if-procedure))
		(let* ((v (abstract-eval1 (application-argument e)
					  (restrict-environment
					   (environment-binding-values b)
					   e
					   application-argument)
					  bs)))
		 (let* ((v1 (vlad-car v))
			(v2 (vlad-cdr v))
			(v3 (vlad-car v2))
			(v4 (vlad-cdr v2))
			(v5 (cond
			     ((eq? v1 'boolean)
			      (abstract-value-union
			       (abstract-apply v3 (vlad-empty-list) bs)
			       (abstract-apply v4 (vlad-empty-list) bs)))
			     ((vlad-false? v1)
			      (abstract-apply v4 (vlad-empty-list) bs))
			     (else (abstract-apply v3 (vlad-empty-list) bs)))))
		  (if (and (not (void? v5)) (eq? v1 'boolean))
		      (let ((v6 (abstract-apply v3 (vlad-empty-list) bs))
			    (v7 (abstract-apply v4 (vlad-empty-list) bs)))
		       (unionp abstract-value-pair=?
			       (all-subwidenings v6 v5)
			       (all-subwidenings v7 v5)))
		      '())))
		'())))
	  (expression-binding-flow b))
	 '())))
   bs)))

(define (all-functions bs)
 (map-reduce
  (lambda (v1v2sa v2v2sb) (unionp abstract-value-pair=? v1v2sa v2v2sb))
  '()
  (lambda (b)
   (let ((e (expression-binding-expression b)))
    (if (application? e)
	(map-reduce
	 (lambda (v1v2sa v2v2sb) (unionp abstract-value-pair=? v1v2sa v2v2sb))
	 '()
	 (lambda (b)
	  (let ((v1 (abstract-eval1 (application-callee e)
				    (restrict-environment
				     (environment-binding-values b)
				     e
				     application-callee)
				    bs)))
	   (cond
	    ((closure? v1)
	     (list (list v1
			 (abstract-eval1 (application-argument e)
					 (restrict-environment
					  (environment-binding-values b)
					  e
					  application-argument)
					 bs))))
	    ((and (primitive-procedure? v1)
		  (eq? (primitive-procedure-name v1) 'if-procedure))
	     (let* ((v (abstract-eval1 (application-argument e)
				       (restrict-environment
					(environment-binding-values b)
					e
					application-argument)
				       bs)))
	      (let* ((v1 (vlad-car v))
		     (v2 (vlad-cdr v))
		     (v3 (vlad-car v2))
		     (v4 (vlad-cdr v2))
		     (v5
		      (cond ((eq? v1 'boolean)
			     (abstract-value-union
			      (abstract-apply v3 (vlad-empty-list) bs)
			      (abstract-apply v4 (vlad-empty-list) bs)))
			    ((vlad-false? v1)
			     (abstract-apply v4 (vlad-empty-list) bs))
			    (else (abstract-apply v3 (vlad-empty-list) bs)))))
	       (if (void? v5)
		   '()
		   (cond ((eq? v1 'boolean)
			  ;; We make the assumption that v3 and v4 will not
			  ;; be abstract-value=?. If this assumption is false
			  ;; then there may be duplicates.
			  (list (list v3 (vlad-empty-list))
				(list v4 (vlad-empty-list))))
			 ((vlad-false? v1) (list (list v4 (vlad-empty-list))))
			 (else (list (list v3 (vlad-empty-list)))))))))
	    (else '()))))
	 (expression-binding-flow b))
	'())))
  bs))

(define (all-primitives s bs)
 (map-reduce
  (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
  '()
  (lambda (b)
   (let ((e (expression-binding-expression b)))
    (if (application? e)
	(remove-duplicatesp
	 abstract-value=?
	 (removeq
	  #f
	  (map (lambda (b)
		(let ((v1 (abstract-eval1 (application-callee e)
					  (restrict-environment
					   (environment-binding-values b)
					   e
					   application-callee)
					  bs)))
		 (if (and (primitive-procedure? v1)
			  (eq? (primitive-procedure-name v1) s))
		     (abstract-eval1 (application-argument e)
				     (restrict-environment
				      (environment-binding-values b)
				      e
				      application-argument)
				     bs)
		     #f)))
	       (expression-binding-flow b))))
	'())))
  bs))

(define (generate-builtin-name s v vs)
 (let ((i (positionp abstract-value=? v vs)))
  (unless i (internal-error))
  (list s i)))

(define (generate-function-name v1 v2 v1v2s)
 (let ((i (positionp abstract-value-pair=? (list v1 v2) v1v2s)))
  (unless i (internal-error))
  (list "f" i)))

(define (generate-widener-name v1 v2 v1v2s)
 (let ((i (positionp abstract-value-pair=? (list v1 v2) v1v2s)))
  (unless i (internal-error))
  (list "widen" i)))

(define (commas-between-void codes)
 (let ((codes (removeq #f codes)))
  (cond
   ((null? codes) "void")
   ((null? (rest codes)) (first codes))
   (else (reduce (lambda (code1 code2) (list code1 "," code2)) codes '())))))

(define (commas-between codes)
 (let ((codes (removeq #f codes)))
  (cond
   ((null? codes) '())
   ((null? (rest codes)) (first codes))
   (else (reduce (lambda (code1 code2) (list code1 "," code2)) codes '())))))

(define (generate-constructor-declarations xs vs)
 (map
  (lambda (v)
   (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
       '()
       (list "static INLINE "
	     (generate-specifier v vs)
	     " "
	     (generate-builtin-name "m" v vs)
	     "("
	     (commas-between-void
	      (map (lambda (s v)
		    (if (void? v) #f (list (generate-specifier v vs) " " s)))
		   (generate-slot-names v xs)
		   (aggregate-value-values v)))
	     ");"
	     #\newline)))
  vs))

(define (generate-constructor-definitions xs vs)
 (map
  (lambda (v)
   (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
       '()
       (list "static INLINE "
	     (generate-specifier v vs)
	     " "
	     (generate-builtin-name "m" v vs)
	     "("
	     (commas-between-void
	      (map (lambda (s v)
		    (if (void? v) #f (list (generate-specifier v vs) " " s)))
		   (generate-slot-names v xs)
		   (aggregate-value-values v)))
	     "){"
	     (generate-specifier v vs)
	     " r;"
	     (map (lambda (s v) (if (void? v) '() (list "r." s "=" s ";")))
		  (generate-slot-names v xs)
		  (aggregate-value-values v))
	     "return r;}"
	     #\newline)))
  vs))

(define (generate-widener-declarations vs v1v2s)
 (map (lambda (v1v2)
       (let ((v1 (first v1v2)) (v2 (second v1v2)))
	(list "static INLINE "
	      (generate-specifier v2 vs)
	      " "
	      (generate-widener-name v1 v2 v1v2s)
	      "("
	      (if (void? v1) "void" (list (generate-specifier v1 vs) " x"))
	      ");"
	      #\newline)))
      v1v2s))

(define (generate-widener-definitions xs vs v1v2s)
 (map
  (lambda (v1v2)
   (let ((v1 (first v1v2)) (v2 (second v1v2)))
    (list "static INLINE "
	  (generate-specifier v2 vs)
	  " "
	  (generate-widener-name v1 v2 v1v2s)
	  "("
	  (if (void? v1) "void" (list (generate-specifier v1 vs) " x"))
	  "){return "
	  (cond ((abstract-boolean? v2) (if (vlad-false? v1) "FALSE" "TRUE"))
		((abstract-real? v1) v1)
		(else (list
		       (generate-builtin-name "m" v2 vs)
		       "("
		       (commas-between
			(map (lambda (s v1 v2)
			      (cond ((void? v2) #f)
				    ((abstract-value=? v1 v2)
				     (list "x." s))
				    (else
				     (list (generate-widener-name v1 v2 v1v2s)
					   "("
					   (if (void? v1) '() (list "x." s))
					   ")"))))
			     (generate-slot-names v2 xs)
			     (aggregate-value-values v1)
			     (aggregate-value-values v2)))
		       ")")))
	  ";}"
	  #\newline)))
  v1v2s))

(define (generate-real-primitive-declarations s s1 s2 bs vs)
 (map (lambda (v)
       (unless (abstract-real? v) (internal-error))
       (list "static INLINE "
	     s1
	     " "
	     (generate-builtin-name s2 v vs)
	     "("
	     (if (void? v) "void" (list (generate-specifier v vs) " x"))
	     ");"
	     #\newline))
      (all-primitives s bs)))

(define (generate-real-primitive-definitions s s1 s2 s3 bs vs)
 (map (lambda (v)
       (unless (abstract-real? v) (internal-error))
       (list "static INLINE "
	     s1
	     " "
	     (generate-builtin-name s2 v vs)
	     "("
	     (if (void? v) "void" (list (generate-specifier v vs) " x"))
	     "){return "
	     (format #f s3 (if (void? v) v "x"))
	     ";}"
	     #\newline))
      (all-primitives s bs)))

(define (generate-real*real-primitive-declarations s s1 s2 bs vs)
 (map (lambda (v)
       (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
	(unless (and (abstract-real? v1) (abstract-real? v2)) (internal-error))
	(list "static INLINE "
	      s1
	      " "
	      (generate-builtin-name s2 v vs)
	      "("
	      (if (void? v) "void" (list (generate-specifier v vs) " x"))
	      ");"
	      #\newline)))
      (all-primitives s bs)))

(define (generate-real*real-primitive-definitions s s1 s2 s3 bs vs)
 (map (lambda (v)
       (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
	(unless (and (abstract-real? v1) (abstract-real? v2)) (internal-error))
	(list "static INLINE "
	      s1
	      " "
	      (generate-builtin-name s2 v vs)
	      "("
	      (if (void? v) "void" (list (generate-specifier v vs) " x"))
	      "){return "
	      (format #f s3 (if (void? v1) v1 "x.a") (if (void? v2) v2 "x.d"))
	      ";}"
	      #\newline)))
      (all-primitives s bs)))

(define (calls-if-procedure? e v2 vs bs)
 (or
  (and
   (application? e)
   (or (and (let ((v1 (abstract-eval1
		       (application-callee e)
		       (restrict-environment vs e application-callee)
		       bs)))
	     (and (primitive-procedure? v1)
		  (eq? (primitive-procedure-name v1) 'if-procedure)))
	    (abstract-value=?
	     (abstract-eval1 (application-argument e)
			     (restrict-environment vs e application-argument)
			     bs)
	     v2))
       (calls-if-procedure? (application-callee e)
			    v2
			    (restrict-environment vs e application-callee)
			    bs)
       (calls-if-procedure? (application-argument e)
			    v2
			    (restrict-environment vs e application-argument)
			    bs)))
  (and (letrec-expression? e)
       (calls-if-procedure? (letrec-expression-body e)
			    v2
			    (letrec-nested-environment vs e)
			    bs))
  (and (cons-expression? e)
       (or (calls-if-procedure? (cons-expression-car e)
				v2
				(restrict-environment vs e cons-expression-car)
				bs)
	   (calls-if-procedure? (cons-expression-cdr e)
				v2
				(restrict-environment vs e cons-expression-cdr)
				bs)))))

(define (calls? e v1 v2 vs bs)
 (or (and (application? e)
	  (or (and (abstract-value=?
		    (abstract-eval1
		     (application-callee e)
		     (restrict-environment vs e application-callee)
		     bs)
		    v1)
		   (abstract-value=?
		    (abstract-eval1
		     (application-argument e)
		     (restrict-environment vs e application-argument)
		     bs)
		    v2))
	      (calls? (application-callee e)
		      v1
		      v2
		      (restrict-environment vs e application-callee)
		      bs)
	      (calls? (application-argument e)
		      v1
		      v2
		      (restrict-environment vs e application-argument)
		      bs)))
     (and (letrec-expression? e)
	  (calls? (letrec-expression-body e)
		  v1
		  v2
		  (letrec-nested-environment vs e)
		  bs))
     (and (cons-expression? e)
	  (or (calls? (cons-expression-car e)
		      v1
		      v2
		      (restrict-environment vs e cons-expression-car)
		      bs)
	      (calls? (cons-expression-cdr e)
		      v1
		      v2
		      (restrict-environment vs e cons-expression-cdr)
		      bs)))))

(define (generate-things1-things2 bs xs vs v1v2s)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (feedback-cached-topological-sort
  (lambda (thing1 thing2)
   (or
    (and (eq? (first thing1) 'function)
	 (eq? (first thing2) 'if)
	 (or (abstract-value=? (first (second thing1))
			       (vlad-car (vlad-cdr (second thing2))))
	     (abstract-value=? (first (second thing1))
			       (vlad-cdr (vlad-cdr (second thing2))))))
    (and (eq? (first thing1) 'if)
	 (eq? (first thing2) 'function)
	 (calls-if-procedure?
	  (closure-body (first (second thing2)))
	  (second thing1)
	  (abstract-apply-closure
	   (lambda (e vs) vs) (first (second thing2)) (second (second thing2)))
	  bs))
    (and (eq? (first thing1) 'function)
	 (eq? (first thing2) 'function)
	 (calls?
	  (closure-body (first (second thing2)))
	  (first (second thing1))
	  (second (second thing1))
	  (abstract-apply-closure
	   (lambda (e vs) vs) (first (second thing2)) (second (second thing2)))
	  bs))))
  (append (map (lambda (v) (list 'if v)) (all-primitives 'if-procedure bs))
	  (map (lambda (v1v2) (list 'function v1v2)) v1v2s))))

(define (generate-if-and-function-declarations bs xs vs v1v2s things1-things2)
 (map
  (lambda (thing)
   (case (first thing)
    ((if)
     (let* ((v (second thing))
	    (v1 (vlad-car v))
	    (v2 (vlad-cdr v))
	    (v3 (vlad-car v2))
	    (v4 (vlad-cdr v2))
	    (v5
	     (cond ((eq? v1 'boolean)
		    (abstract-value-union
		     (abstract-apply v3 (vlad-empty-list) bs)
		     (abstract-apply v4 (vlad-empty-list) bs)))
		   ((vlad-false? v1) (abstract-apply v4 (vlad-empty-list) bs))
		   (else (abstract-apply v3 (vlad-empty-list) bs)))))
      (if (void? v5)
	  '()
	  (list "static INLINE "
		(generate-specifier v5 vs)
		" "
		(generate-builtin-name "if_procedure" v vs)
		"("
		(if (void? v) "void" (list (generate-specifier v vs) " x"))
		");"
		#\newline))))
    ((function)
     (let* ((v1v2 (second thing))
	    (v1 (first v1v2))
	    (v2 (second v1v2))
	    (v3 (abstract-apply v1 v2 bs)))
      (if (void? v3)
	  '()
	  (list
	   "static "
	   (if (memq thing (second things1-things2)) '() "INLINE ")
	   (generate-specifier v3 vs)
	   " "
	   (generate-function-name v1 v2 v1v2s)
	   "("
	   (commas-between-void
	    (list
	     (if (void? v1) #f (list (generate-specifier v1 vs) " c"))
	     (if (void? v2)
		 #f
		 (list (generate-specifier v2 vs)
		       " "
		       (generate-variable-name (closure-parameter v1) xs)))))
	   ");"
	   #\newline))))
    (else (internal-error))))
  (append (first things1-things2) (second things1-things2))))

(define (generate-widen v1 v2 code v1v2s)
 (if (abstract-value=? v1 v2)
     code
     (list (generate-widener-name v1 v2 v1v2s)
	   "("
	   (if (void? v1) '() code)
	   ")")))

(define (generate-if-and-function-definitions
	 bs xs vs v1v2s v1v2s1 things1-things2)
 (map
  (lambda (thing)
   (case (first thing)
    ((if)
     (let* ((v (second thing))
	    (v1 (vlad-car v))
	    (v2 (vlad-cdr v))
	    (v3 (vlad-car v2))
	    (v4 (vlad-cdr v2))
	    (v5
	     (cond ((eq? v1 'boolean)
		    (abstract-value-union
		     (abstract-apply v3 (vlad-empty-list) bs)
		     (abstract-apply v4 (vlad-empty-list) bs)))
		   ((vlad-false? v1) (abstract-apply v4 (vlad-empty-list) bs))
		   (else (abstract-apply v3 (vlad-empty-list) bs)))))
      (if (void? v5)
	  '()
	  (list
	   "static INLINE "
	   (generate-specifier v5 vs)
	   " "
	   (generate-builtin-name "if_procedure" v vs)
	   "("
	   (if (void? v) "void" (list (generate-specifier v vs) " x"))
	   "){return "
	   (cond
	    ((eq? v1 'boolean)
	     (let ((v6 (abstract-apply v3 (vlad-empty-list) bs))
		   (v7 (abstract-apply v4 (vlad-empty-list) bs)))
	      (list "x.a?"
		    (generate-widen
		     v6
		     v5
		     (list (generate-function-name v3 (vlad-empty-list) v1v2s)
			   "("
			   (if (void? v3) '() "x.d.a")
			   ")")
		     v1v2s1)
		    ":"
		    (generate-widen
		     v7
		     v5
		     (list (generate-function-name v4 (vlad-empty-list) v1v2s)
			   "("
			   (if (void? v4) '() "x.d.d")
			   ")")
		     v1v2s1))))
	    ((vlad-false? v1)
	     (list (generate-function-name v4 (vlad-empty-list) v1v2s)
		   "("
		   (if (void? v4) '() "x.d.d")
		   ")"))
	    (else (list (generate-function-name v3 (vlad-empty-list) v1v2s)
			"("
			(if (void? v3) '() "x.d.a")
			")")))
	   ";}"
	   #\newline))))
    ((function)
     (let* ((v1v2 (second thing))
	    (v1 (first v1v2))
	    (v2 (second v1v2))
	    (v3 (abstract-apply v1 v2 bs)))
      (if (void? v3)
	  '()
	  (list
	   "static "
	   (if (memq thing (second things1-things2)) '() "INLINE ")
	   (generate-specifier v3 vs)
	   " "
	   (generate-function-name v1 v2 v1v2s)
	   "("
	   (commas-between-void
	    (list
	     (if (void? v1) #f (list (generate-specifier v1 vs) " c"))
	     (if (void? v2)
		 #f
		 (list (generate-specifier v2 vs)
		       " "
		       (generate-variable-name (closure-parameter v1) xs)))))
	   "){"
	   (generate-letrec-bindings
	    (closure-body v1)
	    (abstract-apply-closure (lambda (e vs) vs) v1 v2)
	    (closure-variables v1)
	    (cond ((nonrecursive-closure? v1) '())
		  ((recursive-closure? v1)
		   (vector->list (recursive-closure-procedure-variables v1)))
		  (else (internal-error)))
	    bs
	    xs
	    vs
	    v1v2s)
	   "return "
	   (generate-expression
	    (closure-body v1)
	    (abstract-apply-closure (lambda (e vs) vs) v1 v2)
	    (closure-variables v1)
	    (cond ((nonrecursive-closure? v1) '())
		  ((recursive-closure? v1)
		   (vector->list (recursive-closure-procedure-variables v1)))
		  (else (internal-error)))
	    bs
	    xs
	    vs
	    v1v2s)
	   ";}"
	   #\newline))))
    (else (internal-error))))
  (append (first things1-things2) (second things1-things2))))

(define (generate-reference x xs2 xs xs1)
 (cond ((memp variable=? x xs2) "c")
       ((memp variable=? x xs) (list "c." (generate-variable-name x xs1)))
       (else (generate-variable-name x xs1))))

(define (generate-expression e vs xs xs2 bs xs1 vs1 v1v2s)
 (let ((v (abstract-eval1 e vs bs)))
  (cond
   ((void? v)
    (cond
     ((vlad-empty-list? v) (internal-error))
     ((vlad-true? v) "TRUE")
     ((vlad-false? v) "FALSE")
     ;; This assumes that Scheme inexact numbers are printed as C doubles.
     ((real? v) (exact->inexact v))
     ((primitive-procedure? v) (internal-error))
     ((nonrecursive-closure? v) (internal-error))
     ((recursive-closure? v) (internal-error))
     ((bundle? v) (internal-error))
     ((tagged-pair? v) (internal-error))
     (else (internal-error))))
   ((constant-expression? e) (internal-error))
   ((variable-access-expression? e)
    (generate-reference (variable-access-expression-variable e) xs2 xs xs1))
   ((lambda-expression? e)
    (list
     (generate-builtin-name "m" v vs1)
     "("
     (commas-between
      (map (lambda (x s v) (if (void? v) #f (generate-reference x xs2 xs xs1)))
	   (nonrecursive-closure-variables v)
	   (generate-slot-names v xs1)
	   (aggregate-value-values v)))
     ")"))
   ((application? e)
    (let ((v1 (abstract-eval1 (application-callee e)
			      (restrict-environment vs e application-callee)
			      bs))
	  (v2 (abstract-eval1 (application-argument e)
			      (restrict-environment vs e application-argument)
			      bs)))
     ;; needs work: To give an error on an improper call.
     (if (primitive-procedure? v1)
	 (list
	  ((primitive-procedure-generator v1) v2 vs1)
	  "("
	  ;; needs work: This unsoundly removes the code from the callee, and
	  ;;             possibly the argument, that might do I/O, signal an
	  ;;             error, or not terminate.
	  (if (void? v2)
	      '()
	      (generate-expression
	       (application-argument e)
	       (restrict-environment vs e application-argument)
	       xs
	       xs2
	       bs
	       xs1
	       vs1
	       v1v2s))
	  ")")
	 (list (generate-function-name v1 v2 v1v2s)
	       "("
	       (commas-between
		;; needs work: This unsoundly removes code that might do I/O,
		;;             signal an error, or not terminate.
		(list (if (void? v1)
			  #f
			  (generate-expression
			   (application-callee e)
			   (restrict-environment vs e application-callee)
			   xs
			   xs2
			   bs
			   xs1
			   vs1
			   v1v2s))
		      (if (void? v2)
			  #f
			  (generate-expression
			   (application-argument e)
			   (restrict-environment vs e application-argument)
			   xs
			   xs2
			   bs
			   xs1
			   vs1
			   v1v2s))))
	       ")"))))
   ((letrec-expression? e)
    (generate-expression (letrec-expression-body e)
			 (letrec-nested-environment vs e)
			 xs
			 xs2
			 bs
			 xs1
			 vs1
			 v1v2s))
   ((cons-expression? e)
    (let ((v1 (abstract-eval1 (cons-expression-car e)
			      (restrict-environment vs e cons-expression-car)
			      bs))
	  (v2 (abstract-eval1 (cons-expression-cdr e)
			      (restrict-environment vs e cons-expression-cdr)
			      bs)))
     (list (generate-builtin-name "m" v vs1)
	   "("
	   (commas-between
	    ;; needs work: This unsoundly removes code that might do I/O,
	    ;;             signal an error, or not terminate.
	    (list (if (void? v1)
		      #f
		      (generate-expression
		       (cons-expression-car e)
		       (restrict-environment vs e cons-expression-car)
		       xs
		       xs2
		       bs
		       xs1
		       vs1
		       v1v2s))
		  (if (void? v2)
		      #f
		      (generate-expression
		       (cons-expression-cdr e)
		       (restrict-environment vs e cons-expression-cdr)
		       xs
		       xs2
		       bs
		       xs1
		       vs1
		       v1v2s))))
	   ")")))
   (else (internal-error)))))

(define (generate-letrec-bindings  e vs xs xs2 bs xs1 vs1 v1v2s)
 (let ((v (abstract-eval1 e vs bs)))
  (cond
   ((void? v) '())
   ((constant-expression? e) (internal-error))
   ((variable-access-expression? e) '())
   ((lambda-expression? e) '())
   ((application? e)
    (let ((v1 (abstract-eval1 (application-callee e)
			      (restrict-environment vs e application-callee)
			      bs))
	  (v2 (abstract-eval1 (application-argument e)
			      (restrict-environment vs e application-argument)
			      bs)))
     ;; needs work: To give an error on an improper call.
     (if (primitive-procedure? v1)
	 ;; needs work: This unsoundly removes the code from the callee, and
	 ;;             possibly the argument, that might do I/O, signal an
	 ;;             error, or not terminate.
	 (if (void? v2)
	     '()
	     (generate-letrec-bindings
	      (application-argument e)
	      (restrict-environment vs e application-argument)
	      xs
	      xs2
	      bs
	      xs1
	      vs1
	      v1v2s))
	 ;; needs work: This unsoundly removes code that might do I/O, signal
	 ;;             an error, or not terminate.
	 (list (if (void? v1)
		   '()
		   (generate-letrec-bindings
		    (application-callee e)
		    (restrict-environment vs e application-callee)
		    xs
		    xs2
		    bs
		    xs1
		    vs1
		    v1v2s))
	       (if (void? v2)
		   '()
		   (generate-letrec-bindings
		    (application-argument e)
		    (restrict-environment vs e application-argument)
		    xs
		    xs2
		    bs
		    xs1
		    vs1
		    v1v2s))))))
   ((letrec-expression? e)
    (list
     (map
      (lambda (x)
       (let ((v (new-recursive-closure
		 (letrec-restrict-environment vs e)
		 (list->vector (letrec-expression-procedure-variables e))
		 (list->vector (letrec-expression-lambda-expressions e))
		 (positionp
		  variable=? x (letrec-expression-procedure-variables e)))))
	(if (void? v)
	    '()
	    (list (generate-specifier v vs1)
		  " "
		  (generate-variable-name x xs1)
		  "="
		  (generate-builtin-name "m" v vs1)
		  "("
		  (commas-between
		   (map (lambda (x s v)
			 (if (void? v) #f (generate-reference x xs2 xs xs1)))
			(recursive-closure-variables v)
			(generate-slot-names v xs1)
			(aggregate-value-values v)))
		  ");"))))
      (letrec-expression-procedure-variables e))
     (generate-letrec-bindings (letrec-expression-body e)
			       (letrec-nested-environment vs e)
			       xs
			       xs2
			       bs
			       xs1
			       vs1
			       v1v2s)))
   ((cons-expression? e)
    (let ((v1 (abstract-eval1 (cons-expression-car e)
			      (restrict-environment vs e cons-expression-car)
			      bs))
	  (v2 (abstract-eval1 (cons-expression-cdr e)
			      (restrict-environment vs e cons-expression-cdr)
			      bs)))
     ;; needs work: This unsoundly removes code that might do I/O, signal an
     ;;             error, or not terminate.
     (list (if (void? v1)
	       '()
	       (generate-letrec-bindings
		(cons-expression-car e)
		(restrict-environment vs e cons-expression-car)
		xs
		xs2
		bs
		xs1
		vs1
		v1v2s))
	   (if (void? v2)
	       '()
	       (generate-letrec-bindings
		(cons-expression-cdr e)
		(restrict-environment vs e cons-expression-cdr)
		xs
		xs2
		bs
		xs1
		vs1
		v1v2s)))))
   (else (internal-error)))))

(define (all-ad s bs)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (cached-topological-sort
  component?
  (map-reduce
   (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
   '()
   all-abstract-subvalues
   (map-reduce
    (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
    '()
    (lambda (b)
     (let ((e (expression-binding-expression b)))
      (if (application? e)
	  (remove-duplicatesp
	   abstract-value=?
	   (removeq #f
		    (map (lambda (b)
			  (let ((v1 (abstract-eval1
				     (application-callee e)
				     (restrict-environment
				      (environment-binding-values b)
				      e
				      application-callee)
				     bs)))
			   (if (and (primitive-procedure? v1)
				    (eq? (primitive-procedure-name v1) s))
			       (abstract-eval1 (application-argument e)
					       (restrict-environment
						(environment-binding-values b)
						e
						application-argument)
					       bs)
			       #f)))
			 (expression-binding-flow b))))
	  '())))
    bs))))

(define (all-bundles bs)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (cached-topological-sort
  (lambda (v1 v2)
   (component? (bundle (vlad-car v1) (vlad-cdr v1))
	       (bundle (vlad-car v2) (vlad-cdr v2))))
  (remove-if
   void?
   (map-reduce
    (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
    '()
    (lambda (v) (all-abstract-subvalues-for-bundle (vlad-car v) (vlad-cdr v)))
    (map-reduce
     (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
     '()
     (lambda (b)
      (let ((e (expression-binding-expression b)))
       (if (application? e)
	   (remove-duplicatesp
	    abstract-value=?
	    (removeq
	     #f
	     (map (lambda (b)
		   (let ((v1 (abstract-eval1
			      (application-callee e)
			      (restrict-environment
			       (environment-binding-values b)
			       e
			       application-callee)
			      bs)))
		    (if (and (primitive-procedure? v1)
			     (eq? (primitive-procedure-name v1) 'bundle))
			(abstract-eval1 (application-argument e)
					(restrict-environment
					 (environment-binding-values b)
					 e
					 application-argument)
					bs)
			#f)))
		  (expression-binding-flow b))))
	   '())))
     bs)))))

(define (generate-zero-declarations bs vs)
 (map (lambda (v)
       (let ((v1 (zero v)))
	(if (void? v1)
	    '()
	    (list "static INLINE "
		  (generate-specifier v1 vs)
		  " "
		  (generate-builtin-name "zero" v vs)
		  "("
		  (if (void? v) "void" (list (generate-specifier v vs) " x"))
		  ");"
		  #\newline))))
      (all-ad 'zero bs)))

(define (generate-ad-declarations f s s1 bs vs)
 ;; needs work: transposition
 (map (lambda (v)
       (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
	   '()
	   (let ((v1 (f v)))
	    (if (void? v1)
		'()
		(list "static INLINE "
		      (generate-specifier v1 vs)
		      " "
		      (generate-builtin-name s1 v vs)
		      "("
		      (generate-specifier v vs)
		      " x);"
		      #\newline)))))
      (all-ad s bs)))

(define (generate-bundle-declarations bs vs)
 ;; needs work: transposition
 (map (lambda (v)
       (let ((v1 (bundle (vlad-car v) (vlad-cdr v))))
	(if (void? v1)
	    '()
	    (list "static INLINE "
		  (generate-specifier v1 vs)
		  " "
		  (generate-builtin-name "bundle" v vs)
		  "("
		  (generate-specifier v vs)
		  " x);"
		  #\newline))))
      (all-bundles bs)))

(define (generate-zero-definitions bs xs vs)
 (map (lambda (v)
       (let ((v1 (zero v)))
	(if (void? v1)
	    '()
	    (list
	     "static INLINE "
	     (generate-specifier v1 vs)
	     " "
	     (generate-builtin-name "zero" v vs)
	     "("
	     (if (void? v) "void" (list (generate-specifier v vs) " x"))
	     "){return "
	     (cond ((abstract-boolean? v1) "x")
		   ((abstract-real? v1) "0.0")
		   (else (list
			  (generate-builtin-name "m" v1 vs)
			  "("
			  (commas-between
			   (map (lambda (s v)
				 (if (void? (zero v))
				     #f
				     (list (generate-builtin-name "zero" v vs)
					   "("
					   (if (void? v) '() (list "x." s))
					   ")")))
				(generate-slot-names v xs)
				(aggregate-value-values v)))
			  ")")))
	     ";}"
	     #\newline))))
      (all-ad 'zero bs)))

(define (generate-primal-definitions bs xs vs)
 ;; needs work: transposition
 (map
  (lambda (v)
   (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
       '()
       (let ((v1 (primal v)))
	(if (void? v1)
	    '()
	    (list
	     "static INLINE "
	     (generate-specifier v1 vs)
	     " "
	     (generate-builtin-name "primal" v vs)
	     "("
	     (generate-specifier v vs)
	     " x){return "
	     (if (or (abstract-boolean? v1) (abstract-real? v1))
		 "x.p"
		 (list (generate-builtin-name "m" v1 vs)
		       "("
		       (commas-between
			(map (lambda (s v)
			      (if (void? (primal v))
				  #f
				  (list (generate-builtin-name "primal" v vs)
					"(x."
					s
					")")))
			     (generate-slot-names v xs)
			     (aggregate-value-values v)))
		       ")"))
	     ";}"
	     #\newline)))))
  (all-ad 'primal bs)))

(define (generate-tangent-definitions bs xs vs)
 ;; needs work: transposition
 (map
  (lambda (v)
   (if (or (void? v) (abstract-boolean? v) (abstract-real? v))
       '()
       (let ((v1 (tangent v)))
	(if (void? v1)
	    '()
	    (list
	     "static INLINE "
	     (generate-specifier v1 vs)
	     " "
	     (generate-builtin-name "tangent" v vs)
	     "("
	     (generate-specifier v vs)
	     " x){return "
	     (if (or (abstract-boolean? v1) (abstract-real? v1))
		 "x.t"
		 (list (generate-builtin-name "m" v1 vs)
		       "("
		       (commas-between
			(map (lambda (s v)
			      (if (void? (tangent v))
				  #f
				  (list (generate-builtin-name "tangent" v vs)
					"(x."
					s
					")")))
			     (generate-slot-names v xs)
			     (aggregate-value-values v)))
		       ")"))
	     ";}"
	     #\newline)))))
  (all-ad 'tangent bs)))

(define (generate-bundle-definitions bs xs vs)
 ;; needs work: transposition
 (map
  (lambda (v)
   (let* ((v1 (vlad-car v)) (v2 (vlad-cdr v)) (v3 (bundle v1 v2)))
    (if (void? v3)
	'()
	(list
	 "static INLINE "
	 (generate-specifier v3 vs)
	 " "
	 (generate-builtin-name "bundle" v vs)
	 "("
	 (generate-specifier v vs)
	 " x){return "
	 (generate-builtin-name "m" v3 vs)
	 "("
	 (commas-between
	  ;; needs work: If the primal and or tangent are abstract booleans we
	  ;;             don't check legitimacy.
	  (if (scalar-value? v1)
	      (list (if (void? v1) #f "x.a") (if (void? v2) #f "x.d"))
	      (map (lambda (s4a s4b v4)
		    (if (void? v4)
			#f
			(let ((v5 (vlad-cons (primal v4) (tangent v4))))
			 (list (generate-builtin-name "bundle" v5 vs)
			       "("
			       (generate-builtin-name "m" v5 vs)
			       "("
			       (commas-between
				(map (lambda (s4 s6 v6)
				      (if (void? v6) #f (list "x." s6 "." s4)))
				     (list s4a s4b)
				     (generate-slot-names v5 xs)
				     (aggregate-value-values v5)))
			       "))"))))
		   (generate-slot-names v1 xs)
		   (generate-slot-names v2 xs)
		   (aggregate-value-values v3))))
	 ");}"
	 #\newline))))
  (all-bundles bs)))

(define (generate e bs bs0)
 (let* ((xs (all-variables bs))
	(vs (all-nested-abstract-values bs))
	(v1v2s (all-functions bs))
	(v1v2s1 (all-widenings bs))
	(things1-things2 (generate-things1-things2 bs xs vs v1v2s)))
  (list
   "#include <math.h>" #\newline
   "#include <stdio.h>" #\newline
   "#define car(x) x.a" #\newline
   "#define cdr(x) x.d" #\newline
   "#define TRUE (0==0)" #\newline
   "#define FALSE (0!=0)" #\newline
   "#define INLINE inline __attribute__ ((always_inline))" #\newline
   "static INLINE double write_real(double x){printf(\"%.18lg\\n\",x);return x;}"
   #\newline
   (generate-struct-declarations xs vs)
   (generate-constructor-declarations xs vs)
   (generate-widener-declarations vs v1v2s1)
   (generate-real*real-primitive-declarations '+ "double" "add" bs vs)
   (generate-real*real-primitive-declarations '- "double" "minus" bs vs)
   (generate-real*real-primitive-declarations '* "double" "times" bs vs)
   (generate-real*real-primitive-declarations '/ "double" "divide" bs vs)
   (generate-real*real-primitive-declarations
    'atan "double" "atantwo" bs vs)
   (generate-real*real-primitive-declarations '= "int" "eq" bs vs)
   (generate-real*real-primitive-declarations '< "int" "lt" bs vs)
   (generate-real*real-primitive-declarations '> "int" "gt" bs vs)
   (generate-real*real-primitive-declarations '<= "int" "le" bs vs)
   (generate-real*real-primitive-declarations '>= "int" "ge" bs vs)
   (generate-real-primitive-declarations 'zero? "int" "iszero" bs vs)
   (generate-real-primitive-declarations 'positive? "int" "positive" bs vs)
   (generate-real-primitive-declarations 'negative? "int" "negative" bs vs)
   "static INLINE double read_real(void);" #\newline
   (generate-real-primitive-declarations 'real "double" "real" bs vs)
   (generate-real-primitive-declarations 'write "double" "write" bs vs)
   (generate-zero-declarations bs vs)
   (generate-ad-declarations primal 'primal "primal" bs vs)
   (generate-ad-declarations tangent 'tangent "tangent" bs vs)
   (generate-bundle-declarations bs vs)
   (generate-if-and-function-declarations bs xs vs v1v2s things1-things2)
   "int main(void);" #\newline
   (generate-constructor-definitions xs vs)
   (generate-widener-definitions xs vs v1v2s1)
   (generate-real*real-primitive-definitions '+ "double" "add" "~a+~a" bs vs)
   (generate-real*real-primitive-definitions '- "double" "minus" "~a-~a" bs vs)
   (generate-real*real-primitive-definitions '* "double" "times" "~a*~a" bs vs)
   (generate-real*real-primitive-definitions
    '/ "double" "divide" "~a/~a" bs vs)
   (generate-real*real-primitive-definitions
    'atan "double" "atantwo" "atan2(~a,~a)" bs vs)
   (generate-real*real-primitive-definitions '= "int" "eq" "~a==~a" bs vs)
   (generate-real*real-primitive-definitions '< "int" "lt" "~a<~a" bs vs)
   (generate-real*real-primitive-definitions '> "int" "gt" "~a>~a" bs vs)
   (generate-real*real-primitive-definitions '<= "int" "le" "~a<=~a" bs vs)
   (generate-real*real-primitive-definitions '>= "int" "ge" "~a>=~a" bs vs)
   (generate-real-primitive-definitions 'zero? "int" "iszero" "~a==0.0" bs vs)
   (generate-real-primitive-definitions
    'positive? "int" "positive" "~a>0.0" bs vs)
   (generate-real-primitive-definitions
    'negative? "int" "negative" "~a<0.0" bs vs)
   "static INLINE double read_real(void){double x;scanf(\"%lf\",&x);return x;}"
   #\newline
   (generate-real-primitive-definitions 'real "double" "real" "~a" bs vs)
   (generate-real-primitive-definitions
    'write "double" "write" "write_real(~a)" bs vs)
   (generate-zero-definitions bs xs vs)
   (generate-primal-definitions bs xs vs)
   (generate-tangent-definitions bs xs vs)
   (generate-bundle-definitions bs xs vs)
   (generate-if-and-function-definitions bs xs vs v1v2s v1v2s1 things1-things2)
   (list
    "int main(void){"
    (let ((vs (environment-binding-values
	       (first
		(expression-binding-flow (lookup-expression-binding e bs))))))
     (if (every void? vs)
	 '()
	 (list
	  "struct {"
	  (map (lambda (v x)
		(if (void? v)
		    '()
		    (list (generate-specifier v vs)
			  " "
			  (generate-variable-name x xs)
			  ";")))
	       vs
	       (free-variables e))
	  "} c;"
	  (map
	   (lambda (v x)
	    (let loop ((v1 (value-binding-value
			    (find-if
			     (lambda (b)
			      (variable=? x (value-binding-variable b)))
			     bs0)))
		       (c (list "c." (generate-variable-name x xs)))
		       (v v))
	     (if (void? v)
		 '()
		 (cond ((abstract-boolean? v)
			(list c "=" (if (vlad-false? v1) "FALSE" "TRUE") ";"))
		       ((abstract-real? v) (list c "=" v1 ";"))
		       ((vlad-pair? v)
			(list (loop (vlad-car v1) (list c ".a") (vlad-car v))
			      (loop (vlad-cdr v1) (list c ".a") (vlad-car v))))
		       (else (internal-error))))))
	   vs
	   (free-variables e)))))
    (generate-letrec-bindings
     e
     (environment-binding-values
      (first (expression-binding-flow (lookup-expression-binding e bs))))
     (free-variables e)
     '()
     bs
     xs
     vs
     v1v2s)
    ;; needs work: This unsoundly removes code that might do I/O, signal
    ;;             an error, or not terminate.
    (if (void?
	 (abstract-eval1
	  e
	  (environment-binding-values
	   (first (expression-binding-flow (lookup-expression-binding e bs))))
	  bs))
	'()
	(list
	 (generate-expression
	  e
	  (environment-binding-values
	   (first (expression-binding-flow (lookup-expression-binding e bs))))
	  (free-variables e)
	  '()
	  bs
	  xs
	  vs
	  v1v2s)
	 ";"))
    "return 0;}"
    #\newline))))

(define (generate-file code pathname)
 (call-with-output-file (replace-extension pathname "c")
  (lambda (output-port)
   (let loop ((code code))
    (cond ((char? code) (write-char code output-port))
	  ((string? code) (display code output-port))
	  ((number? code) (write code output-port))
	  ((pair? code) (loop (car code)) (loop (cdr code)))
	  ((null? code) #f)
	  (else (internal-error)))))))

;;; Serialization

(define (all-subobjects object)
 (let ((objects '()))
  (let loop ((object object))
   (cond ((primitive-procedure? object) #f)
	 ((string? object)
	  (unless (memq object objects) (set! objects (cons object objects))))
	 ((pair? object)
	  (unless (memq object objects)
	   (set! objects (cons object objects))
	   (loop (car object))
	   (loop (cdr object))))
	 ((vector? object)
	  (unless (memq object objects)
	   (set! objects (cons object objects))
	   (for-each-vector loop object)))))
  objects))

(define (serialize-object object objects)
 (cond ((primitive-procedure? object)
	`(primitive-procedure
	  ;; needs work: closure conversion of primitives
	  ,(positionq object (map value-binding-value *value-bindings*))))
       ((or (null? object)
	    (boolean? object)
	    (char? object)
	    (and (number? object) (exact? object))
	    (symbol? object))
	object)
       ((and (number? object) (inexact? object))
	`(double ,(double-part object 0)
		 ,(double-part object 1)
		 ,(double-part object 2)
		 ,(double-part object 3)))
       ((or (string? object) (pair? object) (vector? object))
	`(table ,(positionq object objects)))
       (else (internal-error "Cannot serialize this object"))))

(define (serialize object)
 (let ((objects (all-subobjects object)))
  (cons
   (serialize-object object objects)
   (map (lambda (object)
	 (cond ((primitive-procedure? object) (internal-error))
	       ((string? object) object)
	       ((pair? object)
		(cons (serialize-object (car object) objects)
		      (serialize-object (cdr object) objects)))
	       ((vector? object)
		(map-vector (lambda (object) (serialize-object object objects))
			    object))
	       (else (internal-error))))
	objects))))

(define (unserialize-object object objects)
 (cond ((or (null? object)
	    (boolean? object)
	    (char? object)
	    (and (number? object) (exact? object))
	    (symbol? object))
	object)
       ((pair? object)
	(case (first object)
	 ((primitive-procedure)
	  ;; needs work: closure conversion of primitives
	  (value-binding-value (list-ref *value-bindings* (second object))))
	 ((double)
	  (make-double
	   (second object) (third object) (fourth object) (fifth object)))
	 ((table) (list-ref objects (second object)))
	 (else (internal-error "Cannot unserialize this object"))))
       (else (internal-error "Cannot unserialize this object"))))

(define (unserialize objects)
 (for-each
  (lambda (object)
   (cond
    ((string? object) #f)
    ((pair? object)
     (set-car! object (unserialize-object (car object) (rest objects)))
     (set-cdr! object (unserialize-object (cdr object) (rest objects))))
    ((vector? object)
     (for-each-n
      (lambda (i)
       (vector-set!
	object i (unserialize-object (vector-ref object i) (rest objects))))
      (vector-length object)))
    (else (internal-error))))
  (rest objects))
 (unserialize-object (first objects) (rest objects)))

(define (write-ebs-to-file bs pathname)
 (call-with-output-file (replace-extension pathname "ebs")
  (lambda (port) (write (serialize bs) port) (newline port))))

(define (read-ebs-from-file pathname)
 (unserialize (read-object-from-file (replace-extension pathname "ebs"))))

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

(define (read-real) (if *run?* (unimplemented "read-real") 'real))

(define (unary f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x))) (f x))))

(define (unary-predicate f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x))) (if (f x) (vlad-true) (vlad-false)))))

(define (unary-real f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (abstract-real? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (real? x) (f x) 'real))))

(define (unary-real-predicate f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (abstract-real? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (real? x) (if (f x) (vlad-true) (vlad-false)) 'boolean))))

(define (binary f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (vlad-pair? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f (vlad-car x) (vlad-cdr x)))))

(define (binary-real f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (vlad-pair? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
    (unless (and (abstract-real? x1) (abstract-real? x2))
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    ;; needs work: This may be imprecise for *, /, and atan.
    (if (and (real? x1) (real? x2)) (f x1 x2) 'real)))))

(define (binary-real-predicate f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (vlad-pair? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
    (unless (and (abstract-real? x1) (abstract-real? x2))
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (if (and (real? x1) (real? x2))
	(if (f x1 x2) (vlad-true) (vlad-false))
	'boolean)))))

(define (ternary f s)
 (lambda (x bs)
  (unless (and (vlad-pair? x) (vlad-empty-list? (vlad-car x)))
   (internal-error))
  (let ((x (vlad-cdr x)))
   (unless (vlad-pair? x)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x23 (vlad-cdr x)))
    (unless (vlad-pair? x23)
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (f (vlad-car x) (vlad-car x23) (vlad-cdr x23) bs)))))

(define (define-primitive-procedure x procedure generator forward reverse)
 (set! *value-bindings*
       (cons (make-value-binding
	      x
	      (vlad-cons (vlad-empty-list)
			 (make-primitive-procedure
			  x procedure generator forward reverse 0)))
	     *value-bindings*)))

(define (vlad-forward-listify l)
 (if (null? l)
     (bundle (vlad-empty-list) (zero (vlad-empty-list)))
     (new-tagged-pair (add-tag 'forward (empty-tags))
		      (first l)
		      (vlad-forward-listify (rest l)))))

(define (vlad-reverse-listify l)
 (if (null? l)
     (*j (vlad-empty-list))
     (new-tagged-pair (add-tag 'reverse (empty-tags))
		      (first l)
		      (vlad-reverse-listify (rest l)))))

(define (free-values-in-top-level-environment e)
 (let ((wizard? *wizard?*))
  (set! *wizard?* #t)
  (syntax-check-expression! e)
  (set! *wizard?* wizard?))
 (map (lambda (x)
       (value-binding-value
	(find-if (lambda (b) (variable=? x (value-binding-variable b)))
		 *value-bindings*)))
      (free-variables (concrete->abstract e))))

(define (evaluate-in-top-level-environment e)
 (let ((wizard? *wizard?*))
  (set! *wizard?* #t)
  (syntax-check-expression! e)
  (set! *wizard?* wizard?))
 (let ((result (parse e)))
  (concrete-eval (first result) (map value-binding-value (second result)))))

(define (initialize-forwards-and-reverses!)
 (for-each
  (lambda (b)
   (set-primitive-procedure-forward!
    (vlad-cdr (value-binding-value b))
    (new-tagged-pair
     (add-tag 'forward (empty-tags))
     (vlad-forward-listify
      (free-values-in-top-level-environment
       (primitive-procedure-forward (vlad-cdr (value-binding-value b)))))
     (evaluate-in-top-level-environment
      (primitive-procedure-forward (vlad-cdr (value-binding-value b))))))
   (set-primitive-procedure-reverse!
    (vlad-cdr (value-binding-value b))
    (new-tagged-pair
     (add-tag 'reverse (empty-tags))
     (vlad-reverse-listify
      (free-values-in-top-level-environment
       (primitive-procedure-reverse (vlad-cdr (value-binding-value b)))))
     (evaluate-in-top-level-environment
      (primitive-procedure-reverse (vlad-cdr (value-binding-value b)))))))
  *value-bindings*))

(define (initialize-basis!)
 (define-primitive-procedure '+
  (binary-real + "+")
  (lambda (v vs) (generate-builtin-name "add" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (+ x1 x2) (+ x1-perturbation x2-perturbation))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (+ x1 x2))
	   (lambda ((sensitivity y))
	    (cons (sensitivity y) (sensitivity y)))))))
 (define-primitive-procedure '-
  (binary-real - "-")
  (lambda (v vs) (generate-builtin-name "minus" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (- x1 x2) (- x1-perturbation x2-perturbation))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (- x1 x2))
	       (lambda ((sensitivity y))
		(cons (sensitivity y) (- 0.0 (sensitivity y)))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (- x1 x2))
	       (lambda ((sensitivity y))
		(cons (sensitivity y) (- (real 0) (sensitivity y)))))))))
 (define-primitive-procedure '*
  (binary-real * "*")
  (lambda (v vs) (generate-builtin-name "times" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (* x1 x2) (+ (* x2 x1-perturbation) (* x1 x2-perturbation)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (* x1 x2))
	   (lambda ((sensitivity y))
	    (cons (* x2 (sensitivity y)) (* x1 (sensitivity y))))))))
 (define-primitive-procedure '/
  (binary-real divide "/")
  (lambda (v vs) (generate-builtin-name "divide" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (/ x1 x2)
	     (/ (- (* x2 x1-perturbation) (* x1 x2-perturbation)) (* x2 x2)))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (/ x1 x2))
	       (lambda ((sensitivity y))
		(cons (/ (sensitivity y) x2)
		      (- 0.0 (/ (* x1 (sensitivity y)) (* x2 x2))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (/ x1 x2))
	       (lambda ((sensitivity y))
		(cons (/ (sensitivity y) x2)
		      (- (real 0) (/ (* x1 (sensitivity y)) (* x2 x2))))))))))
 (define-primitive-procedure 'sqrt
  (unary-real sqrt "sqrt")
  (lambda (v vs) "sqrt")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (sqrt x) (/ x-perturbation (+ (sqrt x) (sqrt x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (sqrt x))
	   (lambda ((sensitivity y))
	    (/ (sensitivity y) (+ (sqrt x) (sqrt x))))))))
 (define-primitive-procedure 'exp
  (unary-real exp "exp")
  (lambda (v vs) "exp")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (exp x) (* (exp x) x-perturbation))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (exp x))
	   (lambda ((sensitivity y)) (* (exp x) (sensitivity y)))))))
 (define-primitive-procedure 'log
  (unary-real log "log")
  (lambda (v vs) "log")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (log x) (/ x-perturbation x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (log x)) (lambda ((sensitivity y)) (/ (sensitivity y) x))))))
 (define-primitive-procedure 'sin
  (unary-real sin "sin")
  (lambda (v vs) "sin")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (sin x) (* (cos x) x-perturbation))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (sin x))
	   (lambda ((sensitivity y)) (* (cos x) (sensitivity y)))))))
 (define-primitive-procedure 'cos
  (unary-real cos "cos")
  (lambda (v vs) "cos")
  (if *imprecise-inexacts?*
      '(lambda ((forward x))
	(let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
	 (bundle (cos x) (- 0.0 (* (sin x) x-perturbation)))))
      '(lambda ((forward x))
	(let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
	 (bundle (cos x) (- (real 0) (* (sin x) x-perturbation))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons (*j (cos x))
	       (lambda ((sensitivity y))
		(- 0.0 (* (sin x) (sensitivity y)))))))
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons (*j (cos x))
	       (lambda ((sensitivity y))
		(- (real 0) (* (sin x) (sensitivity y)))))))))
 (define-primitive-procedure 'atan
  (binary-real atan "atan")
  (lambda (v vs) (generate-builtin-name "atantwo" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (atan x2 x1)
	     (/ (- (* x1 x2-perturbation) (* x2 x1-perturbation))
		(+ (* x1 x1) (* x2 x2))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(cons (- 0.0
			 (/ (* x2 (sensitivity y)) (+ (* x1 x1) (* x2 x2))))
		      (/ (* x1 (sensitivity y)) (+ (* x1 x1) (* x2 x2))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(cons (- (real 0)
			 (/ (* x2 (sensitivity y)) (+ (* x1 x1) (* x2 x2))))
		      (/ (* x1 (sensitivity y)) (+ (* x1 x1) (* x2 x2))))))))))
 (define-primitive-procedure '=
  (binary-real-predicate = "=")
  (lambda (v vs) (generate-builtin-name "eq" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (j* (= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (= x1 x2))
	   (lambda ((sensitivity y)) (cons (zero x1) (zero x2)))))))
 (define-primitive-procedure '<
  (binary-real-predicate < "<")
  (lambda (v vs) (generate-builtin-name "lt" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (j* (< x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (< x1 x2))
	   (lambda ((sensitivity y)) (cons (zero x1) (zero x2)))))))
 (define-primitive-procedure '>
  (binary-real-predicate > ">")
  (lambda (v vs) (generate-builtin-name "gt" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (j* (> x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (> x1 x2))
	   (lambda ((sensitivity y)) (cons (zero x1) (zero x2)))))))
 (define-primitive-procedure '<=
  (binary-real-predicate <= "<=")
  (lambda (v vs) (generate-builtin-name "le" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (j* (<= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (<= x1 x2))
	   (lambda ((sensitivity y)) (cons (zero x1) (zero x2)))))))
 (define-primitive-procedure '>=
  (binary-real-predicate >= ">=")
  (lambda (v vs) (generate-builtin-name "ge" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (j* (>= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (>= x1 x2))
	   (lambda ((sensitivity y)) (cons (zero x1) (zero x2)))))))
 (define-primitive-procedure 'zero?
  (unary-real-predicate zero? "zero?")
  (lambda (v vs) (generate-builtin-name "iszero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (zero? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?")
  (lambda (v vs) (generate-builtin-name "positive" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (positive? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (positive? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?")
  (lambda (v vs) (generate-builtin-name "negative" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (negative? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (negative? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'null?
  (unary-predicate vlad-empty-list? "null?")
  (lambda (v vs) (unimplemented "null?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (null? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'boolean?
  (unary-predicate abstract-boolean? "boolean?")
  (lambda (v vs) (unimplemented "boolean?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (boolean? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'real?
  (unary-predicate abstract-real? "real?")
  (lambda (v vs) (unimplemented "real?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (real? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'pair?
  (unary-predicate vlad-pair? "pair?")
  (lambda (v vs) (unimplemented "pair?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (pair? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?")
  (lambda (v vs) (unimplemented "procedure?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (procedure? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (procedure? x)) (lambda ((sensitivity y)) (zero x))))))
 ;; The forward? and reverse? primitives are not referentially transparent and
 ;; violate the forward-transformation rule for functions that only rearrange
 ;; data.
 (define-primitive-procedure 'forward?
  (unary-predicate vlad-forward? "forward?")
  (lambda (v vs) (unimplemented "forward?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (forward? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'reverse?
  (unary-predicate vlad-reverse? "reverse?")
  (lambda (v vs) (unimplemented "reverse?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (reverse? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (reverse? x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'if-procedure
  (ternary
   (lambda (x1 x2 x3 bs)
    (if *run?*
	(if (vlad-false? x1)
	    (concrete-apply (vlad-cdr x3)
			    (vlad-cons (vlad-car x3) (vlad-empty-list)))
	    (concrete-apply (vlad-cdr x2)
			    (vlad-cons (vlad-car x2) (vlad-empty-list))))
	(begin
	 (unimplemented "abstract evaluator for if-procedure")
	 (cond ((eq? x1 'boolean)
		(let ((v2 (abstract-apply-closure
			   (lambda (e vs) (abstract-eval1 e vs bs))
			   x2
			   (vlad-empty-list)))
		      (v3 (abstract-apply-closure
			   (lambda (e vs) (abstract-eval1 e vs bs))
			   x3
			   (vlad-empty-list))))
		 ;; needs work: a little hokey
		 (cond ((abstract-top? v2) v3)
		       ((abstract-top? v3) v2)
		       (else (abstract-value-union v2 v3)))))
	       ((vlad-false? x1)
		(abstract-apply-closure
		 (lambda (e vs) (abstract-eval1 e vs bs))
		 x3
		 (vlad-empty-list)))
	       (else (abstract-apply-closure
		      (lambda (e vs) (abstract-eval1 e vs bs))
		      x2
		      (vlad-empty-list)))))))
   "if-procedure")
  (lambda (v vs) (generate-builtin-name "if_procedure" v vs))
  '(lambda ((forward x))
    (let (((cons* x1 x2 x3) (primal (forward x)))
	  ((cons* x1-perturbation x2-perturbation x3-perturbation)
	   (tangent (forward x))))
     (if x1
	 ((bundle x2 x2-perturbation) (bundle '() (zero '())))
	 ((bundle x3 x3-perturbation) (bundle '() (zero '()))))))
  '(lambda ((reverse x))
    (let (((cons* x1 x2 x3) (*j-inverse (reverse x))))
     (if x1
	 (let (((cons (reverse y) (backpropagator y)) ((*j x2) (*j '()))))
	  (cons (reverse y)
		(lambda ((sensitivity y))
		 (cons* (zero x1)
			;; needs work: think this through again
			;; ((backpropagator y) (sensitivity y)) should be
			;; the sensitivity to the ignored '() argument of x2
			((backpropagator y) (sensitivity y))
			(zero x3)))))
	 (let (((cons (reverse y) (backpropagator y)) ((*j x3) (*j '()))))
	  (cons (reverse y)
		(lambda ((sensitivity y))
		 (cons* (zero x1)
			(zero x2)
			;; needs work: think this through again
			;; ((backpropagator y) (sensitivity y)) should be
			;; the sensitivity to the ignored '() argument of x3
			((backpropagator y) (sensitivity y))))))))))
 (define-primitive-procedure 'read-real
  ;; needs work: Should enforce that the argument is vlad-empty-list.
  (unary (lambda (x) (read-real)) "read-real")
  (lambda (v vs) "read_real")
  (if *imprecise-inexacts?*
      ;; needs work: Tags are lost in the (lambda () ...) and should enforce
      ;;             that the argument is (forward vlad-empty-list).
      '(lambda () (bundle (read-real) 0.0))
      ;; needs work: Tags are lost in the (lambda () ...) and should enforce
      ;;             that the argument is (forward vlad-empty-list).
      '(lambda () (bundle (read-real) (real 0))))
  ;; needs work: Tags are lost in the first (lambda () ...) and should enforce
  ;;             that the argument to the first is (reverse vlad-empty-list).
  '(lambda () (cons (*j (read-real)) (lambda ((sensitivity y)) '()))))
 (define-primitive-procedure 'real
  (unary-real (lambda (x) (if *run?* x 'real)) "real")
  (lambda (v vs) (generate-builtin-name "real" v vs))
  ;; These widen the tangent and cotangent as well. Nothing requires us to do
  ;; so. It is just a design decision.
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (real x) (real x-perturbation))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real x)) (lambda ((sensitivity y)) (real (sensitivity y)))))))
 (define-primitive-procedure 'write
  (unary (lambda (x)
	  (when *run?* ((if *pp?* pp write) (externalize x)) (newline))
	  x)
	 "write")
  (lambda (v vs) (generate-builtin-name "write" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (write x) x-perturbation)))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write x)) (lambda ((sensitivity y)) (sensitivity y))))))
 (define-primitive-procedure 'zero
  (unary zero "zero")
  (lambda (v vs) (generate-builtin-name "zero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (zero x) (zero x-perturbation))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x)) (lambda ((sensitivity y)) (zero x))))))
 (define-primitive-procedure 'primal
  (unary primal "primal")
  (lambda (v vs) (generate-builtin-name "primal" v vs))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  (x-forward-perturbation (tangent (forward x-forward))))
     (bundle (primal x-forward) (primal x-forward-perturbation))))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (cons (*j (primal x-forward))
	   ;; needs work: not sure that this call to j* is correct
	   (lambda ((sensitivity y)) (j* (sensitivity y)))))))
 (define-primitive-procedure 'tangent
  (unary tangent "tangent")
  (lambda (v vs) (generate-builtin-name "tangent" v vs))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  (x-forward-perturbation (tangent (forward x-forward))))
     (bundle (tangent x-forward) (tangent x-forward-perturbation))))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward))))
     (cons (*j (tangent x-forward))
	   (lambda ((sensitivity y-perturbation))
	    (bundle (zero (primal x-forward))
		    (sensitivity y-perturbation)))))))
 (define-primitive-procedure 'bundle
  (binary bundle "bundle")
  (lambda (v vs) (generate-builtin-name "bundle" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2-perturbation) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation-perturbation)
	   (tangent (forward x))))
     (bundle (bundle x1 x2-perturbation)
	     (bundle x1-perturbation x2-perturbation-perturbation))))
  '(lambda ((reverse x))
    (let (((cons x1 x2-perturbation) (*j-inverse (reverse x))))
     (cons (*j (bundle x1 x2-perturbation))
	   (lambda ((sensitivity (forward y)))
	    (cons (primal (sensitivity (forward y)))
		  (tangent (sensitivity (forward y)))))))))
 (define-primitive-procedure 'plus
  (binary plus "plus")
  (lambda (v vs) (unimplemented "plus"))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-perturbation x2-perturbation) (tangent (forward x))))
     (bundle (plus x1 x2) (plus x1-perturbation x2-perturbation))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (plus x1 x2))
	   (lambda ((sensitivity y))
	    (cons (sensitivity y) (sensitivity y)))))))
 (define-primitive-procedure '*j
  (unary *j "*j")
  (lambda (v vs) (unimplemented "*j"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (x-perturbation (tangent (forward x))))
     (bundle (*j x) (*j x-perturbation))))
  '(lambda ((reverse x))
    ;; The *j composed with *j-inverse could be optimized away.
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (*j x))
	   (lambda ((sensitivity (reverse y)))
	    (*j-inverse (sensitivity (reverse y))))))))
 (define-primitive-procedure '*j-inverse
  (unary *j-inverse "*j-inverse")
  (lambda (v vs) (unimplemented "*j-inverse"))
  ;; The argument must be called x-reverse so as not to confuse the tags.
  '(lambda ((forward x-reverse))
    (let ((x-reverse (primal (forward x-reverse)))
	  (x-reverse-perturbation (tangent (forward x-reverse))))
     (bundle (*j-inverse x-reverse) (*j-inverse x-reverse-perturbation))))
  ;; The argument must be called x-reverse so as not to confuse the tags.
  '(lambda ((reverse x-reverse))
    (let ((x-reverse (*j-inverse (reverse x-reverse))))
     ;; The *j composed with *j-inverse could be optimized away.
     (cons (*j (*j-inverse x-reverse))
	   (lambda ((sensitivity y)) (*j (sensitivity y)))))))
 (initialize-forwards-and-reverses!))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
