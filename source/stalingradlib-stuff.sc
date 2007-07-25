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

;;; needs work
;;;  1. zero, primal, tangent, bundle, plus, *j, and *j-inverse should be lazy.
;;;  2. does making plus lazy eliminate the need to special case for generic
;;;     zeros?
;;;  3. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  4. We removed -wizard because macro expansion required (ignore) and
;;;     (consvar x1 x2). Someday we need to put it back in.
;;;  5. For now, we don't optimize away tangents that are equivalent to the
;;;     primal.

;;; Scott Pairs
;;;  1. pair? will return #t and procedure? will return #f on some procedures
;;;     that are compatible with pairs.
;;;  2. You can take the car and cdr of some procedures that are compatible
;;;     with pairs and not get an error.
;;;  3. Primitives that expect tuples will accept procedures that are
;;;     compatible with pairs and not give an error.
;;;  4. Procedures that are compatible with pairs will print as pairs rather
;;;     than as procedures.
;;;  5. You can call a pair.

(include "QobiScheme.sch")
(include "c-externals.sc")
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. unary -
;;;  2. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  3. chars, ports, eof object, symbols, continuations, strings, vectors
;;;  4. enforce don't shadow: car, cdr, cons-procedure, and ys

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

(define-structure constant-expression value)

(define-structure variable-access-expression variable index)

(define-structure lambda-expression
 free-variables
 free-variable-indices			;vector
 variable
 body)

(define-structure application callee argument free-variables)

(define-structure letrec-expression
 bodies-free-variables
 bodies-free-variable-indices		;vector
 body-free-variables
 body-free-variable-indices		;vector
 procedure-variables
 argument-variables
 bodies
 body)

(define-structure cons-expression tags car cdr free-variables)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 name procedure generator forward reverse meter)

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

;;; Parameters

(define *include-path* '())

(define *encoded-booleans?* #f)

(define *scott-pairs?* #f)

(define *letrec-as-y?* #f)

(define *flow-analysis?* #f)

(define *compile?* #f)

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-nonrecursive-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-nicely?* #f)

(define *unabbreviate-transformed?* #t)

(define *unabbreviate-nonrecursive-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *x* #f)

(define *expression-equality* 'structural)

(define *imprecise-zero?* #f)

(define *imprecise-inexacts?* #f)

(define *verbose?* #f)

(define *run?* #f)

;;; Procedures

;;; Error Handing

(define (compile-time-error message . arguments)
 (apply format stderr-port message arguments)
 (newline stderr-port)
 (exit -1))

(define (run-time-error message . vs)
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
 (display "Error: ")
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

;;; Values

(define (scalar-value? v)
 (or (null? v)
     (abstract-boolean? v)
     (abstract-real? v)
     (primitive-procedure? v)))

(define (aggregate-value-values v)
 (cond ((closure? v) (vector->list (closure-values v)))
       ((bundle? v) (list (bundle-primal v) (bundle-tangent v)))
       ((reverse-tagged-value? v) (list (reverse-tagged-value-primal v)))
       ((tagged-pair? v) (list (tagged-pair-car v) (tagged-pair-cdr v)))
       (else (internal-error))))

(define (tagged-null tags)
 (if (null? tags)
     '()
     (case (first tags)
      ((forward) (let ((x (tagged-null (rest tags)))) (bundle x (zero x))))
      ((reverse) (*j (tagged-null (rest tags))))
      (else (internal-error)))))

(define vlad-true #t)

(define vlad-false #f)

(define (vlad-true? v)
 (if *encoded-booleans?*
     ;; (lambda (p)
     ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) a))) x3))) (x2 (p x1)))
     ;;   x2))
     (and
      (nonrecursive-closure? v)
      (not (vlad-forward? v))
      (not (vlad-reverse? v))
      (null? (closure-variables v))
      (let*? (closure-body v))
      (= (length (let*-variables (closure-body v))) 2)
      (lambda-expression? (first (let*-expressions (closure-body v))))
      (let*?
       (lambda-expression-body (first (let*-expressions (closure-body v)))))
      (= (length (let*-variables
		  (lambda-expression-body
		   (first (let*-expressions (closure-body v))))))
	 1)
      (lambda-expression?
       (first (let*-expressions
	       (lambda-expression-body
		(first (let*-expressions (closure-body v)))))))
      (variable-access-expression?
       (lambda-expression-body
	(first (let*-expressions
		(lambda-expression-body
		 (first (let*-expressions (closure-body v))))))))
      ;; Check that x3 is bound to (lambda (d) a), not (lambda (d) d).
      (variable=? (variable-access-expression-variable
		   (lambda-expression-body
		    (first (let*-expressions
			    (lambda-expression-body
			     (first (let*-expressions (closure-body v))))))))
		  (lambda-expression-variable
		   (first (let*-expressions (closure-body v)))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (let*-body (lambda-expression-body
		   (first (let*-expressions (closure-body v))))))
      (variable=?
       (variable-access-expression-variable
	(let*-body
	 (lambda-expression-body (first (let*-expressions (closure-body v))))))
       (first (let*-variables
	       (lambda-expression-body
		(first (let*-expressions (closure-body v)))))))
      (application? (second (let*-expressions (closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee (second (let*-expressions (closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (second (let*-expressions (closure-body v)))))
		  (closure-variable v))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument (second (let*-expressions (closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (second (let*-expressions (closure-body v)))))
		  (first (let*-variables (closure-body v))))
      (variable-access-expression? (let*-body (closure-body v)))
      (variable=? (variable-access-expression-variable
		   (let*-body (closure-body v)))
		  (second (let*-variables (closure-body v)))))
     (eq? v #t)))

(define (vlad-false? v)
 (if *encoded-booleans?*
     ;; (lambda (p)
     ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) d))) x3))) (x2 (p x1)))
     ;;   x2))
     (and
      (nonrecursive-closure? v)
      (not (vlad-forward? v))
      (not (vlad-reverse? v))
      (null? (closure-variables v))
      (let*? (closure-body v))
      (= (length (let*-variables (closure-body v))) 2)
      (lambda-expression? (first (let*-expressions (closure-body v))))
      (let*?
       (lambda-expression-body (first (let*-expressions (closure-body v)))))
      (= (length (let*-variables
		  (lambda-expression-body
		   (first (let*-expressions (closure-body v))))))
	 1)
      (lambda-expression?
       (first (let*-expressions
	       (lambda-expression-body
		(first (let*-expressions (closure-body v)))))))
      (variable-access-expression?
       (lambda-expression-body
	(first (let*-expressions
		(lambda-expression-body
		 (first (let*-expressions (closure-body v))))))))
      (variable=? (variable-access-expression-variable
		   (lambda-expression-body
		    (first (let*-expressions
			    (lambda-expression-body
			     (first (let*-expressions (closure-body v))))))))
		  (lambda-expression-variable
		   (first (let*-expressions
			   (lambda-expression-body
			    (first (let*-expressions (closure-body v))))))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (let*-body (lambda-expression-body
		   (first (let*-expressions (closure-body v))))))
      (variable=?
       (variable-access-expression-variable
	(let*-body
	 (lambda-expression-body (first (let*-expressions (closure-body v))))))
       (first (let*-variables
	       (lambda-expression-body
		(first (let*-expressions (closure-body v)))))))
      (application? (second (let*-expressions (closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee (second (let*-expressions (closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (second (let*-expressions (closure-body v)))))
		  (closure-variable v))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument (second (let*-expressions (closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (second (let*-expressions (closure-body v)))))
		  (first (let*-variables (closure-body v))))
      (variable-access-expression? (let*-body (closure-body v)))
      (variable=? (variable-access-expression-variable
		   (let*-body (closure-body v)))
		  (second (let*-variables (closure-body v)))))
     (eq? v #f)))

(define (closure? v) (or (nonrecursive-closure? v) (recursive-closure? v)))

(define (closure-variables v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-variables v))
       ((recursive-closure? v) (recursive-closure-variables v))
       (else (internal-error))))

(define (closure-values v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-values v))
       ((recursive-closure? v) (recursive-closure-values v))
       (else (internal-error))))

(define (closure-variable v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-variable v))
       ((recursive-closure? v)
	(vector-ref (recursive-closure-argument-variables v)
		    (recursive-closure-index v)))
       (else (internal-error))))

(define (closure-tags v) (variable-tags (closure-variable v)))

(define (closure-body v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-body v))
       ((recursive-closure? v)
	(vector-ref (recursive-closure-bodies v) (recursive-closure-index v)))
       (else (internal-error))))

(define (vlad-procedure? v)
 (and (or (primitive-procedure? v) (closure? v))
      (not (vlad-pair? v '()))
      (not (vlad-true? v))
      (not (vlad-false? v))))

(define (vlad-forward? v)
 (or (and (closure? v) (forward-variable? (closure-variable v)))
     (bundle? v)
     (and (not *scott-pairs?*)
	  (tagged-pair? v)
	  (memq 'forward (tagged-pair-tags v)))))

(define (vlad-reverse? v)
 (or (and (closure? v) (reverse-variable? (closure-variable v)))
     (reverse-tagged-value? v)
     (and (not *scott-pairs?*)
	  (tagged-pair? v)
	  (memq 'reverse (tagged-pair-tags v)))))

(define (vlad-pair? v tags)
 (if *scott-pairs?*
     (if (null? tags)
	 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
	 (and
	  (nonrecursive-closure? v)
	  (not (vlad-forward? v))
	  (not (vlad-reverse? v))
	  (= (length (closure-variables v)) 2)
	  (let*? (closure-body v))
	  (= (length (let*-variables (closure-body v))) 2)
	  (application? (first (let*-expressions (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee (first (let*-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee (first (let*-expressions (closure-body v)))))
	   (closure-variable v))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument (first (let*-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-argument (first (let*-expressions (closure-body v)))))
	   (first (closure-variables v)))
	  (application? (second (let*-expressions (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee (second (let*-expressions (closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee (second (let*-expressions (closure-body v)))))
	   (first (let*-variables (closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument (second (let*-expressions (closure-body v)))))
	  (variable=? (variable-access-expression-variable
		       (application-argument
			(second (let*-expressions (closure-body v)))))
		      (second (closure-variables v)))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression? (let*-body (closure-body v)))
	  (variable=? (variable-access-expression-variable
		       (let*-body (closure-body v)))
		      (second (let*-variables (closure-body v)))))
	 (case (first tags)
	  ((forward) (vlad-pair? (primal v) (rest tags)))
	  ((reverse) (vlad-pair? (*j-inverse v) (rest tags)))
	  (else (internal-error))))
     (and (tagged-pair? v) (equal-tags? (tagged-pair-tags v) tags))))

(define (vlad-car v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take car of a non-pair" v))
 (if *scott-pairs?*
     (if (null? tags)
	 (vector-ref (closure-values v) 0)
	 (case (first tags)
	  ((forward) (bundle (vlad-car (primal v) (rest tags))
			     (vlad-car (tangent v) (rest tags))))
	  ((reverse) (*j (vlad-car (*j-inverse v) (rest tags))))
	  (else (internal-error))))
     (tagged-pair-car v)))

(define (vlad-cdr v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take cdr of a non-pair" v))
 (if *scott-pairs?*
     (if (null? tags)
	 (vector-ref (closure-values v) 1)
	 (case (first tags)
	  ((forward) (bundle (vlad-cdr (primal v) (rest tags))
			     (vlad-cdr (tangent v) (rest tags))))
	  ((reverse) (*j (vlad-cdr (*j-inverse v) (rest tags))))
	  (else (internal-error))))
     (tagged-pair-cdr v)))

(define (vlad-cons v1 v2)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (if *scott-pairs?*
     (let ((vs (vector v1 v2)))
      (make-nonrecursive-closure
       '(a d)
       vs
       'm
       (index
	'm
	'(a d)
	(new-let* '(x1 x2)
		  (list (new-application (new-variable-access-expression 'm)
					 (new-variable-access-expression 'a))
			(new-application (new-variable-access-expression 'x1)
					 (new-variable-access-expression 'd)))
		  (new-variable-access-expression 'x2)))))
     (make-tagged-pair '() v1 v2)))

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->symbol			;debugging: was uninterned
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (hensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->symbol			;debugging: was uninterned
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
	 (else (internal-error))))
       (else (internal-error))))

;;; needs work: variables must be equal even when tags are permuted
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
	      (else (internal-error)))
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

(define (sort-variables xs) (sort xs variable<? identity))

(define (parameter->consvar p)
 (cond ((variable? p) p)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3) (internal-error))
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
	 (else (internal-error))))
       (else (internal-error))))

(define (duplicates? xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (member (first xs) (rest xs)) (duplicates? (rest xs)))))

(define (duplicatesp? p xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (memp p (first xs) (rest xs)) (duplicatesp? p (rest xs)))))

(define (perturbationify x) `(perturbation ,x))

(define (forwardify x) `(forward ,x))

(define (sensitivityify x) `(sensitivity ,x))

(define (backpropagatorify x) `(backpropagator ,x))

(define (reverseify x) `(reverse ,x))

(define (perturbation-variable? x) (memq 'perturbation (variable-tags x)))

(define (forward-variable? x) (memq 'forward (variable-tags x)))

(define (sensitivity-variable? x) (memq 'sensitivity (variable-tags x)))

(define (backpropagator-variable? x) (memq 'backpropagator (variable-tags x)))

(define (reverse-variable? x) (memq 'reverse (variable-tags x)))

(define (unperturbationify x)
 (unless (perturbation-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ;; needs work: should we unwrap the alpha?
   ((alpha) (loop (second x)))
   ((perturbation) (second x))
   ((forward) (cons (first x) (loop (second x))))
   ((sensitivity) (cons (first x) (loop (second x))))
   ((reverse) (cons (first x) (loop (second x))))
   (else (internal-error)))))

(define (unforwardify x)
 (unless (forward-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ;; needs work: should we unwrap the alpha?
   ((alpha) (loop (second x)))
   ((perturbation) (cons (first x) (loop (second x))))
   ((forward) (second x))
   ((sensitivity) (cons (first x) (loop (second x))))
   ((reverse) (cons (first x) (loop (second x))))
   (else (internal-error)))))

(define (unsensitivityify x)
 (unless (sensitivity-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ;; needs work: should we unwrap the alpha?
   ((alpha) (loop (second x)))
   ((perturbation) (cons (first x) (loop (second x))))
   ((forward) (cons (first x) (loop (second x))))
   ((sensitivity) (second x))
   ((reverse) (cons (first x) (loop (second x))))
   (else (internal-error)))))

(define (unbackpropagatorify x) (unimplemented "unbackpropagatorify"))

(define (unreverseify x)
 (unless (reverse-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ;; needs work: should we unwrap the alpha?
   ((alpha) (loop (second x)))
   ((perturbation) (cons (first x) (loop (second x))))
   ((forward) (cons (first x) (loop (second x))))
   ((sensitivity) (cons (first x) (loop (second x))))
   ((reverse) (second x))
   (else (internal-error)))))

(define (lax-unreverseify x) (unimplemented "lax-unreverseify"))

(define (perturbation-access x)
 (new-variable-access-expression (perturbationify x)))

(define (forward-access x) (new-variable-access-expression (forwardify x)))

(define (sensitivity-access x)
 (new-variable-access-expression (sensitivityify x)))

(define (backpropagator-access x)
 (new-variable-access-expression (backpropagatorify x)))

(define (reverse-access x) (new-variable-access-expression (reverseify x)))

(define (unperturbation-access x)
 (new-variable-access-expression (unperturbationify x)))

(define (unforward-access x) (new-variable-access-expression (unforwardify x)))

(define (unsensitivity-access x)
 (new-variable-access-expression (unsensitivityify x)))

(define (unbackpropagator-access x)
 (new-variable-access-expression (unbackpropagatorify x)))

(define (unreverse-access x) (new-variable-access-expression (unreverseify x)))

(define (perturbationify-access e)
 (new-variable-access-expression
  (perturbationify (variable-access-expression-variable e))))

(define (forwardify-access e)
 (new-variable-access-expression
  (forwardify (variable-access-expression-variable e))))

(define (sensitivityify-access e)
 (new-variable-access-expression
  (sensitivityify (variable-access-expression-variable e))))

(define (backpropagatorify-access e)
 (new-variable-access-expression
  (backpropagatorify (variable-access-expression-variable e))))

(define (reverseify-access e)
 (new-variable-access-expression
  (reverseify (variable-access-expression-variable e))))

(define (unperturbationify-access e)
 (new-variable-access-expression
  (unperturbationify (variable-access-expression-variable e))))

(define (unforwardify-access e)
 (new-variable-access-expression
  (unforwardify (variable-access-expression-variable e))))

(define (unsensitivityify-access e)
 (new-variable-access-expression
  (unsensitivityify (variable-access-expression-variable e))))

(define (unbackpropagatorify-access e)
 (new-variable-access-expression
  (unbackpropagatorify (variable-access-expression-variable e))))

(define (unreverseify-access e)
 (new-variable-access-expression
  (unreverseify (variable-access-expression-variable e))))

(define (variable-tags x)
 (if (pair? x)
     (case (first x)
      ((alpha) (variable-tags (second x)))
      ((perturbation) (cons 'perturbation (variable-tags (second x))))
      ((forward) (cons 'forward (variable-tags (second x))))
      ((sensitivity) (cons 'sensitivity (variable-tags (second x))))
      ((backpropagator) (cons 'backpropagator (variable-tags (second x))))
      ((reverse) (cons 'reverse (variable-tags (second x))))
      (else '()))
     '()))

(define (remove-oneq tag tags)
 (when (null? tags) (internal-error))
 (if (eq? (first tags) tag)
     (rest tags)
     (cons (first tags) (remove-oneq tag (rest tags)))))

(define (lambda-expression-tags e)
 (variable-tags (lambda-expression-variable e)))

(define (equal-tags? tags1 tags2)
 (and (every (lambda (tag1) (= (countq tag1 tags1) (countq tag1 tags2)))
	     tags1)
      (every (lambda (tag2) (= (countq tag2 tags1) (countq tag2 tags2)))
	     tags2)))

;;; Expression constructors

(define (new-variable-access-expression x)
 (make-variable-access-expression x #f))

(define (new-lambda-expression x e)
 ;; No need to sort here because (free-variables e) is sorted and removing
 ;; a variable does not disturb that.
 (make-lambda-expression (removep variable=? x (free-variables e)) #f x e))

(define (new-application e1 e2)
 (make-application
  e1
  e2
  (sort-variables (union-variables (free-variables e1) (free-variables e2)))))

(define (create-application bs tags e . es)
 (new-application e (make-cons* bs tags es)))

(define (new-let* xs es e)
 (if (null? xs)
     e
     (new-application
      ;; needs work: This disables vestigial let*-expressions.
      (if #f
	  (make-lambda-expression #f
				  #f
				  (first xs)
				  (new-let* (rest xs) (rest es) e))
	  (new-lambda-expression (first xs) (new-let* (rest xs) (rest es) e)))
      (first es))))

(define (create-let* bs e)
 (new-let*
  (map variable-binding-variable bs) (map variable-binding-expression bs) e))

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

(define (new-cons-expression tags e1 e2)
 (make-cons-expression
  tags
  e1
  e2
  (sort-variables (union-variables (free-variables e1) (free-variables e2)))))

(define (create-cons-expression e1 e2) (new-cons-expression '() e1 e2))

;;; LET*

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))
     (and (cons-expression? e)
	  (or (contains-letrec? (cons-expression-car e))
	      (contains-letrec? (cons-expression-cdr e))))))

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

;;; Standard prelude

(define (standard-prelude e)
 `(let* (,@(if *scott-pairs?*
	       '((car (lambda (p) (p (lambda (a) (lambda (d) a)))))
		 (cdr (lambda (p) (p (lambda (a) (lambda (d) d)))))
		 (cons-procedure
		  (lambda (a) (lambda (d) (lambda (m) ((m a) d))))))
	       '())
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
 (for-each
  (lambda (d)
   (unless (definition? d) (compile-time-error "Invalid definition: ~s" d)))
  ds)
 (standard-prelude
  `(letrec ,(map (lambda (d)
		  `(,(definens-name (second d))
		    ,(definens-expression (second d) (third d))))
		 ds)
    ,e)))

;;; Alpha conversion

(define (alphaify x xs)
 (if (memp variable=? x xs)
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

(define (alpha-convert e xs)
 ;; needs work: Should have structure instead of list.
 ;; needs work: to make faster
 (second
  (let outer ((e e) (xs xs) (bs (map make-alpha-binding xs xs)))
   (cond
    ((constant-expression? e) e)
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
      (list (first result) (new-lambda-expression x (second result)))))
    ((application? e)
     (let* ((result1 (outer (application-callee e) xs bs))
	    (result2 (outer (application-argument e) (first result1) bs)))
      (list (first result2)
	    (new-application (second result1) (second result2)))))
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
		  (new-letrec-expression
		   (reverse xs3) (reverse xs4) (reverse es1) (second result))))
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
    ((cons-expression? e)
     (let* ((result1 (outer (cons-expression-car e) xs bs))
	    (result2 (outer (cons-expression-cdr e) (first result1) bs)))
      (list (first result2)
	    (new-cons-expression
	     (cons-expression-tags e) (second result1) (second result2)))))
    (else (internal-error))))))

(define (alpha-equivalent? e1 e2 xs1 xs2)
 ;; This is what Stump calls hypothetical (or contextual) alpha equivalence,
 ;; i.e. whether e1 is alpha-equivalent to e2 in the context where each xs1_i
 ;; is assumed to be equivalent to the corresponding ex2_i.
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
	(append (letrec-expression-procedure-variables e2) xs2)))
  (and (cons-expression? e1)
       (cons-expression? e2)
       (alpha-equivalent?
	(cons-expression-car e1) (cons-expression-car e2) xs1 xs2)
       (alpha-equivalent?
	(cons-expression-cdr e1) (cons-expression-cdr e2) xs1 xs2))))

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
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e)
	(if (eq? (lambda-expression-free-variables e) #f)
	    (unimplemented "vestigial let*-expressions")
	    (lambda-expression-free-variables e)))
       ((application? e) (application-free-variables e))
       ((letrec-expression? e) (letrec-expression-body-free-variables e))
       ((cons-expression? e) (cons-expression-free-variables e))
       (else (internal-error))))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (variable=? x-prime x) (memp variable=? x-prime xs))
   (internal-error))
  ;; The reverse is necessary because let*-expression doesn't prune unaccessed
  ;; variables.
  (if (memp variable=? x-prime xs)
      ;; This is a vestigial let*-expression.
      (- (length xs) (positionp variable=? x-prime (reverse xs)) 1)
      -1))
 (cond
  ((variable-access-expression? e)
   (make-variable-access-expression
    (variable-access-expression-variable e)
    (lookup (variable-access-expression-variable e))))
  ((lambda-expression? e)
   (make-lambda-expression
    (lambda-expression-free-variables e)
    ;; This is a vestigial let*-expression.
    (if (eq? (lambda-expression-free-variables e) #f)
	#f
	(list->vector (map lookup (free-variables e))))
    (lambda-expression-variable e)
    (index (lambda-expression-variable e)
	   (free-variables e)
	   (lambda-expression-body e))))
  ;; This is a vestigial let*-expression.
  ((let*? e)
   (let loop ((xs1 (let*-variables e))
	      (es1 (let*-expressions e))
	      (xs xs)
	      (es2 '()))
    (if (null? xs1)
	(new-let* (let*-variables e) (reverse es2) (index x xs (let*-body e)))
	(loop (rest xs1)
	      (rest es1)
	      ;; needs work: This is not safe-for-space because we don't remove
	      ;;             unused elements of xs.
	      (append xs (list (first xs1)))
	      (cons (index x xs (first es1)) es2)))))
  ((application? e)
   (new-application (index x xs (application-callee e))
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
  ((cons-expression? e)
   (new-cons-expression (cons-expression-tags e)
			(index x xs (cons-expression-car e))
			(index x xs (cons-expression-cdr e))))
  (else (internal-error))))

;;; ANF conversion

(define (anf-result result)
 ;; needs work: Should have structure instead of list.
 (when (and (not (null? (fourth result)))
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
  (map (lambda (b)
	(lambda-expression-variable (variable-binding-expression b)))
       (reverse (fourth result)))
  (map (lambda (b) (lambda-expression-body (variable-binding-expression b)))
       (reverse (fourth result)))
  (new-let* (map variable-binding-variable (reverse (third result)))
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
  ((letrec-expression? e)
   (max
    (reduce
     max (map variable-anf-max (letrec-expression-procedure-variables e)) 0)
    (reduce
     max (map variable-anf-max (letrec-expression-argument-variables e)) 0)
    (reduce max (map anf-max (letrec-expression-bodies e)) 0)
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
 ;; needs work: to make faster
 (anf-result
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
		   (new-lambda-expression
		    (lambda-expression-variable e) (anf-result result)))
		  bs1)
	    bs2)))
    ((let*? e)
     (let inner ((i i)
		 (xs (let*-variables e))
		 (es (let*-expressions e))
		 (bs1 bs1)
		 (bs2 bs2))
      (if (null? xs)
	  (outer i (let*-body e) bs1 bs2)
	  (let ((result (outer i (first es) bs1 bs2)))
	   (inner
	    (first result)
	    (rest xs)
	    (rest es)
	    (cons (make-variable-binding
		   (first xs) (new-variable-access-expression (second result)))
		  (third result))
	    (fourth result))))))
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
    ((letrec-expression? e)
     (let inner ((i i)
		 (xs1 (letrec-expression-procedure-variables e))
		 (xs2 (letrec-expression-argument-variables e))
		 (es (letrec-expression-bodies e))
		 (bs2 bs2))
      (if (null? xs1)
	  (outer i (letrec-expression-body e) bs1 bs2)
	  (let ((result (outer i (first es) '() '())))
	   (inner
	    (first result)
	    (rest xs1)
	    (rest xs2)
	    (rest es)
	    (cons (make-variable-binding
		   (first xs1)
		   (new-lambda-expression (first xs2) (anf-result result)))
		  bs2))))))
    ((cons-expression? e)
     (let* ((result1 (outer i (cons-expression-car e) bs1 bs2))
	    (result2 (outer (first result1)
			    (cons-expression-cdr e)
			    (third result1)
			    (fourth result1)))
	    (i (+ (first result2) 1))
	    (x `(anf ,i)))
      ;; result
      (list i
	    x
	    (cons (make-variable-binding
		   x
		   (new-cons-expression
		    (cons-expression-tags e)
		    (new-variable-access-expression (second result1))
		    (new-variable-access-expression (second result2))))
		  (third result2))
	    (fourth result2))))
    (else (internal-error))))))

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
     (if (let*? (letrec-expression-body e))
	 (let*-variables (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-variables e) '())))

(define (anf-let*-expressions e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-expressions (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-expressions e) '())))

(define (anf-variable e)
 (variable-access-expression-variable
  (if (letrec-expression? e)
      (if (let*? (letrec-expression-body e))
	  (let*-body (letrec-expression-body e))
	  (letrec-expression-body e))
      (if (let*? e) (let*-body e) e))))

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
       ;; ANF should never have letrec.
       ((letrec-expression? e) (internal-error))
       ((cons-expression? e)
	(new-cons-expression (cons-expression-tags e)
			     (substitute x1 x2 (cons-expression-car e))
			     (substitute x1 x2 (cons-expression-cdr e))))
       (else (internal-error))))

(define (copy-propagate e)
 ;; needs work: to make faster
 (let outer ((e e))
  (new-letrec-expression
   (anf-letrec-procedure-variables e)
   (anf-letrec-argument-variables e)
   (map outer (anf-letrec-bodies e))
   (let inner ((xs1 (anf-let*-variables e))
	       (es1 (anf-let*-expressions e))
	       (x (anf-variable e))
	       (xs2 '())
	       (es2 '()))
    (if (null? xs1)
	(new-let*
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
		  (cons (new-lambda-expression
			 (lambda-expression-variable e1)
			 (outer (lambda-expression-body e1)))
			es2)))
	  ((application? e1)
	   (inner (rest xs1) (rest es1) x (cons x1 xs2) (cons e1 es2)))
	  ((cons-expression? e1)
	   (inner (rest xs1) (rest es1) x (cons x1 xs2) (cons e1 es2)))
	  (else (internal-error)))))))))

;;; Constant Conversion

(define (constants-in e)
 (cond ((constant-expression? e) (list (constant-expression-value e)))
       ((variable-access-expression? e) '())
       ((lambda-expression? e) (constants-in (lambda-expression-body e)))
       ((application? e)
	(unionp abstract-value=?
		(constants-in (application-callee e))
		(constants-in (application-argument e))))
       ((letrec-expression? e)
	(unionp abstract-value=?
		(reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
			(map constants-in (letrec-expression-bodies e))
			'())
		(constants-in (letrec-expression-body e))))
       ((cons-expression? e)
	(unionp abstract-value=?
		(constants-in (cons-expression-car e))
		(constants-in (cons-expression-cdr e))))
       (else (internal-error))))

(define (constant-convert bs e)
 (cond ((constant-expression? e)
	(new-variable-access-expression
	 (value-binding-variable
	  (find-if (lambda (b)
		    (abstract-value=? (value-binding-value b)
				      (constant-expression-value e)))
		   bs))))
       ((variable-access-expression? e) e)
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
       ((cons-expression? e)
	(new-cons-expression (cons-expression-tags e)
			     (constant-convert bs (cons-expression-car e))
			     (constant-convert bs (cons-expression-cdr e))))
       (else (internal-error))))

;;; Concrete->Abstract

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
       (else (internal-error))))

(define (macro-expand e)
 (if (list? e)
     (case (first e)
      ((lambda)
       (unless (and (= (length e) 3) (list? (second e)))
	(compile-time-error "Invalid expression: ~s" e))
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
	       (compile-time-error "Invalid parameter: ~s" p))
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
	     (else (compile-time-error "Invalid parameter: ~s" p))))
	   (else (compile-time-error "Invalid parameter: ~s" p)))))
	(else `(lambda ((cons* ,@(second e))) ,(third e)))))
      ((letrec)
       (unless (and (= (length e) 3)
		    (list? (second e))
		    (every
		     (lambda (b)
		      (and (list? b) (= (length b) 2) (variable? (first b))))
		     (second e)))
	(compile-time-error "Invalid expression: ~s" e))
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
       (if *encoded-booleans?*
	   `((,(second e)
	      (cons (lambda () ,(third e)) (lambda () ,(fourth e)))))
	   ;; needs work: to ensure that you don't shadow if-procedure
	   `(if-procedure
	     ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e)))))
      ;; needs work: to ensure that you don't shadow cons-procedure
      ((cons)
       (unless (= (length e) 3)
	(compile-time-error "Invalid expression: ~s" e))
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
   ((null? e) (compile-time-error "Invalid expression: ~s" e))
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((variable? e)
    (unless (memp variable=? e xs)
     (compile-time-error "Unbound variable: ~s" e))
    #f)
   ((list? e)
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (compile-time-error "Invalid expression: ~s" e))
	      #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (compile-time-error "Invalid expression: ~s" e))
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
		   (compile-time-error "Invalid expression: ~s" e))
		  (let ((xs0 (map first (second e))))
		   (when (duplicates? xs0)
		    (compile-time-error "Duplicate variables: ~s" e))
		   (for-each
		    (lambda (b)
		     (let ((e1 (macro-expand (second b))))
		      (unless (and (list? e1)
				   (= (length e1) 3)
				   (eq? (first e1) 'lambda))
		       (compile-time-error "Invalid expression: ~s" e))
		      (loop e1  (append xs0 xs))))
		    (second e))
		   (loop (third e) (append xs0 xs))))))
     ((let) (loop (macro-expand e) xs))
     ((let*) (loop (macro-expand e) xs))
     ((if) (loop (macro-expand e) xs))
     ((cons) (cond (*scott-pairs?* (loop (macro-expand e) xs))
		   (else (unless (= (length e) 3)
			  (compile-time-error "Invalid expression: ~s" e))
			 (loop (second e) xs)
			 (loop (third e) xs))))
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

(define (concrete->abstract-expression e)
 (cond
  ((boolean? e) (concrete->abstract-expression `',e))
  ((real? e) (concrete->abstract-expression `',e))
  ((variable? e) (new-variable-access-expression e))
  ((list? e)
   (case (first e)
    ((quote) (make-constant-expression (internalize (second e))))
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
    ((cons)
     (if *scott-pairs?*
	 (concrete->abstract-expression (macro-expand e))
	 (create-cons-expression (concrete->abstract-expression (second e))
				 (concrete->abstract-expression (third e)))))
    ((cons*) (concrete->abstract-expression (macro-expand e)))
    ((list) (concrete->abstract-expression (macro-expand e)))
    ((cond) (concrete->abstract-expression (macro-expand e)))
    ((and) (concrete->abstract-expression (macro-expand e)))
    ((or) (concrete->abstract-expression (macro-expand e)))
    (else (case (length (rest e))
	   ((0) (concrete->abstract-expression (macro-expand e)))
	   ((1) (new-application (concrete->abstract-expression (first e))
				 (concrete->abstract-expression (second e))))
	   (else (concrete->abstract-expression (macro-expand e)))))))
  (else (internal-error))))

(define (parse e)
 (let* ((e (concrete->abstract-expression e))
	(bs (map (lambda (v) (make-value-binding (gensym) v))
		 (constants-in e)))
	(e (constant-convert bs e))
	;; debugging
	(e (if *flow-analysis?*
	       (alpha-convert e (free-variables e))
	       (copy-propagate
		(anf-convert (alpha-convert e (free-variables e))))))
	(xs (free-variables e))
	(bs (append bs *value-bindings*)))
  (list
   (index #f xs e)
   (map (lambda (x)
	 (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))
	xs))))

;;; AD

(define (zero v)
 (cond
  ((null? v) v)
  ((and (not *encoded-booleans?*) (abstract-boolean? v)) v)
  ((abstract-real? v) (if (and (not *run?*) *imprecise-zero?*) 'real 0))
  ((primitive-procedure? v) v)
  ((nonrecursive-closure? v)
   (let ((e (new-lambda-expression (closure-variable v) (closure-body v))))
    (make-nonrecursive-closure
     (free-variables e)
     ;; This assumes that the closure variables are in the same order.
     (map-vector zero (closure-values v))
     (lambda-expression-variable e)
     (lambda-expression-body e))))
  ((recursive-closure? v)
   (let ((es (map-vector new-lambda-expression
			 (recursive-closure-argument-variables v)
			 (recursive-closure-bodies v))))
    (make-recursive-closure
     ;; This assumes that the closure variables are in the same order.
     (closure-variables v)
     (map-vector zero (closure-values v))
     (recursive-closure-procedure-variables v)
     (map-vector lambda-expression-variable es)
     (map-vector lambda-expression-body es)
     (recursive-closure-index v))))
  ((bundle? v)
   (make-bundle (zero (bundle-primal v)) (zero (bundle-tangent v))))
  ((reverse-tagged-value? v)
   (make-reverse-tagged-value (zero (reverse-tagged-value-primal v))))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   (make-tagged-pair (tagged-pair-tags v)
		     (zero (vlad-car v (tagged-pair-tags v)))
		     (zero (vlad-cdr v (tagged-pair-tags v)))))
  (else (internal-error))))

;;; Forward Mode

(define (forward-transform e)
 (cond ((variable-access-expression? e) (forwardify-access e))
       ((lambda-expression? e)
	(new-lambda-expression (forwardify (lambda-expression-variable e))
			       (forward-transform (lambda-expression-body e))))
       ((application? e)
	(new-application (forward-transform (application-callee e))
			 (forward-transform (application-argument e))))
       ((letrec-expression? e)
	(new-letrec-expression
	 (map forwardify (letrec-expression-procedure-variables e))
	 (map forwardify (letrec-expression-argument-variables e))
	 (map forward-transform (letrec-expression-bodies e))
	 (forward-transform (letrec-expression-body e))))
       ((cons-expression? e)
	(new-cons-expression (cons 'forward (cons-expression-tags e))
			     (forward-transform (cons-expression-car e))
			     (forward-transform (cons-expression-cdr e))))
       (else (internal-error))))

(define (forward-transform-inverse e)
 (cond
  ((variable-access-expression? e) (unforwardify-access e))
  ((lambda-expression? e)
   (new-lambda-expression
    (unforwardify (lambda-expression-variable e))
    (forward-transform-inverse (lambda-expression-body e))))
  ((application? e)
   (new-application (forward-transform-inverse (application-callee e))
		    (forward-transform-inverse (application-argument e))))
  ((letrec-expression? e)
   (new-letrec-expression
    (map unforwardify (letrec-expression-procedure-variables e))
    (map unforwardify (letrec-expression-argument-variables e))
    (map forward-transform-inverse (letrec-expression-bodies e))
    (forward-transform-inverse (letrec-expression-body e))))
  ((cons-expression? e)
   (unless (memq 'forward (cons-expression-tags e)) (internal-error))
   (new-cons-expression (remove-oneq 'forward (cons-expression-tags e))
			(forward-transform-inverse (cons-expression-car e))
			(forward-transform-inverse (cons-expression-cdr e))))
  (else (internal-error))))

(define (primal v-forward)
 (cond
  ((null? v-forward)
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((and (not *encoded-booleans?*) (abstract-boolean? v-forward))
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((abstract-real? v-forward)
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((primitive-procedure? v-forward)
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((nonrecursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error "Attempt to take primal of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (abstract-value=? v-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let ((e (forward-transform-inverse
		  (new-lambda-expression
		   (closure-variable v-forward) (closure-body v-forward)))))
	 (make-nonrecursive-closure
	  (free-variables e)
	  ;; This assumes that the closure variables are in the same order.
	  (map-vector primal (closure-values v-forward))
	  (lambda-expression-variable e)
	  (index (lambda-expression-variable e)
		 (free-variables e)
		 (lambda-expression-body e)))))))
  ((recursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error "Attempt to take primal of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (abstract-value=? v-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let* ((es (vector->list
		    (map-vector
		     (lambda (x e)
		      (forward-transform-inverse (new-lambda-expression x e)))
		     (recursive-closure-argument-variables v-forward)
		     (recursive-closure-bodies v-forward))))
	       (xs1 (map-vector
		     unforwardify
		     (recursive-closure-procedure-variables v-forward)))
	       (xs (letrec-recursive-closure-variables
		    (vector->list xs1)
		    (map lambda-expression-variable es)
		    (map lambda-expression-body es)))
	       (xs2 (append (vector->list xs1) xs)))
	 (make-recursive-closure
	  xs
	  ;; This assumes that the closure variables are in the same order.
	  (map-vector primal (closure-values v-forward))
	  xs1
	  (list->vector (map lambda-expression-variable es))
	  (list->vector
	   (map (lambda (e)
		 (index (lambda-expression-variable e)
			xs2
			(lambda-expression-body e)))
		es))
	  (recursive-closure-index v-forward))))))
  ((bundle? v-forward)
   (if (scalar-value? (bundle-primal v-forward))
       (bundle-primal v-forward)
       (make-bundle (primal (bundle-primal v-forward))
		    (primal (bundle-tangent v-forward)))))
  ((reverse-tagged-value? v-forward)
   (make-reverse-tagged-value
    (primal (reverse-tagged-value-primal v-forward))))
  ((and (not *scott-pairs?*) (tagged-pair? v-forward))
   (unless (memq 'forward (tagged-pair-tags v-forward))
    (run-time-error "Attempt to take primal of a non-forward value" v-forward))
   (make-tagged-pair (remove-oneq 'forward (tagged-pair-tags v-forward))
		     (primal (tagged-pair-car v-forward))
		     (primal (tagged-pair-cdr v-forward))))
  (else (internal-error))))

(define (tangent v-forward)
 (cond
  ((null? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((and (not *encoded-booleans?*) (abstract-boolean? v-forward))
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((abstract-real? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((primitive-procedure? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((nonrecursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error
     "Attempt to take tangent of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (abstract-value=? v-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let ((e (forward-transform-inverse
		  (new-lambda-expression
		   (closure-variable v-forward) (closure-body v-forward)))))
	 (make-nonrecursive-closure
	  (free-variables e)
	  ;; This assumes that the closure variables are in the same order.
	  (map-vector tangent (closure-values v-forward))
	  (lambda-expression-variable e)
	  (index (lambda-expression-variable e)
		 (free-variables e)
		 (lambda-expression-body e)))))))
  ((recursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error
     "Attempt to take tangent of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (abstract-value=? v-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let* ((es (vector->list
		    (map-vector
		     (lambda (x e)
		      (forward-transform-inverse
		       (new-lambda-expression x e)))
		     (recursive-closure-argument-variables v-forward)
		     (recursive-closure-bodies v-forward))))
	       (xs1 (map-vector
		     unforwardify
		     (recursive-closure-procedure-variables v-forward)))
	       (xs (letrec-recursive-closure-variables
		    (vector->list xs1)
		    (map lambda-expression-variable es)
		    (map lambda-expression-body es)))
	       (xs2 (append (vector->list xs1) xs)))
	 (make-recursive-closure
	  xs
	  ;; This assumes that the closure variables are in the same order.
	  (map-vector tangent (closure-values v-forward))
	  xs1
	  (list->vector (map lambda-expression-variable es))
	  (list->vector
	   (map (lambda (e)
		 (index (lambda-expression-variable e)
			xs2
			(lambda-expression-body e)))
		es))
	  (recursive-closure-index v-forward))))))
  ((bundle? v-forward)
   (if (scalar-value? (bundle-primal v-forward))
       (bundle-tangent v-forward)
       (make-bundle (tangent (bundle-primal v-forward))
		    (tangent (bundle-tangent v-forward)))))
  ((reverse-tagged-value? v-forward)
   (make-reverse-tagged-value
    (tangent (reverse-tagged-value-primal v-forward))))
  ((and (not *scott-pairs?*) (tagged-pair? v-forward))
   (unless (memq 'forward (tagged-pair-tags v-forward))
    (run-time-error
     "Attempt to take tangent of a non-forward value" v-forward))
   (make-tagged-pair (remove-oneq 'forward (tagged-pair-tags v-forward))
		     (tangent (tagged-pair-car v-forward))
		     (tangent (tagged-pair-cdr v-forward))))
  (else (internal-error))))

(define (legitimate? v v-perturbation)
 (or (and (null? v) (null? v-perturbation))
     (and (not *encoded-booleans?*)
	  (abstract-boolean? v)
	  (abstract-boolean? v-perturbation)
	  (or (eq? v 'boolean)
	      (eq? v-perturbation 'boolean)
	      (eq? v v-perturbation)))
     (and (abstract-real? v) (abstract-real? v-perturbation))
     (and (primitive-procedure? v)
	  (primitive-procedure? v-perturbation)
	  (eq? v v-perturbation))
     (and (nonrecursive-closure? v)
	  (nonrecursive-closure? v-perturbation)
	  (nonrecursive-closure-match? v v-perturbation)
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in
	  ;; abstract-environment=?.
	  (every-vector
	   legitimate? (closure-values v) (closure-values v-perturbation)))
     (and (recursive-closure? v)
	  (recursive-closure? v-perturbation)
	  (recursive-closure-match? v v-perturbation)
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in
	  ;; abstract-environment=?.
	  (every-vector
	   legitimate? (closure-values v) (closure-values v-perturbation)))
     (and (bundle? v)
	  (bundle? v-perturbation)
	  (legitimate? (bundle-primal v) (bundle-primal v-perturbation))
	  (legitimate? (bundle-tangent v) (bundle-tangent v-perturbation)))
     (and (reverse-tagged-value? v)
	  (reverse-tagged-value? v-perturbation)
	  (legitimate? (reverse-tagged-value-primal v)
		       (reverse-tagged-value-primal v-perturbation)))
     (and (not *scott-pairs?*)
	  (tagged-pair? v)
	  (tagged-pair? v-perturbation)
	  (equal-tags? (tagged-pair-tags v) (tagged-pair-tags v-perturbation))
	  (legitimate? (tagged-pair-car v) (tagged-pair-car v-perturbation))
	  (legitimate? (tagged-pair-cdr v) (tagged-pair-cdr v-perturbation)))))

(define (bundle-internal v v-perturbation)
 (cond
  ((null? v) (make-bundle v v-perturbation))
  ((and (not *encoded-booleans?*) (abstract-boolean? v))
   (make-bundle v v-perturbation))
  ((abstract-real? v) (make-bundle v v-perturbation))
  ((primitive-procedure? v) (primitive-procedure-forward v))
  ((nonrecursive-closure? v)
   (let ((e (forward-transform
	     (new-lambda-expression (closure-variable v) (closure-body v)))))
    (make-nonrecursive-closure
     (free-variables e)
     ;; This assumes that the corresponding closure variables in v,
     ;; v-perturbation, and v-forward are in the same order. See the note in
     ;; abstract-environment=?.
     (map-vector
      bundle-internal (closure-values v) (closure-values v-perturbation))
     (lambda-expression-variable e)
     (index (lambda-expression-variable e)
	    (free-variables e)
	    (lambda-expression-body e)))))
  ((recursive-closure? v)
   (let* ((es (vector->list
	       (map-vector
		(lambda (x e) (forward-transform (new-lambda-expression x e)))
		(recursive-closure-argument-variables v)
		(recursive-closure-bodies v))))
	  (xs1 (map-vector forwardify
			   (recursive-closure-procedure-variables v)))
	  (xs (letrec-recursive-closure-variables
	       (vector->list xs1)
	       (map lambda-expression-variable es)
	       (map lambda-expression-body es)))
	  (xs2 (append (vector->list xs1) xs)))
    (make-recursive-closure
     xs
     ;; This assumes that the corresponding closure variables in v,
     ;; v-perturbation, and v-forward are in the same order. See the note in
     ;; abstract-environment=?.
     (map-vector
      bundle-internal (closure-values v) (closure-values v-perturbation))
     xs1
     (list->vector (map lambda-expression-variable es))
     (list->vector
      (map
       (lambda (e)
	(index (lambda-expression-variable e) xs2 (lambda-expression-body e)))
       es))
     (recursive-closure-index v))))
  ((bundle? v)
   (make-bundle
    (bundle-internal (bundle-primal v) (bundle-primal v-perturbation))
    (bundle-internal (bundle-tangent v) (bundle-tangent v-perturbation))))
  ((reverse-tagged-value? v)
   (make-reverse-tagged-value
    (bundle-internal (reverse-tagged-value-primal v)
		     (reverse-tagged-value-primal v-perturbation))))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   (make-tagged-pair
    (cons 'forward (tagged-pair-tags v))
    (bundle-internal (tagged-pair-car v) (tagged-pair-car v-perturbation))
    (bundle-internal (tagged-pair-cdr v) (tagged-pair-cdr v-perturbation))))
  (else (internal-error))))

(define (bundle v v-perturbation)
 (unless (legitimate? v v-perturbation)
  (run-time-error
   "The arguments to bundle are illegitimate" v v-perturbation))
 (bundle-internal v v-perturbation))

;;; Base variables
;;; needs work: This whole section will be removed when we update reverse mode.

(define (base-variables x) (unimplemented "base-variables"))

(define (nonrecursive-closure-base-letrec-variables x)
 (unimplemented "nonrecursive-closure-base-letrec-variables"))

(define (recursive-closure-base-letrec-variables x i)
 (unimplemented "recursive-closure-base-letrec-variables"))

(define (lambda-expression-base-free-variables e)
 (unimplemented "lambda-expression-base-free-variables"))

(define (anf-letrec-bodies-base-free-variables e)
 (unimplemented "anf-letrec-bodies-base-free-variables"))

;;; Reverse Mode

(define (added-variable bs v)
 (new-variable-access-expression
  (alpha-binding-variable2
   (find-if (lambda (b) (variable=? v (alpha-binding-variable1 b))) bs))))

(define (make-zero bs e) (new-application (added-variable bs 'zero) e))

(define (make-plus bs e1 e2)
 (create-application bs '() (added-variable bs 'plus) e1 e2))

(define (make-primal bs e) (new-application (added-variable bs 'primal) e))

(define (make-tangent bs e) (new-application (added-variable bs 'tangent) e))

(define (make-bundle-invocation bs e1 e2)
 (create-application bs '() (added-variable bs 'bundle) e1 e2))

(define (make-j* bs e) (new-application (added-variable bs 'j*) e))

(define (make-*j bs e) (new-application (added-variable bs '*j) e))

(define (make-*j-inverse bs e)
 (new-application (added-variable bs '*j-inverse) e))

(define (tagify bs tags e)
 ;; needs work: direct tags
 (let loop ((tags tags))
  (if (null? tags)
      e
      ((case (first tags)
	;; needs work: other tags
	((forward) make-j*)
	((reverse) make-*j)
	(else (internal-error)))
       bs
       (loop (rest tags))))))

(define (make-car bs tags e)
 ;; needs work: direct tags
 ;; We no longer do car-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'car) e)
     (case (first tags)
      ;; needs work: other tags
      ((forward)
       (make-bundle-invocation bs
			       (make-car bs (rest tags) (make-primal bs e))
			       (make-car bs (rest tags) (make-tangent bs e))))
      ((reverse) (make-*j bs (make-car bs (rest tags) (make-*j-inverse bs e))))
      (else (internal-error)))))

(define (make-cdr bs tags e)
 ;; needs work: direct tags
 ;; We no longer do cdr-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'cdr) e)
     (case (first tags)
      ;; needs work: other tags
      ((forward)
       (make-bundle-invocation bs
			       (make-cdr bs (rest tags) (make-primal bs e))
			       (make-cdr bs (rest tags) (make-tangent bs e))))
      ((reverse) (make-*j bs (make-cdr bs (rest tags) (make-*j-inverse bs e))))
      (else (internal-error)))))

(define (make-cons bs tags e1 e2)
 (if *scott-pairs?*
     (if (null? tags)
	 (new-application
	  (new-application (added-variable bs 'cons-procedure) e1) e2)
	 (case (first tags)
	  ;; needs work: other tags
	  ((forward) (make-bundle-invocation bs
					     (make-cons bs
							(rest tags)
							(make-primal bs e1)
							(make-primal bs e2))
					     (make-cons bs
							(rest tags)
							(make-tangent bs e1)
							(make-tangent bs e2))))
	  ((reverse) (make-*j bs
			      (make-cons bs
					 (rest tags)
					 (make-*j-inverse bs e1)
					 (make-*j-inverse bs e2))))
	  (else (internal-error))))
     (new-cons-expression tags e1 e2)))

(define (make-cons* bs tags es)
 (cond ((null? es) (tagify bs tags (added-variable bs 'null)))
       ((null? (rest es)) (first es))
       (else (make-cons bs tags (first es) (make-cons* bs tags (rest es))))))

(define (make-list-invocation bs tags es)
 (if (null? es)
     (tagify bs tags (added-variable bs 'null))
     (make-cons bs tags (first es) (make-list-invocation bs tags (rest es)))))

(define (make-cons-bindings bs tags x0 x1 e)
 (let ((x (parameter->consvar `(cons ,x0 ,x1))))
  (list (make-variable-binding x e)
	(make-variable-binding
	 x0 (make-car bs tags (new-variable-access-expression x)))
	(make-variable-binding
	 x1 (make-cdr bs tags (new-variable-access-expression x))))))

(define (make-list-bindings bs tags xs e)
 (if (null? xs)
     '()
     (let ((x (parameter->consvar `(list ,@xs))))
      (cons
       (make-variable-binding x e)
       (let loop ((xs xs) (x x))
	(if (null? (rest xs))
	    (list (make-variable-binding
		   (first xs)
		   (make-car bs tags (new-variable-access-expression x))))
	    (cons (make-variable-binding
		   (first xs)
		   (make-car bs tags (new-variable-access-expression x)))
		  (cons (make-variable-binding
			 (third x)
			 (make-cdr bs tags (new-variable-access-expression x)))
			(loop (rest xs) (third x))))))))))

(define (reverse-transform bs e ws gs zs)
 (let* ((tags (lambda-expression-tags e))
	(x (lambda-expression-variable e))
	(e1 (lambda-expression-body e))
	(fs (anf-letrec-procedure-variables e1))
	(needed? (lambda (x1)
		  (or (variable=? x1 x)
		      (memp variable=? x1 (anf-let*-variables e1))
		      (memp variable=? x1 fs)
		      (memp variable=? x1 gs)
		      (memp variable=? x1 zs))))
	(bs0
	 (reduce
	  append
	  (map
	   (lambda (t e)
	    (cond
	     ((variable-access-expression? e)
	      (let ((x1 (variable-access-expression-variable e)))
	       (if (needed? x1)
		   (list (make-variable-binding
			  (sensitivityify x1)
			  (make-plus
			   bs (sensitivity-access x1) (sensitivity-access t))))
		   '())))
	     ((lambda-expression? e)
	      (let ((xs (lambda-expression-base-free-variables e)))
	       (if (null? xs)
		   '()
		   (let ((x (parameter->consvar
			     `(list ,@(map sensitivityify xs)))))
		    (cons
		     (make-variable-binding x (sensitivity-access t))
		     (let loop ((xs xs) (x x))
		      (if (null? (rest xs))
			  (if (needed? (first xs))
			      (list (make-variable-binding
				     (sensitivityify (first xs))
				     (make-plus
				      bs
				      (sensitivity-access (first xs))
				      (make-car
				       bs
				       (lambda-expression-tags e)
				       (new-variable-access-expression x)))))
			      '())
			  (if (needed? (first xs))
			      (cons
			       (make-variable-binding
				(sensitivityify (first xs))
				(make-plus
				 bs
				 (sensitivity-access (first xs))
				 (make-car
				  bs
				  (lambda-expression-tags e)
				  (new-variable-access-expression x))))
			       (if (some needed? (rest xs))
				   (cons (make-variable-binding
					  (third x)
					  (make-cdr
					   bs
					   (lambda-expression-tags e)
					   (new-variable-access-expression x)))
					 (loop (rest xs) (third x)))
				   '()))
			      (if (some needed? (rest xs))
				  (cons (make-variable-binding
					 (third x)
					 (make-cdr
					  bs
					  (lambda-expression-tags e)
					  (new-variable-access-expression x)))
					(loop (rest xs) (third x)))
				  '())))))))))
	     ((application? e)
	      (let ((x1 (variable-access-expression-variable
			 (application-callee e)))
		    (x2 (variable-access-expression-variable
			 (application-argument e))))
	       (reduce
		append
		(list
		 (if (or (needed? x1) (needed? x2))
		     (list
		      (make-variable-binding
		       `(consvar ,(sensitivityify x1) ,(sensitivityify x2))
		       (new-application
			(backpropagator-access t) (sensitivity-access t))))
		     '())
		 (if (needed? x1)
		     (list (make-variable-binding
			    (sensitivityify x1)
			    (make-plus bs
				       (sensitivity-access x1)
				       (make-car
					bs
					'()
					(new-variable-access-expression
					 `(consvar ,(sensitivityify x1)
						   ,(sensitivityify x2)))))))
		     '())
		 (if (needed? x2)
		     (list (make-variable-binding
			    (sensitivityify x2)
			    (make-plus bs
				       (sensitivity-access x2)
				       (make-cdr
					bs
					'()
					(new-variable-access-expression
					 `(consvar ,(sensitivityify x1)
						   ,(sensitivityify x2)))))))
		     '()))
		'())))
	     ((cons-expression? e)
	      (let ((x1 (variable-access-expression-variable
			 (cons-expression-car e)))
		    (x2 (variable-access-expression-variable
			 (cons-expression-cdr e))))
	       (reduce
		append
		(list
		 (if (needed? x1)
		     (list (make-variable-binding
			    (sensitivityify x1)
			    (make-plus bs
				       (sensitivity-access x1)
				       (make-car bs
						 (cons-expression-tags e)
						 (sensitivity-access t)))))
		     '())
		 (if (needed? x2)
		     (list (make-variable-binding
			    (sensitivityify x2)
			    (make-plus bs
				       (sensitivity-access x2)
				       (make-cdr bs
						 (cons-expression-tags e)
						 (sensitivity-access t)))))
		     '()))
		'())))
	     (else (internal-error))))
	   (reverse (anf-let*-variables e1))
	   (reverse (anf-let*-expressions e1)))
	  '()))
	(e2
	 (create-let*
	  (reduce
	   append
	   (map
	    (lambda (x e)
	     (cond
	      ((variable-access-expression? e)
	       (list
		(make-variable-binding (reverseify x) (reverseify-access e))))
	      ((lambda-expression? e)
	       (list (make-variable-binding
		      (reverseify x)
		      (reverse-transform
		       bs
		       e
		       (anf-letrec-bodies-base-free-variables e)
		       '()
		       (lambda-expression-base-free-variables e)))))
	      ((application? e)
	       (make-cons-bindings
		bs
		'()
		(reverseify x)
		(backpropagatorify x)
		(new-application
		 (reverseify-access (application-callee e))
		 (reverseify-access (application-argument e)))))
	      ((cons-expression? e)
	       (list (make-variable-binding
		      (reverseify x)
		      (new-cons-expression
		       (cons 'reverse (cons-expression-tags e))
		       (reverseify-access (cons-expression-car e))
		       (reverseify-access (cons-expression-cdr e))))))
	      (else (internal-error))))
	    (anf-let*-variables e1)
	    (anf-let*-expressions e1))
	   '())
	  (make-cons
	   bs
	   '()
	   (reverse-access (anf-variable e1))
	   (let ((e4
		  (create-let*
		   (append
		    (map
		     (lambda (x)
		      (make-variable-binding
		       (sensitivityify x)
		       (make-zero bs (make-*j-inverse bs (reverse-access x)))))
		     (removep
		      variable=?
		      (anf-variable e1)
		      (cons x (append (anf-let*-variables e1) fs gs zs))))
		    bs0
		    (make-list-bindings
		     bs
		     tags
		     (map sensitivityify ws)
		     (let loop ((fs fs))
		      (if (null? fs)
			  (make-list-invocation
			   bs tags (map sensitivity-access ws))
			  (make-plus bs
				     (sensitivity-access (first fs))
				     (loop (rest fs)))))))
		   (make-cons
		    bs
		    '()
		    (let loop ((gs gs))
		     (if (null? gs)
			 (make-list-invocation
			  bs tags (map sensitivity-access zs))
			 (make-plus
			  bs
			  (sensitivity-access (first gs)) (loop (rest gs)))))
		    (sensitivity-access x)))))
	    (new-lambda-expression (sensitivityify (anf-variable e1)) e4))))))
  (new-lambda-expression
   (reverseify x)
   (if (null? fs)
       e2
       (let ((es
	      (map (lambda (x e3)
		    (let ((e5 (new-lambda-expression x e3)))
		     (reverse-transform
		      bs e5 (anf-letrec-bodies-base-free-variables e5) fs ws)))
		   (letrec-expression-argument-variables e1)
		   (letrec-expression-bodies e1))))
	(new-letrec-expression (map reverseify fs)
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
  (null? (cons-expression-tags e2))
  ;; Technically not needed since in ANF.
  (variable-access-expression? (cons-expression-car e2))
  ;; Technically not needed since in ANF.
  (variable-access-expression? (cons-expression-cdr e2))
  (variable=?
   (variable-access-expression-variable (cons-expression-cdr e2)) x1)
  ;; Technically not needed since in ANF.
  (variable-access-expression? e)
  (variable=? (variable-access-expression-variable e) x2)))

(define (cons-split? x1 x2 x3 e1 e2 e3)
 ;; x1=xa xb
 ;; x2=car x1
 ;; x3=cdr x1
 ;; --------------------------------------------
 ;; x2=xa xb
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
 (unless (let*? e) (internal-error))
 (let loop ((xs (let*-variables e))
	    (es (let*-expressions e))
	    (xs0 '())
	    (es0 '()))
  (cond
   ((null? xs) (internal-error))
   ((and (= (length xs) 3)
	 (result-cons? (first xs) (second xs) (third xs)
		       (first es) (second es) (third es)
		       (let*-body e)))
    (if (null? xs0)
	(unreverseify-access (partial-cons-argument (first es)))
	(new-let* (reverse xs0)
		  (reverse es0)
		  (unreverseify-access (partial-cons-argument (first es))))))
   ((and (= (length xs) 2)
	 (result-cons-expression?
	  (first xs) (second xs) (first es) (second es) (let*-body e)))
    (if (null? xs0)
	(unreverseify-access (cons-expression-car (second es)))
	(new-let* (reverse xs0)
		  (reverse es0)
		  (unreverseify-access (cons-expression-car (second es))))))
   ((and (>= (length xs) 3)
	 (cons-split? (first xs) (second xs) (third xs)
		      (first es) (second es) (third es)))
    (loop (rest (rest (rest xs)))
	  (rest (rest (rest es)))
	  (cons (unreverseify (second xs)) xs0)
	  (cons (new-application
		 (unreverseify-access (application-callee (first es)))
		 (unreverseify-access (application-argument (first es))))
		es0)))
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
		 (rest (cons-expression-tags (first es)))
		 (unreverseify-access (cons-expression-car (first es)))
		 (unreverseify-access (cons-expression-cdr (first es))))
		es0)))
   (else (internal-error)))))

(define (reverse-transform-inverse e)
 (new-lambda-expression
  (unreverseify (lambda-expression-variable e))
  (let ((e (lambda-expression-body e)))
   (if (letrec-expression? e)
       (new-letrec-expression
	(map unreverseify (letrec-expression-procedure-variables e))
	(map unreverseify (letrec-expression-argument-variables e))
	(map reverse-transform-inverse-internal (letrec-expression-bodies e))
	(reverse-transform-inverse-internal (letrec-expression-body e)))
       (reverse-transform-inverse-internal e)))))

(define (added-value x)
 (if *scott-pairs?*
     (case x
      ;; These are magic names.
      ((null) '())
      ((car) (evaluate-in-top-level-environment 'car))
      ((cdr) (evaluate-in-top-level-environment 'cdr))
      ((cons-procedure) (evaluate-in-top-level-environment 'cons-procedure))
      (else (value-binding-value
	     (find-if (lambda (b) (variable=? (value-binding-variable b) x))
		      *value-bindings*))))
     (case x
      ;; This is a magic name.
      ((null) '())
      (else (value-binding-value
	     (find-if (lambda (b) (variable=? (value-binding-variable b) x))
		      *value-bindings*))))))

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

(define (added-bindings)
 ;; needs work: To replace anonymous gensym with derived gensym.
 (map (lambda (x) (make-alpha-binding x (hensym)))
      ;; These are magic names.
      (append (if *scott-pairs?*
		  (list 'null 'car 'cdr 'cons-procedure)
		  (list 'null))
	      (map value-binding-variable *value-bindings*))))

(define (conform? v1 v2)
 (or (and (null? v1) (null? v2))
     (and (not *encoded-booleans?*)
	  (abstract-boolean? v1)
	  (abstract-boolean? v1)
	  (eq? v1 v2))
     (and (abstract-real? v1) (abstract-real? v2))
     (and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (nonrecursive-closure-match? v1 v2)
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in
	  ;; abstract-environment=?.
	  (every-vector conform? (closure-values v1) (closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (recursive-closure-match? v1 v2)
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in
	  ;; abstract-environment=?.
	  (every-vector conform? (closure-values v1) (closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (conform? (bundle-primal v1) (bundle-primal v2))
	  (conform? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (conform? (reverse-tagged-value-primal v1)
		    (reverse-tagged-value-primal v2)))
     (and (not *scott-pairs?*)
	  (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (conform? (tagged-pair-car v1) (tagged-pair-car v2))
	  (conform? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))))

(define (plus-internal v1 v2)
 (cond
  ((null? v1) v1)
  ((and (not *encoded-booleans?*) (abstract-boolean? v1)) v1)
  ((eq? v1 'real) 'real)
  ((eq? v2 'real) 'real)
  ((abstract-real? v1) (+ v1 v2))
  ((primitive-procedure? v1) v1)
  ((nonrecursive-closure? v1)
   (let ((e (new-lambda-expression (closure-variable v1) (closure-body v2))))
    (make-nonrecursive-closure
     (free-variables e)
     ;; This assumes that the corresponding closure variables in v1 and
     ;; v2 are in the same order. See the note in abstract-environment=?.
     (map-vector plus-internal (closure-values v1) (closure-values v2))
     (lambda-expression-variable e)
     (lambda-expression-body e))))
  ((recursive-closure? v1)
   (let ((es (map-vector new-lambda-expression
			 (recursive-closure-argument-variables v1)
			 (recursive-closure-bodies v1))))
    (make-recursive-closure
     ;; This assumes that the corresponding closure variables in v1 and
     ;; v2 are in the same order. See the note in abstract-environment=?.
     (closure-variables v1)
     (map-vector plus-internal (closure-values v1) (closure-values v2))
     (recursive-closure-procedure-variables v1)
     (map-vector lambda-expression-variable es)
     (map-vector lambda-expression-body es)
     (recursive-closure-index v1))))
  ((bundle? v1)
   (make-bundle (plus-internal (bundle-primal v1) (bundle-primal v2))
		(plus-internal (bundle-tangent v1) (bundle-tangent v2))))
  ((reverse-tagged-value? v1)
   (make-reverse-tagged-value
    (plus-internal (reverse-tagged-value-primal v1)
		   (reverse-tagged-value-primal v2))))
  ((and (not *scott-pairs?*) (tagged-pair? v1))
   (make-tagged-pair
    (tagged-pair-tags v1)
    (plus-internal (tagged-pair-car v1) (tagged-pair-car v2))
    (plus-internal (tagged-pair-cdr v1) (tagged-pair-cdr v2))))
  (else (internal-error))))

(define (plus v1 v2)
 (unless (conform? v1 v2)
  (run-time-error "The arguments to plus are nonconformant" v1 v2))
 (plus-internal v1 v2))

(define (*j v)
 (cond
  ((null? v) (make-reverse-tagged-value v))
  ((and (not *encoded-booleans?*) (abstract-boolean? v))
   (make-reverse-tagged-value v))
  ((abstract-real? v) (make-reverse-tagged-value v))
  ((primitive-procedure? v) (primitive-procedure-reverse v))
  ((nonrecursive-closure? v)
   (let* ((bs (added-bindings))
	  (e (reverse-transform
	      bs
	      (new-lambda-expression (closure-variable v) (closure-body v))
	      (nonrecursive-closure-base-letrec-variables v)
	      '()
	      (base-variables v)))
	  (e (alpha-convert e (free-variables e)))
	  (x (lambda-expression-variable e))
	  (xs (free-variables e)))
    (make-nonrecursive-closure
     xs
     (add/remove-slots
      *j (map reverseify (closure-variables v)) xs (closure-values v) bs)
     x
     (index x xs (copy-propagate (anf-convert (lambda-expression-body e)))))))
  ((recursive-closure? v)
   (let* ((bs (added-bindings))
	  (es (map-n
	       (lambda (i)
		(let ((x (vector-ref
			  (recursive-closure-argument-variables v) i))
		      (e (vector-ref (recursive-closure-bodies v) i)))
		 (reverse-transform
		  bs
		  (new-lambda-expression x e)
		  (recursive-closure-base-letrec-variables v i)
		  (vector->list (recursive-closure-procedure-variables v))
		  (base-variables v))))
	       (vector-length (recursive-closure-bodies v))))
	  (xs1 (map-vector
		reverseify (recursive-closure-procedure-variables v)))
	  (xs (append (vector->list xs1)
		      (letrec-recursive-closure-variables
		       (vector->list xs1)
		       (map lambda-expression-variable es)
		       (map lambda-expression-body es))))
	  (es (map (lambda (e) (alpha-convert e xs)) es))
	  (xs (letrec-recursive-closure-variables
	       (vector->list xs1)
	       (map lambda-expression-variable es)
	       (map lambda-expression-body es))))
    (make-recursive-closure
     xs
     (add/remove-slots
      *j (map reverseify (closure-variables v)) xs (closure-values v) bs)
     xs1
     (list->vector (map lambda-expression-variable es))
     (list->vector
      (map (lambda (e)
	    (index (lambda-expression-variable e)
		   (append (vector->list xs1) xs)
		   (copy-propagate (anf-convert (lambda-expression-body e)))))
	   es))
     (recursive-closure-index v))))
  ((bundle? v) (make-reverse-tagged-value v))
  ((reverse-tagged-value? v) (make-reverse-tagged-value v))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   (make-tagged-pair (cons 'reverse (tagged-pair-tags v))
		     (*j (tagged-pair-car v))
		     (*j (tagged-pair-cdr v))))
  (else (internal-error))))

(define (*j-inverse v-reverse)
 (cond
  ((null? v-reverse)
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((and (not *encoded-booleans?*) (abstract-boolean? v-reverse))
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((abstract-real? v-reverse)
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((primitive-procedure? v-reverse)
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((nonrecursive-closure? v-reverse)
   (unless (and (not (null? (closure-tags v-reverse)))
		(eq? (first (closure-tags v-reverse)) 'reverse))
    (run-time-error
     "Attempt to take *j-inverse of a non-reverse value" v-reverse))
   (let ((b (find-if (lambda (b)
		      (abstract-value=?
		       v-reverse
		       (primitive-procedure-reverse (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let* ((e (reverse-transform-inverse
		   (new-lambda-expression
		    (closure-variable v-reverse) (closure-body v-reverse))))
	       (x (lambda-expression-variable e))
	       (xs (free-variables e)))
	 (make-nonrecursive-closure
	  xs
	  (add/remove-slots
	   *j-inverse
	   (map lax-unreverseify (closure-variables v-reverse))
	   xs
	   (closure-values v-reverse)
	   '())
	  x
	  (index x xs (copy-propagate (lambda-expression-body e))))))))
  ((recursive-closure? v-reverse)
   (unless (and (not (null? (closure-tags v-reverse)))
		(eq? (first (closure-tags v-reverse)) 'reverse))
    (run-time-error
     "Attempt to take *j-inverse of a non-reverse value" v-reverse))
   (let ((b (find-if (lambda (b)
		      (abstract-value=?
		       v-reverse
		       (primitive-procedure-reverse (value-binding-value b))))
		     *value-bindings*)))
    (if b
	(value-binding-value b)
	(let* ((es (vector->list
		    (map-vector
		     (lambda (x e)
		      (reverse-transform-inverse (new-lambda-expression x e)))
		     (recursive-closure-argument-variables v-reverse)
		     (recursive-closure-bodies v-reverse))))
	       (xs1 (map-vector
		     unreverseify
		     (recursive-closure-procedure-variables v-reverse)))
	       (xs (letrec-recursive-closure-variables
		    (vector->list xs1)
		    (map lambda-expression-variable es)
		    (map lambda-expression-body es))))
	 (make-recursive-closure
	  xs
	  (add/remove-slots
	   *j-inverse
	   (map lax-unreverseify (closure-variables v-reverse))
	   xs
	   (closure-values v-reverse)
	   '())
	  xs1
	  (list->vector (map lambda-expression-variable es))
	  (list->vector
	   (map (lambda (e)
		 (index (lambda-expression-variable e)
			(append (vector->list xs1) xs)
			(copy-propagate (lambda-expression-body e))))
		es))
	  (recursive-closure-index v-reverse))))))
  ((bundle? v-reverse)
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((reverse-tagged-value? v-reverse)
   (reverse-tagged-value-primal v-reverse))
  ((and (not *scott-pairs?*) (tagged-pair? v-reverse))
   (unless (and (not (null? (tagged-pair-tags v-reverse)))
		(eq? (first (tagged-pair-tags v-reverse)) 'reverse))
    (run-time-error
     "Attempt to take primal of a non-reverse value" v-reverse))
   (make-tagged-pair (rest (tagged-pair-tags v-reverse))
		     (*j-inverse (tagged-pair-car v-reverse))
		     (*j-inverse (tagged-pair-cdr v-reverse))))
  (else (internal-error))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (abstract->concrete e)
 (cond
  ((let*? e)
   (let loop ((xs (let*-variables e)) (es (let*-expressions e)) (bs '()))
    (cond
     ((null? xs)
      (case (length bs)
       ((0) (internal-error))
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
     ((and *unabbreviate-nicely?*
	   (= (length xs) 2)
	   (result-cons-expression?
	    (first xs) (second xs) (first es) (second es) (let*-body e)))
      (case (length bs)
       ((0) `(cons ,(abstract->concrete (cons-expression-car (second es)))
		   ,(abstract->concrete (first es))))
       ((1) `(let ,bs
	      (cons ,(abstract->concrete (cons-expression-car (second es)))
		    ,(abstract->concrete (first es)))))
       (else `(let* ,(reverse bs)
	       (cons ,(abstract->concrete (cons-expression-car (second es)))
		     ,(abstract->concrete (first es)))))))
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
  ((cons-expression? e)
   (if (null? (cons-expression-tags e))
       `(cons ,(abstract->concrete (cons-expression-car e))
	      ,(abstract->concrete (cons-expression-cdr e)))
       `(cons ,(cons-expression-tags e)
	      ,(abstract->concrete (cons-expression-car e))
	      ,(abstract->concrete (cons-expression-cdr e)))))
  (else (internal-error))))

(define (quotable? v)
 (cond ((and (not *unabbreviate-transformed?*) (vlad-forward? v)) #f)
       ((and (not *unabbreviate-transformed?*) (vlad-reverse? v)) #f)
       ((null? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((eq? v 'boolean) #f)
       ((real? v) #t)
       ((eq? v 'real) #f)
       ((vlad-pair? v '())
	(and (quotable? (vlad-car v '())) (quotable? (vlad-cdr v '()))))
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
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *scott-pairs?*) (tagged-pair? v)))
		(vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(bundle ,(loop (primal v) quote?)
			   ,(loop (tangent v) quote?)))
		 (else `(forward ,(loop (primal v) quote?)
				 ,(loop (tangent v) quote?)))))
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *scott-pairs?*) (tagged-pair? v)))
		(vlad-reverse? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(*j ,(loop (*j-inverse v) quote?)))
		 (else `(reverse ,(loop (*j-inverse v) quote?)))))
	  ((null? v)
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
	  ((vlad-pair? v '())
	   (if (and *unabbreviate-executably?* (not quote?))
	       (if (quotable? v)
		   `',(cons (loop (vlad-car v '()) #t)
			    (loop (vlad-cdr v '()) #t))
		   `(cons ,(loop (vlad-car v '()) #f)
			  ,(loop (vlad-cdr v '()) #f)))
	       (cons (loop (vlad-car v '()) quote?)
		     (loop (vlad-cdr v '()) quote?))))
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
	     (case (length (closure-variables v))
	      ((0)
	       `(lambda (,(closure-variable v))
		 ,(abstract->concrete (closure-body v))))
	      ((1)
	       `(let ,(map-indexed
		       (lambda (x i)
			`(,x ,(loop (vector-ref (closure-values v) i) quote?)))
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
	    (*unabbreviate-nonrecursive-closures?*
	     `(nonrecursive-closure
	       ,(map-indexed
		 (lambda (x i)
		  `(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		 (closure-variables v))
	       (lambda (,(closure-variable v))
		,(abstract->concrete (closure-body v)))))
	    (else `(lambda (,(closure-variable v))
		    ,(abstract->concrete (closure-body v))))))
	  ((recursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (internal-error))
	     (case (length (closure-variables v))
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
			    `(,x ,(loop
				   (vector-ref (closure-values v) i) quote?)))
			   (closure-variables v))
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
			   ,(loop (vector-ref (closure-values v) i) quote?)))
			(closure-variables v))
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
		  `(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		 (closure-variables v))
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

;;; Evaluator

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

(define (tag-check? tags v)
 (or (null? tags)
     (case (first tags)
      ((forward) (and (vlad-forward? v) (tag-check? (rest tags) (primal v))))
      ((reverse)
       (and (vlad-reverse? v) (tag-check? (rest tags) (*j-inverse v))))
      (else (internal-error)))))

;;; needs work: This evaluator is not tail recursive.

(define (call callee argument)
 (unless (or (and *encoded-booleans?*
		  (or (vlad-pair? callee '())
		      (vlad-true? callee)
		      (vlad-false? callee)))
	     (and *scott-pairs?* (vlad-pair? callee '()))
	     (vlad-procedure? callee))
  (run-time-error "Target is not a procedure" callee))
 (unless (tag-check? (cond ((primitive-procedure? callee) '())
			   ((closure? callee) (closure-tags callee))
			   (else (internal-error)))
		     argument)
  (run-time-error "Argument has wrong type for target" callee argument))
 (set! *stack* (cons (list callee argument) *stack*))
 (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	     ((nonrecursive-closure? callee) *trace-nonrecursive-closures?*)
	     ((recursive-closure? callee) *trace-recursive-closures?*)
	     (else (internal-error)))
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
 (let ((result (cond ((primitive-procedure? callee)
		      ((primitive-procedure-procedure callee) argument #f))
		     ((nonrecursive-closure? callee)
		      (evaluate
		       (closure-body callee) argument (closure-values callee)))
		     ((recursive-closure? callee)
		      (evaluate
		       (closure-body callee)
		       argument
		       (vector-append
			(map-n-vector
			 (lambda (i)
			  (if (= i (recursive-closure-index callee))
			      ;; to preserve eq?ness
			      callee
			      (make-recursive-closure
			       (closure-variables callee)
			       (closure-values callee)
			       (recursive-closure-procedure-variables callee)
			       (recursive-closure-argument-variables callee)
			       (recursive-closure-bodies callee)
			       i)))
			 (vector-length (recursive-closure-bodies callee)))
			(closure-values callee))))
		     (else (internal-error)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((nonrecursive-closure? callee) *trace-nonrecursive-closures?*)
	      ((recursive-closure? callee) *trace-recursive-closures?*)
	      (else (internal-error)))
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

(define (evaluate e v vs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (cond ((variable-access-expression? e)
	(lookup (variable-access-expression-index e)))
       ((lambda-expression? e)
	(let ((vs (map-vector
		   lookup (lambda-expression-free-variable-indices e))))
	 (make-nonrecursive-closure (free-variables e)
				    vs
				    (lambda-expression-variable e)
				    (lambda-expression-body e))))
       ;; This is a vestigial let*-expression.
       ((let*? e)
	(let ((x? (and *x* (variable=? (first (let*-variables e)) *x*))))
	 (let loop ((es (let*-expressions e))
		    (xs (let*-variables e))
		    (vs vs))
	  (if (null? es)
	      (evaluate (let*-body e) v vs)
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
       ((application? e)
	;; This LET* is to specify the evaluation order.
	(let* ((callee (evaluate (application-callee e) v vs))
	       (argument (evaluate (application-argument e) v vs)))
	 (call callee argument)))
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
	     (make-recursive-closure
	      (letrec-expression-bodies-free-variables e)
	      vs
	      xs0
	      xs1
	      es
	      i))
	    (vector-length es)))
	  (map-vector lookup
		      (letrec-expression-body-free-variable-indices e)))))
       ((cons-expression? e)
	;; This LET* is to specify the evaluation order.
	(let* ((car (evaluate (cons-expression-car e) v vs))
	       (cdr (evaluate (cons-expression-cdr e) v vs)))
	 (make-tagged-pair (cons-expression-tags e) car cdr)))
       (else (internal-error))))

;;; Flow Analysis

;;; General

(define (positionp-vector p x v)
 ;; belongs in QobiScheme
 (let loop ((i 0))
  (cond ((>= i (vector-length v)) #f)
	((p x (vector-ref v i)) i)
	(else (loop (+ i 1))))))

;;; Expression Equality

(define (expression-eqv? e1 e2)
 (or (and (constant-expression? e1)
	  (constant-expression? e2)
	  (equal? (constant-expression-value e1)
		  (constant-expression-value e2)))
     (and (variable-access-expression? e1)
	  (variable-access-expression? e2)
	  (variable=? (variable-access-expression-variable e1)
		      (variable-access-expression-variable e2)))
     (and (lambda-expression? e1)
	  (lambda-expression? e2)
	  (variable=? (lambda-expression-variable e1)
		      (lambda-expression-variable e2))
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
	  (every variable=?
		 (letrec-expression-argument-variables e1)
		 (letrec-expression-argument-variables e2))
	  (every expression-eqv?
		 (letrec-expression-bodies e1)
		 (letrec-expression-bodies e2))
	  (expression-eqv? (letrec-expression-body e1)
			   (letrec-expression-body e2)))
     (and (cons-expression? e1) (cons-expression? e2)
	  (equal-tags? (cons-expression-tags e1) (cons-expression-tags e2))
	  (expression-eqv? (cons-expression-car e1) (cons-expression-car e2))
	  (expression-eqv? (cons-expression-cdr e1)
			   (cons-expression-cdr e2)))))

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

;;; Abstract Values

(define (abstract-boolean? v)
 (or (vlad-true? v) (vlad-false? v) (eq? v 'boolean)))

(define (abstract-real? v) (or (real? v) (eq? v 'real)))

(define (abstract-top? v) (eq? v 'top))

(define (abstract-top) 'top)

(define (potentially-imprecise-vlad-value->abstract-value v)
 (cond ((scalar-value? v)
	(if (and *imprecise-inexacts?* (real? v) (inexact? v)) 'real v))
       ((nonrecursive-closure? v)
	(make-nonrecursive-closure
	 (closure-variables v)
	 (map-vector potentially-imprecise-vlad-value->abstract-value
		     (closure-values v))
	 (closure-variable v)
	 (closure-body v)))
       ((recursive-closure? v)
	(make-recursive-closure
	 (closure-variables v)
	 (map-vector potentially-imprecise-vlad-value->abstract-value
		     (closure-values v))
	 (recursive-closure-procedure-variables v)
	 (recursive-closure-argument-variables v)
	 (recursive-closure-bodies v)
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
	(make-tagged-pair (tagged-pair-tags v)
			  (potentially-imprecise-vlad-value->abstract-value
			   (tagged-pair-car v))
			  (potentially-imprecise-vlad-value->abstract-value
			   (tagged-pair-cdr v))))
       (else (internal-error))))

(define (nonrecursive-closure-match? v1 v2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (variable=? (closure-variable v1) (closure-variable v2))
	  (expression=? (closure-body v1) (closure-body v2)))))

(define (recursive-closure-match? v1 v2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (= (recursive-closure-index v1) (recursive-closure-index v2))
	  (= (vector-length (recursive-closure-procedure-variables v1))
	     (vector-length (recursive-closure-procedure-variables v2)))
	  (= (vector-length (recursive-closure-argument-variables v1))
	     (vector-length (recursive-closure-argument-variables v2)))
	  (every-vector variable=?
			(recursive-closure-procedure-variables v1)
			(recursive-closure-procedure-variables v2))
	  (every-vector variable=?
			(recursive-closure-argument-variables v1)
			(recursive-closure-argument-variables v2))
	  (every-vector expression=?
			(recursive-closure-bodies v1)
			(recursive-closure-bodies v2)))))

(define (abstract-value=? v1 v2)
 (or (and (null? v1) (null? v2))
     (and (not *encoded-booleans?*)
	  (abstract-boolean? v1)
	  (abstract-boolean? v2)
	  (eq? v1 v2))
     (and (abstract-real? v1)
	  (abstract-real? v2)
	  ;; This was = but then it equates exact values with inexact values
	  ;; and this breaks -imprecise-inexacts.
	  (equal? v1 v2))
     (and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (nonrecursive-closure-match? v1 v2)
	  (abstract-environment=? (closure-values v1) (closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (recursive-closure-match? v1 v2)
	  (abstract-environment=? (closure-values v1) (closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (abstract-value=? (bundle-primal v1) (bundle-primal v2))
	  (abstract-value=? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (abstract-value=? (reverse-tagged-value-primal v1)
			    (reverse-tagged-value-primal v2)))
     (and (not *scott-pairs?*)
	  (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (abstract-value=? (tagged-pair-car v1) (tagged-pair-car v2))
	  (abstract-value=? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))
     (and (abstract-top? v1) (abstract-top? v2))))

(define (abstract-value-union v1 v2)
 (cond ((and (null? v1) (null? v2)) '())
       ((and (not *encoded-booleans?*)
	     (abstract-boolean? v1)
	     (abstract-boolean? v2))
	(if (eq? v1 v2) v1 'boolean))
       ((and (abstract-real? v1) (abstract-real? v2))
	(if (equal? v1 v2) v1 'real))
       ((and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
	v1)
       ((and (nonrecursive-closure? v1)
	     (nonrecursive-closure? v2)
	     (nonrecursive-closure-match? v1 v2))
	(let ((vs (abstract-environment-union
		   (closure-values v1) (closure-values v2))))
	 (if (some-vector abstract-top? vs)
	     (abstract-top)
	     ;; See the note in abstract-environment=?.
	     (make-nonrecursive-closure (closure-variables v1)
					vs
					(closure-variable v1)
					(closure-body v1)))))
       ((and (recursive-closure? v1)
	     (recursive-closure? v2)
	     (recursive-closure-match? v1 v2))
	(let ((vs (abstract-environment-union
		   (closure-values v1) (closure-values v2))))
	 (if (some-vector abstract-top? vs)
	     (abstract-top)
	     ;; See the note in abstract-environment=?.
	     (make-recursive-closure (closure-variables v1)
				     vs
				     (recursive-closure-procedure-variables v1)
				     (recursive-closure-argument-variables v1)
				     (recursive-closure-bodies v1)
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
       ((and (not *scott-pairs?*)
	     (tagged-pair? v1)
	     (tagged-pair? v2)
	     (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
	(let ((v-car (abstract-value-union (tagged-pair-car v1)
					   (tagged-pair-car v2)))
	      (v-cdr (abstract-value-union (tagged-pair-cdr v1)
					   (tagged-pair-cdr v2))))
	 (if (or (abstract-top? v-car) (abstract-top? v-cdr))
	     (abstract-top)
	     (make-tagged-pair (tagged-pair-tags v1) v-car v-cdr))))
       (else (abstract-top))))

;;; Abstract Environments

(define (restrict-environment vs e f)
 (let ((xs (free-variables e)))
  (list->vector (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
		     (free-variables (f e))))))

(define (letrec-restrict-environment vs e)
 (let ((xs (free-variables e)))
  (list->vector (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
		     (letrec-expression-bodies-free-variables e)))))

(define (letrec-nested-environment vs e)
 (list->vector
  (map (lambda (x)
	(if (memp variable=? x (letrec-expression-procedure-variables e))
	    (let ((vs (letrec-restrict-environment vs e)))
	     (make-recursive-closure
	      (letrec-expression-bodies-free-variables e)
	      vs
	      (list->vector (letrec-expression-procedure-variables e))
	      (list->vector (letrec-expression-argument-variables e))
	      (list->vector (letrec-expression-bodies e))
	      (positionp
	       variable=? x (letrec-expression-procedure-variables e))))
	    (vector-ref vs (positionp variable=? x (free-variables e)))))
       (free-variables (letrec-expression-body e)))))

(define (abstract-environment=? vs1 vs2)
 ;; This assumes that the free variables in two alpha-equivalent expressions
 ;; are in the same order. Note that this is a weak notion of equivalence. A
 ;; stronger notion would attempt to find a correspondence between the free
 ;; variables that would allow them to be contextually alpha equivalent.
 (every-vector abstract-value=? vs1 vs2))

(define (abstract-environment-union vs1 vs2)
 (map-vector abstract-value-union vs1 vs2))

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
 (unless (= (vector-length vs) (length (free-variables e))) (internal-error))
 (list (make-expression-binding
	e (list (make-environment-binding vs (abstract-top))))))

(define (initial-abstract-analysis e bs)
 ;; This (like update-analysis-domains) only makes domains.
 (make-abstract-analysis
  e
  (list->vector
   (map
    (lambda (x)
     (potentially-imprecise-vlad-value->abstract-value
      (value-binding-value
       (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))))
    (free-variables e)))))

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
 (cond
  ((nonrecursive-closure? v1)
   (p (closure-body v1)
      (list->vector
       (map (lambda (x)
	     (if (variable=? x (closure-variable v1))
		 v2
		 (vector-ref (closure-values v1)
			     (positionp variable=? x (closure-variables v1)))))
	    (free-variables (closure-body v1))))))
  ((recursive-closure? v1)
   (p (closure-body v1)
      (list->vector
       (map (lambda (x)
	     (cond
	      ((variable=? x (closure-variable v1)) v2)
	      ((some-vector (lambda (x1) (variable=? x x1))
			    (recursive-closure-procedure-variables v1))
	       (make-recursive-closure
		(closure-variables v1)
		(closure-values v1)
		(recursive-closure-procedure-variables v1)
		(recursive-closure-argument-variables v1)
		(recursive-closure-bodies v1)
		(positionp-vector
		 variable=? x (recursive-closure-procedure-variables v1))))
	      (else
	       (vector-ref (closure-values v1)
			   (positionp variable=? x (closure-variables v1))))))
	    (free-variables (closure-body v1))))))
  (else (internal-error))))

(define (abstract-apply v1 v2 bs)
 (if (or (abstract-top? v1) (abstract-top? v2))
     (abstract-top)
     (cond
      ((primitive-procedure? v1) ((primitive-procedure-procedure v1) v2 bs))
      ((closure? v1)
       (abstract-apply-closure (lambda (e vs) (abstract-eval1 e vs bs)) v1 v2))
      (else (run-time-error "Target is not a procedure" v1)))))

(define (abstract-eval e vs bs)
 (cond
  ((variable-access-expression? e)
   (unless (= (length (free-variables e)) 1) (internal-error))
   (vector-ref vs 0))
  ((lambda-expression? e)
   (make-nonrecursive-closure (free-variables e)
			      vs
			      (lambda-expression-variable e)
			      (lambda-expression-body e)))
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
    (if (or (abstract-top? v1) (abstract-top? v2))
	(abstract-top)
	(make-tagged-pair (cons-expression-tags e) v1 v2))))
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
 (if (or (abstract-top? v1) (abstract-top? v2))
     (empty-abstract-analysis)
     (cond
      ((primitive-procedure? v1)
       ;; needs work: should put this into slots of the primitive procedures
       (if (eq? (primitive-procedure-name v1) 'if-procedure)
	   ((ternary
	     (lambda (v1 v2 v3 bs)
	      (unless (and (nonrecursive-closure? v2)
			   (nonrecursive-closure? v3))
	       (run-time-error "You used if-procedure"))
	      (cond ((eq? v1 'boolean)
		     (abstract-analysis-union
		      (abstract-apply-closure
		       (lambda (e vs) (abstract-eval1-prime e vs bs))
		       v2
		       (tagged-null (closure-tags v2)))
		      (abstract-apply-closure
		       (lambda (e vs) (abstract-eval1-prime e vs bs))
		       v3
		       (tagged-null (closure-tags v3)))))
		    (v1 (abstract-apply-closure
			 (lambda (e vs) (abstract-eval1-prime e vs bs))
			 v2
			 (tagged-null (closure-tags v2))))
		    (else (abstract-apply-closure
			   (lambda (e vs) (abstract-eval1-prime e vs bs))
			   v3
			   (tagged-null (closure-tags v3))))))
	     "if-procedure")
	    v2
	    bs)
	   (empty-abstract-analysis)))
      ((closure? v1)
       (abstract-apply-closure
	(lambda (e vs) (abstract-eval1-prime e vs bs)) v1 v2))
      (else (run-time-error "Target is not a procedure" v1)))))

(define (abstract-eval-prime e vs bs)
 (cond
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
 (reduce abstract-analysis-union
	 (map (lambda (b1)
	       (reduce abstract-analysis-union
		       (map (lambda (b2)
			     (abstract-eval-prime
			      (expression-binding-expression b1)
			      (environment-binding-values b2)
			      bs))
			    (expression-binding-flow b1))
		       (empty-abstract-analysis)))
	      bs)
	 (empty-abstract-analysis)))

(define (concrete-reals-in v)
 (cond ((real? v) (list v))
       ((scalar-value? v) '())
       ((abstract-top? v) '())
       (else (reduce
	      unionv (map concrete-reals-in (aggregate-value-values v)) '()))))

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
	    (reduce
	     + (map (lambda (b) (length (expression-binding-flow b))) bs1) 0)))
   (when *verbose?*
    (format #t "expressions: ~s, max flow size: ~s, tops: ~s, concrete reals: ~s~%"
	    (length bs)
	    (reduce max
		    (map (lambda (b) (length (expression-binding-flow b))) bs)
		    minus-infinity)
	    (reduce
	     +
	     (map
	      (lambda (b)
	       (count-if
		(lambda (b) (abstract-top? (environment-binding-value b)))
		(expression-binding-flow b)))
	      bs)
	     0)
	    (reduce
	     unionv
	     (map (lambda (b)
		   (reduce
		    unionv
		    (map (lambda (b)
			  (unionv
			   (reduce-vector
			    unionv
			    (map-vector concrete-reals-in
					(environment-binding-values b))
			    '())
			   (concrete-reals-in (environment-binding-value b))))
			 (expression-binding-flow b))
		    '()))
		  bs)
	     '())))
   (if (abstract-analysis=? bs1 bs) bs (loop bs1 (+ i 1))))))

;;; Pretty printer for abstract

(define (externalize-abstract-environment xs vs)
 (unless (and (vector? vs) (= (length xs) (vector-length vs)))
  (internal-error "Not an abstract environment"))
 (map (lambda (x v) (list x (externalize v))) xs (vector->list vs)))

(define (externalize-abstract-environment-binding xs b)
 (unless (environment-binding? b)
  (internal-error "Not an abstract environment binding"))
 (list (externalize-abstract-environment xs (environment-binding-values b))
       (externalize (environment-binding-value b))))

(define (externalize-abstract-flow xs bs)
 (unless (and (list? bs) (every environment-binding? bs))
  (internal-error "Not an abstract flow"))
 (map (lambda (b) (externalize-abstract-environment-binding xs b)) bs))

(define (externalize-abstract-expression-binding b)
 (unless (expression-binding? b)
  (internal-error "Not an abstract expression binding"))
 (list (abstract->concrete (expression-binding-expression b))
       (externalize-abstract-flow
	(free-variables (expression-binding-expression b))
	(expression-binding-flow b))))

(define (externalize-abstract-analysis bs)
 (unless (and (list? bs) (every expression-binding? bs))
  (internal-error "Not an abstract analysis"))
 (map externalize-abstract-expression-binding bs))

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
 (cond ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e)
	(adjoinp variable=?
		 (lambda-expression-variable e)
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
		 (letrec-expression-argument-variables e)
		 (unionp variable=?
			 (reduce (lambda (xs1 xs2) (unionp variable=? xs1 xs2))
				 (map all-variables-in-expression
				      (letrec-expression-bodies e))
				 '())
			 (all-variables-in-expression
			  (letrec-expression-body e))))))
       ((cons-expression? e)
	(unionp variable=?
		(all-variables-in-expression (cons-expression-car e))
		(all-variables-in-expression (cons-expression-cdr e))))
       (else (internal-error))))

(define (all-variables bs)
 (reduce (lambda (xs1 xs2) (unionp variable=? xs1 xs2))
	 (map (lambda (b)
	       (all-variables-in-expression (expression-binding-expression b)))
	      bs)
	 '()))

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
 (cond ((closure? v)
	(map (lambda (x) (generate-variable-name x xs)) (closure-variables v)))
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
 (reduce
  (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
  (map (lambda (b)
	(reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		(map (lambda (b)
		      (remove-duplicatesp
		       abstract-value=?
		       (cons (environment-binding-value b)
			     (vector->list (environment-binding-values b)))))
		     (expression-binding-flow b))
		'()))
       bs)
  '()))

(define (all-abstract-subvalues v)
 (cons v
       (if (scalar-value? v)
	   '()
	   (reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		   (map all-abstract-subvalues (aggregate-value-values v))
		   '()))))

(define (all-abstract-subvalues-for-bundle v v-perturbation)
 (cons (vlad-cons v v-perturbation)
       (if (or (and (void? v) (void? v-perturbation))
	       (and (abstract-boolean? v) (abstract-boolean? v-perturbation))
	       (and (abstract-real? v) (abstract-real? v-perturbation)))
	   '()
	   (reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		   (map all-abstract-subvalues-for-bundle
			(aggregate-value-values v)
			(aggregate-value-values v-perturbation))
		   '()))))

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
 (let ((graph (reduce append
		      (map (lambda (x1)
			    (reduce append
				    (map (lambda (x2)
					  (if (and (not (eq? x1 x2)) (p x1 x2))
					      (list (list x1 x2))
					      '()))
					 l)
				    '()))
			   l)
		      '())))
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
 (let ((graph (reduce append
		      (map (lambda (x1)
			    (reduce append
				    (map (lambda (x2)
					  (if (and (not (eq? x1 x2)) (p x1 x2))
					      (list (list x1 x2))
					      '()))
					 l)
				    '()))
			   l)
		      '())))
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
	  (reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
		  (map all-abstract-subvalues (all-abstract-values bs))'()))))

(define (all-primitives s bs)
 (reduce
  (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
  (map (lambda (b)
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
       bs)
  '()))

(define (generate-builtin-name s v vs)
 (let ((i (positionp abstract-value=? v vs)))
  (unless i (internal-error))
  (list s i)))

(define (generate-function-name v1 v2 v1v2s)
 (let ((i (positionp (lambda (v1v2a v1v2b)
		      (and (abstract-value=? (first v1v2a) (first v1v2b))
			   (abstract-value=? (second v1v2a) (second v1v2b))))
		     (list v1 v2)
		     v1v2s)))
  (unless i (internal-error))
  (list "f" i)))

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
       (let ((v1 (vlad-car v '())) (v2 (vlad-cdr v '())))
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
       (let ((v1 (vlad-car v '())) (v2 (vlad-cdr v '())))
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

(define (all-functions bs)
 (reduce
  (lambda (v1v2sa v2v2sb)
   (unionp (lambda (v1v2a v1v2b)
	    (and (abstract-value=? (first v1v2a) (first v1v2b))
		 (abstract-value=? (second v1v2a) (second v1v2b))))
	   v1v2sa
	   v2v2sb))
  (map (lambda (b)
	(let ((e (expression-binding-expression b)))
	 (if (application? e)
	     (reduce
	      (lambda (v1v2sa v2v2sb)
	       (unionp (lambda (v1v2a v1v2b)
			(and (abstract-value=? (first v1v2a) (first v1v2b))
			     (abstract-value=? (second v1v2a) (second v1v2b))))
		       v1v2sa
		       v2v2sb))
	      (map
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
		    (let* ((v1 (vlad-car v '()))
			   (v2 (vlad-cdr v '()))
			   (v3 (vlad-car v2 '()))
			   (v4 (vlad-cdr v2 '()))
			   (v5
			    (cond
			     ((eq? v1 'boolean)
			      (abstract-value-union
			       (abstract-apply
				v3 (tagged-null (closure-tags v3)) bs)
			       (abstract-apply
				v4 (tagged-null (closure-tags v4)) bs)))
			     (v1 (abstract-apply
				  v3 (tagged-null (closure-tags v3)) bs))
			     (else (abstract-apply
				    v4 (tagged-null (closure-tags v4)) bs)))))
		     (if (void? v5)
			 '()
			 (cond
			  ((eq? v1 'boolean)
			   ;; We make the assumption that v3 and v4 will not
			   ;; be abstract-value=?. If this assumption is false
			   ;; then there may be duplicates.
			   (list (list v3 (tagged-null (closure-tags v3)))
				 (list v4 (tagged-null (closure-tags v4)))))
			  (v1 (list (list v3 (tagged-null (closure-tags v3)))))
			  (else
			   (list
			    (list v4 (tagged-null (closure-tags v4))))))))))
		  (else '()))))
	       (expression-binding-flow b))
	      '())
	     '())))
       bs)
  '()))

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
			       (vlad-car (vlad-cdr (second thing2) '()) '()))
	     (abstract-value=? (first (second thing1))
			       (vlad-cdr (vlad-cdr (second thing2) '()) '()))))
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
	    (v1 (vlad-car v '()))
	    (v2 (vlad-cdr v '()))
	    (v3 (vlad-car v2 '()))
	    (v4 (vlad-cdr v2 '()))
	    (v5
	     (cond ((eq? v1 'boolean)
		    (abstract-value-union
		     (abstract-apply v3 (tagged-null (closure-tags v3)) bs)
		     (abstract-apply v4 (tagged-null (closure-tags v4)) bs)))
		   (v1 (abstract-apply v3 (tagged-null (closure-tags v3)) bs))
		   (else
		    (abstract-apply v4 (tagged-null (closure-tags v4)) bs)))))
      (when (and (eq? v1 'boolean)
		 (not
		  (abstract-value=?
		   (abstract-apply v3 (tagged-null (closure-tags v3)) bs)
		   (abstract-apply v4 (tagged-null (closure-tags v4)) bs))))
       (unimplemented "balancing"))
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
		       (generate-variable-name (closure-variable v1) xs)))))
	   ");"
	   #\newline))))
    (else (internal-error))))
  (append (first things1-things2) (second things1-things2))))

(define (generate-if-and-function-definitions bs xs vs v1v2s things1-things2)
 (map
  (lambda (thing)
   (case (first thing)
    ((if)
     (let* ((v (second thing))
	    (v1 (vlad-car v '()))
	    (v2 (vlad-cdr v '()))
	    (v3 (vlad-car v2 '()))
	    (v4 (vlad-cdr v2 '()))
	    (v5
	     (cond ((eq? v1 'boolean)
		    (abstract-value-union
		     (abstract-apply v3 (tagged-null (closure-tags v3)) bs)
		     (abstract-apply v4 (tagged-null (closure-tags v4)) bs)))
		   (v1 (abstract-apply v3 (tagged-null (closure-tags v3)) bs))
		   (else
		    (abstract-apply v4 (tagged-null (closure-tags v4)) bs)))))
      (when (and (eq? v1 'boolean)
		 (not
		  (abstract-value=?
		   (abstract-apply v3 (tagged-null (closure-tags v3)) bs)
		   (abstract-apply v4 (tagged-null (closure-tags v4)) bs))))
       (unimplemented "balancing"))
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
	   (cond ((eq? v1 'boolean)
		  (list "x.a?"
			(generate-function-name
			 v3 (tagged-null (closure-tags v3)) v1v2s)
			"("
			(if (void? v3) '() "x.d.a")
			")"
			":"
			(generate-function-name
			 v4 (tagged-null (closure-tags v4)) v1v2s)
			"("
			(if (void? v4) '() "x.d.d")
			")"))
		 (v1 (list (generate-function-name
			    v3 (tagged-null (closure-tags v3)) v1v2s)
			   "("
			   (if (void? v3) '() "x.d.a")
			   ")"))
		 (else (list (generate-function-name
			      v4 (tagged-null (closure-tags v4)) v1v2s)
			     "("
			     (if (void? v4) '() "x.d.d")
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
		       (generate-variable-name (closure-variable v1) xs)))))
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
     ((null? v) (internal-error))
     ((eq? v #t) "TRUE")
     ((eq? v #f) "FALSE")
     ;; This assumes that Scheme inexact numbers are printed as C doubles.
     ((real? v) (exact->inexact v))
     ((primitive-procedure? v) (internal-error))
     ((nonrecursive-closure? v) (internal-error))
     ((recursive-closure? v) (internal-error))
     ((bundle? v) (internal-error))
     ((tagged-pair? v) (internal-error))
     (else (internal-error))))
   ((variable-access-expression? e)
    (generate-reference (variable-access-expression-variable e) xs2 xs xs1))
   ((lambda-expression? e)
    (list
     (generate-builtin-name "m" v vs1)
     "("
     (commas-between
      (map (lambda (x s v) (if (void? v) #f (generate-reference x xs2 xs xs1)))
	   (closure-variables v)
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
       (let ((v (let ((vs (letrec-restrict-environment vs e)))
		 (make-recursive-closure
		  (letrec-expression-bodies-free-variables e)
		  vs
		  (list->vector (letrec-expression-procedure-variables e))
		  (list->vector (letrec-expression-argument-variables e))
		  (list->vector (letrec-expression-bodies e))
		  (positionp
		   variable=? x (letrec-expression-procedure-variables e))))))
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
			(closure-variables v)
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
  (reduce
   (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
   (map
    all-abstract-subvalues
    (reduce
     (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
     (map
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
      bs)
     '()))
   '())))

(define (all-bundles bs)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (cached-topological-sort
  (lambda (v1 v2)
   (component? (bundle (vlad-car v1 '()) (vlad-cdr v1 '()))
	       (bundle (vlad-car v2 '()) (vlad-cdr v2 '()))))
  (remove-if
   void?
   (reduce
    (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
    (map
     (lambda (v)
      (all-abstract-subvalues-for-bundle (vlad-car v '()) (vlad-cdr v '())))
     (reduce
      (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
      (map (lambda (b)
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
	   bs)
      '()))
    '()))))

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
 (map (lambda (v)
       (let ((v1 (bundle (vlad-car v '()) (vlad-cdr v '()))))
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
 (map
  (lambda (v)
   (let* ((v1 (vlad-car v '())) (v2 (vlad-cdr v '())) (v3 (bundle v1 v2)))
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
   (generate-if-and-function-definitions bs xs vs v1v2s things1-things2)
   (list
    "int main(void){"
    (let ((vs
	   (vector->list
	    (environment-binding-values
	     (first
	      (expression-binding-flow (lookup-expression-binding e bs)))))))
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
		 (cond
		  ((abstract-boolean? v)
		   (list c "=" (if v1 "TRUE" "FALSE") ";"))
		  ((abstract-real? v) (list c "=" v1 ";"))
		  ((vlad-pair? v '())
		   (list
		    (loop (vlad-car v1 '()) (list c ".a") (vlad-car v '()))
		    (loop (vlad-cdr v1 '()) (list c ".a") (vlad-car v '()))))
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

(define (unary f s) (lambda (x bs) (f x)))

(define (unary-predicate f s) (lambda (x bs) (if (f x) vlad-true vlad-false)))

(define (unary-real f s)
 (lambda (x bs)
  (unless (abstract-real? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (if (real? x) (f x) 'real)))

(define (unary-real-predicate f s)
 (lambda (x bs)
  (unless (abstract-real? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (if (real? x) (if (f x) vlad-true vlad-false) 'boolean)))

(define (binary f s)
 (lambda (x bs)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f (vlad-car x '()) (vlad-cdr x '()))))

(define (binary-real f s)
 (lambda (x bs)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x '())) (x2 (vlad-cdr x '())))
   (unless (and (abstract-real? x1) (abstract-real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   ;; needs work: This may be imprecise for *, /, and atan.
   (if (and (real? x1) (real? x2)) (f x1 x2) 'real))))

(define (binary-real-predicate f s)
 (lambda (x bs)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x '())) (x2 (vlad-cdr x '())))
   (unless (and (abstract-real? x1) (abstract-real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (and (real? x1) (real? x2))
       (if (f x1 x2) vlad-true vlad-false)
       'boolean))))

(define (ternary f s)
 (lambda (x bs)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x23 (vlad-cdr x '())))
   (unless (vlad-pair? x23 '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f (vlad-car x '()) (vlad-car x23 '()) (vlad-cdr x23 '()) bs))))

(define (define-primitive-procedure x procedure generator forward reverse)
 (set! *value-bindings*
       (cons (make-value-binding
	      x
	      (make-primitive-procedure
	       x procedure generator forward reverse 0))
	     *value-bindings*)))

(define (evaluate-in-top-level-environment e)
 (let ((e (standard-prelude e)))
  (syntax-check-expression! e)
  (let ((result (parse e)))
   (evaluate (first result)
	     'unspecified
	     (list->vector (map value-binding-value (second result)))))))

(define (initialize-forwards-and-reverses!)
 (for-each (lambda (b)
	    (set-primitive-procedure-forward!
	     (value-binding-value b)
	     (evaluate-in-top-level-environment
	      (primitive-procedure-forward (value-binding-value b))))
	    (set-primitive-procedure-reverse!
	     (value-binding-value b)
	     (evaluate-in-top-level-environment
	      (primitive-procedure-reverse (value-binding-value b)))))
	   *value-bindings*))

(define (initialize-basis!)
 (set! vlad-true
       (if *encoded-booleans?*
	   ;; (lambda (p)
	   ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) a))) x3)))
	   ;;         (x2 (p x1)))
	   ;;   x2))
	   (make-nonrecursive-closure
	    '()
	    '#()
	    'p
	    (index
	     'p
	     '()
	     (new-let*
	      '(x1 x2)
	      (list (new-lambda-expression
		     'a
		     (new-let* '(x3)
			       (list (new-lambda-expression
				      'd (new-variable-access-expression 'a)))
			       (new-variable-access-expression 'x3)))
		    (new-application (new-variable-access-expression 'p)
				     (new-variable-access-expression 'x1)))
	      (new-variable-access-expression 'x2))))
	   #t))
 (set! vlad-false
       (if *encoded-booleans?*
	   ;; (lambda (p)
	   ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) d))) x3)))
	   ;;         (x2 (p x1)))
	   ;;   x2))
	   (make-nonrecursive-closure
	    '()
	    '#()
	    'p
	    (index
	     'p
	     '()
	     (new-let*
	      '(x1 x2)
	      (list (new-lambda-expression
		     'a
		     (new-let* '(x3)
			       (list (new-lambda-expression
				      'd (new-variable-access-expression 'd)))
			       (new-variable-access-expression 'x3)))
		    (new-application (new-variable-access-expression 'p)
				     (new-variable-access-expression 'x1)))
	      (new-variable-access-expression 'x2))))
	   #f))
 ;; In the following, all real constants are inexact so that they are
 ;; imprecise under -imprecise-inexacts.
 (define-primitive-procedure '+
  (binary-real + "+")
  (lambda (v vs) (generate-builtin-name "add" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (+ x1 x2) (+ (perturbation x1) (perturbation x2)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (+ x1 x2))
	   (lambda ((sensitivity y))
	    (cons '() (cons (sensitivity y) (sensitivity y))))))))
 (define-primitive-procedure '-
  (binary-real - "-")
  (lambda (v vs) (generate-builtin-name "minus" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (- x1 x2) (- (perturbation x1) (perturbation x2)))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (- x1 x2))
	       (lambda ((sensitivity y))
		(cons '() (cons (sensitivity y) (- 0.0 (sensitivity y))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons
	  (*j (- x1 x2))
	  (lambda ((sensitivity y))
	   (cons '() (cons (sensitivity y) (- (real 0) (sensitivity y))))))))))
 (define-primitive-procedure '*
  (binary-real * "*")
  (lambda (v vs) (generate-builtin-name "times" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (* x1 x2)
	     (+ (* x2 (perturbation x1)) (* x1 (perturbation x2))))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (* x1 x2))
	   (lambda ((sensitivity y))
	    (cons '()
		  (cons (* x2 (sensitivity y)) (* x1 (sensitivity y)))))))))
 (define-primitive-procedure '/
  (binary-real divide "/")
  (lambda (v vs) (generate-builtin-name "divide" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle
      (/ x1 x2)
      (/ (- (* x2 (perturbation x1)) (* x1 (perturbation x2))) (* x2 x2)))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons
	  (*j (/ x1 x2))
	  (lambda ((sensitivity y))
	   (cons '()
		 (cons (/ (sensitivity y) x2)
		       (- 0.0 (/ (* x1 (sensitivity y)) (* x2 x2)))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons
	  (*j (/ x1 x2))
	  (lambda ((sensitivity y))
	   (cons
	    '()
	    (cons (/ (sensitivity y) x2)
		  (- (real 0) (/ (* x1 (sensitivity y)) (* x2 x2)))))))))))
 (define-primitive-procedure 'sqrt
  (unary-real sqrt "sqrt")
  (lambda (v vs) "sqrt")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (sqrt x) (/ (perturbation x) (+ (sqrt x) (sqrt x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (sqrt x))
	   (lambda ((sensitivity y))
	    (cons '() (/ (sensitivity y) (+ (sqrt x) (sqrt x)))))))))
 (define-primitive-procedure 'exp
  (unary-real exp "exp")
  (lambda (v vs) "exp")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (exp x) (* (exp x) (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (exp x))
	   (lambda ((sensitivity y))
	    (cons '() (* (exp x) (sensitivity y))))))))
 (define-primitive-procedure 'log
  (unary-real log "log")
  (lambda (v vs) "log")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (log x) (/ (perturbation x) x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (log x))
	   (lambda ((sensitivity y)) (cons '() (/ (sensitivity y) x)))))))
 (define-primitive-procedure 'sin
  (unary-real sin "sin")
  (lambda (v vs) "sin")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (sin x) (* (cos x) (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (sin x))
	   (lambda ((sensitivity y))
	    (cons '() (* (cos x) (sensitivity y))))))))
 (define-primitive-procedure 'cos
  (unary-real cos "cos")
  (lambda (v vs) "cos")
  (if *imprecise-inexacts?*
      '(lambda ((forward x))
	(let ((x (primal (forward x)))
	      ((perturbation x) (tangent (forward x))))
	 (bundle (cos x) (- 0.0 (* (sin x) (perturbation x))))))
      '(lambda ((forward x))
	(let ((x (primal (forward x)))
	      ((perturbation x) (tangent (forward x))))
	 (bundle (cos x) (- (real 0) (* (sin x) (perturbation x)))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons (*j (cos x))
	       (lambda ((sensitivity y))
		(cons '() (- 0.0 (* (sin x) (sensitivity y))))))))
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons (*j (cos x))
	       (lambda ((sensitivity y))
		(cons '() (- (real 0) (* (sin x) (sensitivity y))))))))))
 (define-primitive-procedure 'atan
  (binary-real atan "atan")
  (lambda (v vs) (generate-builtin-name "atantwo" v vs))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (atan x2 x1)
	     (/ (- (* x1 (perturbation x2)) (* x2 (perturbation x1)))
		(+ (* x1 x1) (* x2 x2))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(cons '()
		      (cons (- 0.0
			       (/ (* x2 (sensitivity y))
				  (+ (* x1 x1) (* x2 x2))))
			    (/ (* x1 (sensitivity y))
			       (+ (* x1 x1) (* x2 x2)))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(cons '()
		      (cons (- (real 0)
			       (/ (* x2 (sensitivity y))
				  (+ (* x1 x1) (* x2 x2))))
			    (/ (* x1 (sensitivity y))
			       (+ (* x1 x1) (* x2 x2)))))))))))
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
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
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
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
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
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
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
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
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
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure 'zero?
  (unary-real-predicate zero? "zero?")
  (lambda (v vs) (generate-builtin-name "iszero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (zero? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?")
  (lambda (v vs) (generate-builtin-name "positive" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (positive? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (positive? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?")
  (lambda (v vs) (generate-builtin-name "negative" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (negative? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (negative? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'null?
  (unary-predicate null? "null?")
  (lambda (v vs) (unimplemented "null?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (null? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'boolean?
  (unary-predicate abstract-boolean? "boolean?")
  (lambda (v vs) (unimplemented "boolean?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (boolean? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'real?
  (unary-predicate abstract-real? "real?")
  (lambda (v vs) (unimplemented "real?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (real? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'pair?
  (unary-predicate (lambda (x) (vlad-pair? x '())) "pair?")
  (lambda (v vs) (unimplemented "pair?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (pair? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?")
  (lambda (v vs) (unimplemented "procedure?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (procedure? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (procedure? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'forward?
  (unary-predicate vlad-forward? "forward?")
  (lambda (v vs) (unimplemented "forward?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (forward? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'reverse?
  (unary-predicate vlad-reverse? "reverse?")
  (lambda (v vs) (unimplemented "reverse?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (reverse? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (reverse? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (unless *encoded-booleans?*
  (define-primitive-procedure 'if-procedure
   (ternary
    (lambda (x1 x2 x3 bs)
     (unless (and (nonrecursive-closure? x2) (nonrecursive-closure? x3))
      (run-time-error "You used if-procedure"))
     (if *run?*
	 (if x1
	     (call x2 (tagged-null (closure-tags x2)))
	     (call x3 (tagged-null (closure-tags x3))))
	 (cond ((eq? x1 'boolean)
		(let ((v2 (abstract-apply-closure
			   (lambda (e vs) (abstract-eval1 e vs bs))
			   x2
			   (tagged-null (closure-tags x2))))
		      (v3 (abstract-apply-closure
			   (lambda (e vs) (abstract-eval1 e vs bs))
			   x3
			   (tagged-null (closure-tags x3)))))
		 ;; needs work: a little hokey
		 (cond ((abstract-top? v2) v3)
		       ((abstract-top? v3) v2)
		       (else (abstract-value-union v2 v3)))))
	       (x1 (abstract-apply-closure
		    (lambda (e vs) (abstract-eval1 e vs bs))
		    x2
		    (tagged-null (closure-tags x2))))
	       (else (abstract-apply-closure
		      (lambda (e vs) (abstract-eval1 e vs bs))
		      x3
		      (tagged-null (closure-tags x3)))))))
    "if-procedure")
   (lambda (v vs) (generate-builtin-name "if_procedure" v vs))
   '(lambda ((forward x))
     (let (((cons* x1 x2 x3) (primal (forward x)))
	   ((cons* (perturbation x1) (perturbation x2) (perturbation x3))
	    (tangent (forward x))))
      (if-procedure
       x1 (bundle x2 (perturbation x2)) (bundle x3 (perturbation x3)))))
   ;; needs work: this is wrong now
   '(lambda ((reverse x))
     (let (((cons* x1 x2 x3) (*j-inverse (reverse x))))
      (if-procedure
       x1
       (cons (*j x2)
	     (lambda ((sensitivity y))
	      (cons '() (cons* (zero x1) (sensitivity y) (zero x3)))))
       (cons (*j x3)
	     (lambda ((sensitivity y))
	      (cons '() (cons* (zero x1) (zero x2) (sensitivity y))))))))))
 (unless *scott-pairs?*
  (define-primitive-procedure 'car
   (unary (lambda (x) (vlad-car x '())) "car")
   (lambda (v vs) "car")
   '(lambda ((forward x))
     (let (((cons x1 x2) (primal (forward x)))
	   ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
      (bundle x1 (perturbation x1))))
   '(lambda ((reverse x))
     (let (((cons x1 x2) (*j-inverse (reverse x))))
      (cons (*j x1)
	    (lambda ((sensitivity y))
	     (cons '() (cons (sensitivity y) (zero x2))))))))
  (define-primitive-procedure 'cdr
   (unary (lambda (x) (vlad-cdr x '())) "cdr")
   (lambda (v vs) "cdr")
   '(lambda ((forward x))
     (let (((cons x1 x2) (primal (forward x)))
	   ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
      (bundle x2 (perturbation x2))))
   '(lambda ((reverse x))
     (let (((cons x1 x2) (*j-inverse (reverse x))))
      (cons (*j x2)
	    (lambda ((sensitivity y))
	     (cons '() (cons (zero x1) (sensitivity y)))))))))
 (define-primitive-procedure 'read-real
  (unary (lambda (x) (read-real)) "read-real")
  (lambda (v vs) "read_real")
  (if *imprecise-inexacts?*
      '(lambda ((forward (ignore))) (bundle (read-real) 0.0))
      '(lambda ((forward (ignore))) (bundle (read-real) (real 0))))
  ;; This assumes that you call read-real on '() which is what would happen
  ;; with (real-real).
  '(lambda ((reverse (ignore)))
    (cons (*j (read-real)) (lambda ((sensitivity (ignore))) (cons '() '())))))
 (define-primitive-procedure 'real
  (unary-real (lambda (x) (if *run?* x 'real)) "real")
  (lambda (v vs) (generate-builtin-name "real" v vs))
  ;; These widen the tangent and cotangent as well. Nothing requires us to do
  ;; so. It is just a design decision.
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (real x) (real (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real x))
	   (lambda ((sensitivity y)) (cons '() (real (sensitivity y))))))))
 (define-primitive-procedure 'write
  (unary (lambda (x)
	  (when *run?* ((if *pp?* pp write) (externalize x)) (newline))
	  x)
	 "write")
  (lambda (v vs) (generate-builtin-name "write" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (write x) (perturbation x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write x))
	   (lambda ((sensitivity y)) (cons '() (sensitivity y)))))))
 (define-primitive-procedure 'zero
  (unary zero "zero")
  (lambda (v vs) (generate-builtin-name "zero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (zero x) (zero (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'primal
  (unary primal "primal")
  (lambda (v vs) (generate-builtin-name "primal" v vs))
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  ((perturbation x-forward) (tangent (forward x-forward))))
     (bundle (primal x-forward) (primal (perturbation x-forward)))))
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward)))
	  (j* (lambda (x) (bundle x (zero x)))))
     (cons (*j (primal x-forward))
	   ;; needs work: not sure that this call to j* is correct
	   (lambda ((sensitivity y)) (cons '() (j* (sensitivity y))))))))
 (define-primitive-procedure 'tangent
  (unary tangent "tangent")
  (lambda (v vs) (generate-builtin-name "tangent" v vs))
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  ((perturbation x-forward) (tangent (forward x-forward))))
     (bundle (tangent x-forward) (tangent (perturbation x-forward)))))
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward))))
     (cons (*j (tangent x-forward))
	   (lambda ((sensitivity (perturbation y)))
	    (cons '()
		  (bundle (zero (primal x-forward))
			  (sensitivity (perturbation y)))))))))
 (define-primitive-procedure 'bundle
  (binary bundle "bundle")
  (lambda (v vs) (generate-builtin-name "bundle" v vs))
  '(lambda ((forward x))
    (let (((cons x1 (perturbation x2)) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation (perturbation x2)))
	   (tangent (forward x))))
     (bundle (bundle x1 (perturbation x2))
	     (bundle (perturbation x1) (perturbation (perturbation x2))))))
  '(lambda ((reverse x))
    (let (((cons x1 (perturbation x2)) (*j-inverse (reverse x))))
     (cons (*j (bundle x1 (perturbation x2)))
	   (lambda ((sensitivity (forward y)))
	    (cons '()
		  (cons (primal (sensitivity (forward y)))
			(tangent (sensitivity (forward y))))))))))
 (define-primitive-procedure 'plus
  (binary plus "plus")
  (lambda (v vs) (unimplemented "plus"))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (plus x1 x2) (plus (perturbation x1) (perturbation x2)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (plus x1 x2))
	   (lambda ((sensitivity y))
	    (cons '() (cons (sensitivity y) (sensitivity y))))))))
 (define-primitive-procedure '*j
  (unary *j "*j")
  (lambda (v vs) (unimplemented "*j"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (*j x) (*j (perturbation x)))))
  '(lambda ((reverse x))
    ;; The *j composed with *j-inverse could be optimized away.
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (*j x))
	   (lambda ((sensitivity (reverse y)))
	    (cons '() (*j-inverse (sensitivity (reverse y)))))))))
 (define-primitive-procedure '*j-inverse
  (unary *j-inverse "*j-inverse")
  (lambda (v vs) (unimplemented "*j-inverse"))
  '(lambda ((forward x-reverse))
    (let ((x-reverse (primal (forward x-reverse)))
	  ((perturbation x-reverse) (tangent (forward x-reverse))))
     (bundle (*j-inverse x-reverse) (*j-inverse (perturbation x-reverse)))))
  '(lambda ((reverse x-reverse))
    (let ((x-reverse (*j-inverse (reverse x-reverse))))
     ;; The *j composed with *j-inverse could be optimized away.
     (cons (*j (*j-inverse x-reverse))
	   (lambda ((sensitivity y)) (cons '() (*j (sensitivity y))))))))
 (initialize-forwards-and-reverses!))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
