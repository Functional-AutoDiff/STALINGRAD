(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004, 2005, and 2006 Purdue University. All rights reserved.

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
;;;    http://www-bcl.cs.nuim.ie/~barak/

;;; needs work
;;;  1. zero, plus, primal, tangent, bundle, *j, and *j-inverse should be
;;;     lazy.
;;;  2. does making plus lazy eliminate the need to special case for generic
;;;     zeros?
;;;  3. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  4. We removed -wizard because macro expansion required (ignore) and
;;;     (consvar x1 x2). Someday we need to put it back in.
;;;  5. For now, we don't optimize away null tangents.

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

;;; Experimental threads
;;;  1. (lambda (x) (bundle (f (primal x)) (f (tangent x)))) ->
;;;     (lambda (x) (f x))

(include "QobiScheme.sch")
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

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 name procedure abstract-procedure forward reverse meter)

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

(define-structure forward-cache-entry primal? primal tangent? tangent forward)

(define-structure reverse-cache-entry primal reverse)

;;; We used to have abstract-environment slots for abstract closures (both
;;; recursive and nonrecursive). But since all such abstract environments must
;;; map precisely the free variables of the expression for nonrecursive
;;; closures and the letrec recursive closure variables for recursive closures,
;;; we take the environments simply to be a list of abstract values in the
;;; canonial order of the free variables or letrec recursive closure variables
;;; respectively. Note that the abstract values in the abstract closures need
;;; not be closed, i.e. they may contain deBruin references to containing
;;; abstract values.

(define-structure abstract-nonrecursive-closure
 abstract-values
 expression)

(define-structure abstract-recursive-closure
 abstract-values
 variables				;vector
 expressions				;vector
 index)

;;; A proto abstract value is
;;; - (),
;;; - #t,
;;; - #f,
;;; - a real,
;;; - real,
;;; - a primitive procedure,
;;; - a nonrecursive closure, or
;;; - a recursive closure.

;;; An abstract value is a list of proto abstract values or an up.

(define-structure up index)

;;; An abstract flow is a list of abstract-environment bindings. All of the
;;; abstract environments in the abstract-environment bindings of a given
;;; abstract flow must map the same set of variables, namely precisely the
;;; free variables in the abstract expresssion binding that contains that
;;; abstract flow. Thus we represent the abstract environment in an
;;; abstract-environment binding as a list of abstract values in the canonical
;;; order of the free variables. Note that both the abstract values in the
;;; abstract environment of an abstract-environment binding as well as the
;;; abstract value in an abstract-environment binding must be closed, i.e. they
;;; may not contain free deBruin references because there are no enclosing
;;; abstract values.

(define-structure abstract-environment-binding
 abstract-values
 abstract-value)

(define-structure abstract-expression-binding expression abstract-flow)

;;; Variables

(define *gensym* 0)

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

(define *trace-nonrecursive-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-nicely?* #f)

(define *unabbreviate-transformed?* #t)

(define *unabbreviate-nonrecursive-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *letrec-as-y?* #f)

(define *anal?* #t)

(define *x* #f)

(define *memoized?* #f)

(define *church?* #f)

(define *cfa0?* #f)

(define *l1* #f)

(define *l2* #f)

(define *l3* #f)

(define *nonrecursive-closure-coalescing-strategy* #f)

(define *l4* #f)

(define *recursive-closure-coalescing-strategy* #f)

(define *l5* #f)

(define *matching-nonrecursive-closure-depth?* #f)

(define *anf-convert?* #t)

(define *allow-only-single-concrete-real?* #f)

(define *track-flow-analysis?* #f)

(define *only-initialized-flows?* #f)
(define *only-updated-bindings?* #f)

(define *include-prior-values?* #t)

(define *debug?* #f)
(define *debug-level* 0)

(define *warn?* #t)
(define *use-alpha-equivalence?* #f)
(define *memoize-alpha-matching?* #f)
(define *memoize-nonrecursive-alpha-matching?* #f)
(define *new-subset* #f)
(define *new-find-path?* #t)

;;; Instrumentation
(define *num-updates* 0)

(define *num-calls-abstract-value-union* 0)
(define *num-paths-looked-at* 0)
(define *total-size-paths-looked-at* 0)
(define *num-calls-limit-depth-to* 0)
(define *num-calls-reduce-depth!* 0)
(define *num-calls-abstract-value-subset* 0)
(define *num-calls-abstract-value-subset-loop?* 0)
(define *num-calls-free-variables* 0)

(define *num-abstract-environment-bindings* 0)
(define *num-calls-abstract-value-in-matching-abstract-environment-hit* 0)
(define *num-calls-abstract-value-in-matching-abstract-environment-miss* 0)
(define *num-calls-multiply-out-nonrecursive-closure* 0)
(define *num-nonrecursive-closures-multiplied-out* 0)
(define *num-calls-multiply-out-recursive-closure* 0)
(define *num-recursive-closures-multiplied-out* 0)

(define *num-calls-abstract-analysis-union* 0)
(define *num-abstract-expression-bindings-in-analysis-unions* 0)
(define *num-calls-create-abstract-analysis* 0)

(define *time-in-widen* 0)
(define *time-in-l2* 0)
(define *time-in-l3* 0)
(define *time-in-l4* 0)
(define *time-in-l5* 0)

(define *time-in-subset* 0)
(define *time-in-generic-union* 0)

(define *time-in-match-us* 0)
(define *time-in-union-us* 0)
(define *time-in-loop* 0)

(define *bucket-names* '())
(define *time-buckets* (make-vector (length *bucket-names*) 0))
(define *bucket-stack* '())

;;; Procedures

;;; VLAD datastructures

(define vlad-true #t)

(define vlad-false #f)

(define (vlad-true? v)
 (if *church?*
     ;; (lambda (p)
     ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) a))) x3))) (x2 (p x1)))
     ;;   x2))
     (and
      (nonrecursive-closure? v)
      (not (vlad-forward? v))
      (not (vlad-reverse? v))
      (null? (nonrecursive-closure-variables v))
      (let*? (nonrecursive-closure-body v))
      (= (length (let*-variables (nonrecursive-closure-body v))) 2)
      (lambda-expression?
       (first (let*-expressions (nonrecursive-closure-body v))))
      (let*?
       (lambda-expression-body
	(first (let*-expressions (nonrecursive-closure-body v)))))
      (= (length (let*-variables
		  (lambda-expression-body
		   (first (let*-expressions (nonrecursive-closure-body v))))))
	 1)
      (lambda-expression?
       (first (let*-expressions
	       (lambda-expression-body
		(first (let*-expressions (nonrecursive-closure-body v)))))))
      (variable-access-expression?
       (lambda-expression-body
	(first (let*-expressions
		(lambda-expression-body
		 (first (let*-expressions (nonrecursive-closure-body v))))))))
      ;; Check that x3 is bound to (lambda (d) a), not (lambda (d) d).
      (variable=?
       (variable-access-expression-variable
	(lambda-expression-body
	 (first (let*-expressions
		 (lambda-expression-body
		  (first (let*-expressions (nonrecursive-closure-body v))))))))
       (lambda-expression-variable
	(first (let*-expressions (nonrecursive-closure-body v)))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (let*-body
	(lambda-expression-body
	 (first (let*-expressions (nonrecursive-closure-body v))))))
      (variable=?
       (variable-access-expression-variable
	(let*-body
	 (lambda-expression-body
	  (first (let*-expressions (nonrecursive-closure-body v))))))
       (first (let*-variables
	       (lambda-expression-body
		(first (let*-expressions (nonrecursive-closure-body v)))))))
      (application? (second (let*-expressions (nonrecursive-closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (nonrecursive-closure-variable v))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (first (let*-variables (nonrecursive-closure-body v))))
      (variable-access-expression? (let*-body (nonrecursive-closure-body v)))
      (variable=? (variable-access-expression-variable
		   (let*-body (nonrecursive-closure-body v)))
		  (second (let*-variables (nonrecursive-closure-body v)))))
     (eq? v #t)))

(define (vlad-false? v)
 (if *church?*
     ;; (lambda (p)
     ;;  (let* ((x1 (lambda (a) (let* ((x3 (lambda (d) d))) x3))) (x2 (p x1)))
     ;;   x2))
     (and
      (nonrecursive-closure? v)
      (not (vlad-forward? v))
      (not (vlad-reverse? v))
      (null? (nonrecursive-closure-variables v))
      (let*? (nonrecursive-closure-body v))
      (= (length (let*-variables (nonrecursive-closure-body v))) 2)
      (lambda-expression?
       (first (let*-expressions (nonrecursive-closure-body v))))
      (let*?
       (lambda-expression-body
	(first (let*-expressions (nonrecursive-closure-body v)))))
      (= (length (let*-variables
		  (lambda-expression-body
		   (first (let*-expressions (nonrecursive-closure-body v))))))
	 1)
      (lambda-expression?
       (first (let*-expressions
	       (lambda-expression-body
		(first (let*-expressions (nonrecursive-closure-body v)))))))
      (variable-access-expression?
       (lambda-expression-body
	(first (let*-expressions
		(lambda-expression-body
		 (first (let*-expressions (nonrecursive-closure-body v))))))))
      (variable=?
       (variable-access-expression-variable
	(lambda-expression-body
	 (first (let*-expressions
		 (lambda-expression-body
		  (first (let*-expressions (nonrecursive-closure-body v))))))))
       (lambda-expression-variable
	(first (let*-expressions
		(lambda-expression-body
		 (first (let*-expressions (nonrecursive-closure-body v))))))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (let*-body
	(lambda-expression-body
	 (first (let*-expressions (nonrecursive-closure-body v))))))
      (variable=?
       (variable-access-expression-variable
	(let*-body
	 (lambda-expression-body
	  (first (let*-expressions (nonrecursive-closure-body v))))))
       (first (let*-variables
	       (lambda-expression-body
		(first (let*-expressions (nonrecursive-closure-body v)))))))
      (application? (second (let*-expressions (nonrecursive-closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (nonrecursive-closure-variable v))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (first (let*-variables (nonrecursive-closure-body v))))
      (variable-access-expression? (let*-body (nonrecursive-closure-body v)))
      (variable=? (variable-access-expression-variable
		   (let*-body (nonrecursive-closure-body v)))
		  (second (let*-variables (nonrecursive-closure-body v)))))
     (eq? v #f)))

(define (vlad-boolean? v) (or (vlad-true? v) (vlad-false? v)))

(define (vlad-forward? v)
 ;; needs work: church
 (or (bundle? v)
     (and (nonrecursive-closure? v)
	  (not (null? (nonrecursive-closure-tags v)))
	  (eq? (first (nonrecursive-closure-tags v)) 'forward))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'forward))))

(define (vlad-reverse? v)
 ;; needs work: church
 (or (reverse-tagged-value? v)
     (and (nonrecursive-closure? v)
	  (not (null? (nonrecursive-closure-tags v)))
	  (eq? (first (nonrecursive-closure-tags v)) 'reverse))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'reverse))))

(define (vlad-pair? v tags)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 ;; needs work: church
 (if (null? tags)
     (and
      (nonrecursive-closure? v)
      (not (vlad-forward? v))
      (not (vlad-reverse? v))
      (= (length (nonrecursive-closure-variables v)) 2)
      (let*? (nonrecursive-closure-body v))
      (= (length (let*-variables (nonrecursive-closure-body v))) 2)
      (application? (first (let*-expressions (nonrecursive-closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee
	(first (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (first (let*-expressions (nonrecursive-closure-body v)))))
		  (nonrecursive-closure-variable v))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument
	(first (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (first (let*-expressions (nonrecursive-closure-body v)))))
		  (first (nonrecursive-closure-variables v)))
      (application? (second (let*-expressions (nonrecursive-closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-callee
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-callee
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (first (let*-variables (nonrecursive-closure-body v))))
      ;; Technically not needed since in ANF.
      (variable-access-expression?
       (application-argument
	(second (let*-expressions (nonrecursive-closure-body v)))))
      (variable=? (variable-access-expression-variable
		   (application-argument
		    (second (let*-expressions (nonrecursive-closure-body v)))))
		  (second (nonrecursive-closure-variables v)))
      ;; Technically not needed since in ANF.
      (variable-access-expression? (let*-body (nonrecursive-closure-body v)))
      (variable=? (variable-access-expression-variable
		   (let*-body (nonrecursive-closure-body v)))
		  (second (let*-variables (nonrecursive-closure-body v)))))
     (case (first tags)
      ((forward) (vlad-pair? (primal v) (rest tags)))
      ((reverse) (vlad-pair? (*j-inverse v) (rest tags)))
      (else (fuck-up)))))

(define (vlad-car v tags)
 ;; needs work: church
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take vlad-car of a non-pair" v))
	(vector-ref (nonrecursive-closure-values v) 0))
       (else (case (first tags)
	      ((forward) (bundle (vlad-car (primal v) (rest tags))
				 (vlad-car (tangent v) (rest tags))))
	      ((reverse) (*j (vlad-car (*j-inverse v) (rest tags))))
	      (else (fuck-up))))))

(define (vlad-cdr v tags)
 ;; needs work: church
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take vlad-cdr of a non-pair" v))
	(vector-ref (nonrecursive-closure-values v) 1))
       (else (case (first tags)
	      ((forward) (bundle (vlad-cdr (primal v) (rest tags))
				 (vlad-cdr (tangent v) (rest tags))))
	      ((reverse) (*j (vlad-cdr (*j-inverse v) (rest tags))))
	      (else (fuck-up))))))

(define (vlad-cons v1 v2)
 ;; needs work: church
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (make-nonrecursive-closure
  '(a d)
  (vector v1 v2)
  'm
  (index 'm
	 '(a d)
	 (new-let* '(x1 x2)
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
      ((forward) (bundle (cons*ify (map primal xs) (rest tags))
			 (cons*ify (map tangent xs) (rest tags))))
      ((reverse) (*j (cons*ify (map *j-inverse xs) (rest tags))))
      (else (fuck-up)))))

(define (vlad-procedure? v)
 (and (or (primitive-procedure? v)
	  (nonrecursive-closure? v)
	  (recursive-closure? v))
      (not (vlad-pair? v '()))
      (not (vlad-true? v))
      (not (vlad-false? v))))

(define (vlad-equal? v1 v2)
 ;; needs work: church
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (and (not *church?*)
	  (or (and (vlad-true? v1) (vlad-true? v2))
	      (and (vlad-false? v1) (vlad-false? v2))))
     (and (real? v1) (real? v2) (= v1 v2))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (= (vector-length (nonrecursive-closure-values v1))
	     (vector-length (nonrecursive-closure-values v2)))
	  (alpha-equivalent?
	   (nonrecursive-closure-body v1)
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
			(recursive-closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (vlad-equal? (bundle-primal v1) (bundle-primal v2))
	  (vlad-equal? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (vlad-equal? (reverse-tagged-value-primal v1)
		       (reverse-tagged-value-primal v2)))))

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

(define (perturbationify x) `(perturbation ,x))

(define (forwardify x) `(forward ,x))

(define (sensitivityify x) `(sensitivity ,x))

(define (backpropagatorify x) `(backpropagator ,x))

(define (reverseify x) `(reverse ,x))

(define (perturbation-variable? x)
 (and (pair? x)
      (or (eq? (first x) 'perturbation)
	  (and (eq? (first x) 'alpha) (perturbation-variable? (second x))))))

(define (forward-variable? x)
 (and (pair? x)
      (or (eq? (first x) 'forward)
	  (and (eq? (first x) 'alpha) (forward-variable? (second x))))))

(define (sensitivity-variable? x)
 (and (pair? x)
      (or (eq? (first x) 'sensitivity)
	  (and (eq? (first x) 'alpha) (sensitivity-variable? (second x))))))

(define (backpropagator-variable? x)
 (and (pair? x)
      (or (eq? (first x) 'backpropagator)
	  (and (eq? (first x) 'alpha) (backpropagator-variable? (second x))))))

(define (reverse-variable? x)
 (and (pair? x)
      (or (eq? (first x) 'reverse)
	  (and (eq? (first x) 'alpha) (reverse-variable? (second x))))))

(define (unperturbationify x)
 (unless (perturbation-variable? x) (fuck-up))
 (let loop ((x x))
  (unless (pair? x) (fuck-up))
  (case (first x)
   ((perturbation) (second x))
   ((alpha) (loop (second x)))
   (else (fuck-up)))))

(define (unforwardify x)
 (unless (forward-variable? x) (fuck-up))
 (let loop ((x x))
  (unless (pair? x) (fuck-up))
  (case (first x)
   ((forward) (second x))
   ((alpha) (loop (second x)))
   (else (fuck-up)))))

(define (unsensitivityify x)
 (unless (sensitivity-variable? x) (fuck-up))
 (let loop ((x x))
  (unless (pair? x) (fuck-up))
  (case (first x)
   ((sensitivity) (second x))
   ((alpha) (loop (second x)))
   (else (fuck-up)))))

(define (unbackpropagatorify x)
 (unless (backpropagator-variable? x) (fuck-up))
 (let loop ((x x))
  (unless (pair? x) (fuck-up))
  (case (first x)
   ((backpropagator) (second x))
   ((alpha) (loop (second x)))
   (else (fuck-up)))))

(define (unreverseify x)
 (unless (reverse-variable? x) (fuck-up))
 (let loop ((x x))
  (unless (pair? x) (fuck-up))
  (case (first x)
   ((reverse) (second x))
   ((alpha) (loop (second x)))
   (else (fuck-up)))))

(define (lax-unreverseify x)
 (let loop ((x x))
  (if (pair? x)
      (case (first x)
       ((reverse) (second x))
       ((alpha) (loop (second x)))
       (else x))
      x)))

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
 (cond ((forward-variable? x) (cons 'forward (variable-tags (unforwardify x))))
       ((reverse-variable? x) (cons 'reverse (variable-tags (unreverseify x))))
       (else '())))

(define (lambda-expression-tags e)
 (variable-tags (lambda-expression-variable e)))

(define (nonrecursive-closure-tags v)
 (variable-tags (nonrecursive-closure-variable v)))

(define (recursive-closure-tags v)
 (variable-tags (vector-ref (recursive-closure-argument-variables v)
			    (recursive-closure-index v))))

;;; Expression constructors

(define (new-variable-access-expression x)
 (make-variable-access-expression x #f))

(define (new-lambda-expression x e)
 (make-lambda-expression (removep variable=? x (free-variables e)) #f x e))

(define (new-application e1 e2)
 (make-application
  e1 e2 (sort-variables
	 (union-variables (free-variables e1) (free-variables e2)))))

(define (create-application bs tags e . es)
 (new-application e (make-cons* bs tags es)))

(define (new-let* xs es e)
 (if (null? xs)
     e
     (new-application
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

;;; LET*

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))))

;;; needs work: The counterparts of these used to be constant-time but are no
;;; longer so. This has implications for vestigial let*-expressions.

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
	     (panic (format #f "Invalid definition: ~s" d))))
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

(define (letrec-recursive-closure-variables xs1 xs2 es)
 (sort-variables
  (set-differencep
   variable=?
   (reduce
    union-variables
    (map (lambda (x e) (removep variable=? x (free-variables e))) xs2 es)
    '())
   xs1)))

(define (free-variables-old e)
 (set! *num-calls-free-variables* (+ *num-calls-free-variables* 1))
 (sort-variables
  (let loop ((e e))
   (cond ((constant-expression? e) '())
	 ((variable-access-expression? e)
	  (list (variable-access-expression-variable e)))
	 ((lambda-expression? e)
	  ;; This is a vestigial let*-expression.
	  (if (eq? (lambda-expression-free-variables e) #f)
	      (removep variable=?
		       (lambda-expression-variable e)
		       (loop (lambda-expression-body e)))
	      (lambda-expression-free-variables e)))
	 ((application? e)
	  (union-variables (loop (application-callee e))
			   (loop (application-argument e))))
	 ((letrec-expression? e) (letrec-expression-body-free-variables e))
	 (else (fuck-up))))))

(define (free-variables e)
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e)
	(if (eq? (lambda-expression-free-variables e) #f)
	    (free-variables-old e)
	    (lambda-expression-free-variables e)))
       ((application? e)
	(if (eq? (application-free-variables e) #f)
	    (free-variables-old e)
	    (application-free-variables e)))
       ((letrec-expression? e) (letrec-expression-body-free-variables e))
       (else (fuck-up))))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (variable=? x-prime x) (memp variable=? x-prime xs)) (fuck-up))
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
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))
		     (free-variables e)))
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
  (fuck-up))
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
  (else (fuck-up))))

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
	   (inner (first result)
		  (rest xs1)
		  (rest xs2)
		  (rest es)
		  (cons (make-variable-binding
			 (first xs1)
			 (new-lambda-expression
			  (first xs2) (anf-result result)))
			bs2))))))
    (else (fuck-up))))))

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
       ((letrec-expression? e) (fuck-up))
       (else (fuck-up))))

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
	  (else (fuck-up)))))))))

;;; Constant Conversion

(define (constants-in e)
 (cond ((constant-expression? e) (list (constant-expression-value e)))
       ((variable-access-expression? e) '())
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
  ((if)
   (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
   (if *church?*
       `((,(second e) (cons (lambda () ,(third e)) (lambda () ,(fourth e)))))
       ;; needs work: to ensure that you don't shadow if-procedure
       `((if-procedure
	  ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))))
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
    ((cons) (concrete->abstract-expression (macro-expand e)))
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
  (else (fuck-up))))

(define (parse e)
 (let* ((e (concrete->abstract-expression e))
	(bs (map (lambda (v) (make-value-binding (gensym) v))
		 (constants-in e)))
	(e (constant-convert bs e))
	(e (copy-propagate (anf-convert (alpha-convert e (free-variables e)))))
	(xs (free-variables e))
	(bs (append bs *value-bindings*)))
  (list
   (index #f xs e)
   (map (lambda (x)
	 (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))
	xs))))

;;; AD

(define (zero x)
 ;; needs work: church
 (cond ((null? x) '())
       ((and (not *church?*) (vlad-boolean? x)) '())
       ((real? x) 0)
       ((primitive-procedure? x) '())
       ((nonrecursive-closure? x)
	(cons*ify (map zero (base-values x)) (nonrecursive-closure-tags x)))
       ((recursive-closure? x)
	(cons*ify (map zero (base-values x)) (recursive-closure-tags x)))
       ((bundle? x)
	(make-bundle (zero (bundle-primal x)) (zero (bundle-tangent x))))
       ((reverse-tagged-value? x)
	(make-reverse-tagged-value (zero (reverse-tagged-value-primal x))))
       (else (fuck-up))))

(define (plus x1 x2)
 (define (conform? x1 x2)
  (or (and (vlad-forward? x1)
	   (vlad-forward? x2)
	   (conform? (primal x1) (primal x2))
	   (conform? (tangent x1) (tangent x2)))
      (and (vlad-reverse? x1)
	   (vlad-reverse? x2)
	   (conform? (*j-inverse x1) (*j-inverse x2)))
      (and (null? x1) (null? x2))
      (and (real? x1) (real? x2))
      (and (vlad-pair? x1 '())
	   (vlad-pair? x2 '())
	   (conform? (vlad-car x1 '()) (vlad-car x2 '()))
	   (conform? (vlad-cdr x1 '()) (vlad-cdr x2 '())))))
 (define (plus x1 x2)
  (cond ((vlad-forward? x1)
	 (bundle (plus (primal x1) (primal x2))
		 (plus (tangent x1) (tangent x2))))
	((vlad-reverse? x1) (*j (plus (*j-inverse x1) (*j-inverse x2))))
	((null? x1) '())
	((real? x1) (+ x1 x2))
	(else (vlad-cons (plus (vlad-car x1 '()) (vlad-car x2 '()))
			 (plus (vlad-cdr x1 '()) (vlad-cdr x2 '()))))))
 (when *anal?*
  (unless (conform? x1 x2)
   (run-time-error "The arguments to plus are nonconformant" x1 x2)))
 (plus x1 x2))

;;; Base variables

(define (forward-uptag-variables xs1 xs2)
 (map (lambda (x1)
       (unless (one (lambda (x2) (variable=? x1 (unforwardify x2))) xs2)
	(fuck-up))
       (find-if (lambda (x2) (variable=? x1 (unforwardify x2))) xs2))
      xs1))

(define (reverse-uptag-variables xs1 xs2)
 (map (lambda (x1)
       (unless (one (lambda (x2) (variable=? x1 (lax-unreverseify x2))) xs2)
	(fuck-up))
       (find-if (lambda (x2) (variable=? x1 (lax-unreverseify x2))) xs2))
      xs1))

(define (base-variables x)
 (cond
  ((primitive-procedure? x) '())
  ((nonrecursive-closure? x)
   (let ((xs (nonrecursive-closure-variables x)))
    (if (null? (nonrecursive-closure-tags x))
	xs
	(case (first (nonrecursive-closure-tags x))
	 ((forward) (forward-uptag-variables (base-variables (primal x)) xs))
	 ((reverse)
	  (reverse-uptag-variables (base-variables (*j-inverse x)) xs))
	 (else (fuck-up))))))
  ((recursive-closure? x)
   (let ((xs (recursive-closure-variables x)))
    (if (null? (recursive-closure-tags x))
	xs
	(case (first (recursive-closure-tags x))
	 ((forward) (forward-uptag-variables (base-variables (primal x)) xs))
	 ((reverse)
	  (reverse-uptag-variables (base-variables (*j-inverse x)) xs))
	 (else (fuck-up))))))
  (else (fuck-up))))

(define (base-values x)
 (let ((xs1 (base-variables x))
       (xs2 (cond
	     ((nonrecursive-closure? x) (nonrecursive-closure-variables x))
	     ((recursive-closure? x) (recursive-closure-variables x))
	     (else (fuck-up))))
       (vs2 (cond ((nonrecursive-closure? x) (nonrecursive-closure-values x))
		  ((recursive-closure? x) (recursive-closure-values x))
		  (else (fuck-up)))))
  (map (lambda (x1) (vector-ref vs2 (positionp variable=? x1 xs2))) xs1)))

(define (nonrecursive-closure-base-letrec-variables x)
 (cond
  ((primitive-procedure? x) '())
  ((nonrecursive-closure? x)
   (let ((xs (anf-letrec-bodies-free-variables
	      (nonrecursive-closure-body x))))
    (if (null? (nonrecursive-closure-tags x))
	xs
	(case (first (nonrecursive-closure-tags x))
	 ((forward)
	  (forward-uptag-variables
	   (nonrecursive-closure-base-letrec-variables (primal x)) xs))
	 ((reverse)
	  (reverse-uptag-variables
	   (nonrecursive-closure-base-letrec-variables (*j-inverse x)) xs))
	 (else (fuck-up))))))
  (else (fuck-up))))

(define (recursive-closure-base-letrec-variables x i)
 (cond ((primitive-procedure? x) '())
       ((recursive-closure? x)
	(let ((xs (anf-letrec-bodies-free-variables
		   (vector-ref (recursive-closure-bodies x) i))))
	 (if (null? (recursive-closure-tags x))
	     xs
	     (case (first (recursive-closure-tags x))
	      ((forward)
	       (forward-uptag-variables
		(recursive-closure-base-letrec-variables (primal x) i) xs))
	      ((reverse)
	       (reverse-uptag-variables
		(recursive-closure-base-letrec-variables (*j-inverse x) i) xs))
	      (else (fuck-up))))))
       (else (fuck-up))))

(define (lambda-expression-base-free-variables e)
 (let ((xs (free-variables e)))
  (if (null? (lambda-expression-tags e))
      xs
      (case (first (lambda-expression-tags e))
       ((forward)
	(forward-uptag-variables
	 (lambda-expression-base-free-variables (forward-transform-inverse e))
	 xs))
       ((reverse)
	(reverse-uptag-variables
	 (lambda-expression-base-free-variables (reverse-transform-inverse e))
	 xs))
       (else (fuck-up))))))

(define (anf-letrec-bodies-base-free-variables e)
 (let ((xs (if (letrec-expression? (lambda-expression-body e))
	       (letrec-expression-bodies-free-variables
		(lambda-expression-body e))
	       '())))
  (if (null? (lambda-expression-tags e))
      xs
      (case (first (lambda-expression-tags e))
       ((forward)
	(forward-uptag-variables
	 (anf-letrec-bodies-base-free-variables (forward-transform-inverse e))
	 xs))
       ((reverse)
	(forward-uptag-variables
	 (anf-letrec-bodies-base-free-variables (reverse-transform-inverse e))
	 xs))
       (else (fuck-up))))))

;;; J*

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
       (else (fuck-up))))

(define (forward-transform-inverse e)
 (cond ((variable-access-expression? e) (unforwardify-access e))
       ((lambda-expression? e)
	(new-lambda-expression
	 (unforwardify (lambda-expression-variable e))
	 (forward-transform-inverse (lambda-expression-body e))))
       ((application? e)
	(new-application
	 (forward-transform-inverse (application-callee e))
	 (forward-transform-inverse (application-argument e))))
       ((letrec-expression? e)
	(new-letrec-expression
	 (map unforwardify (letrec-expression-procedure-variables e))
	 (map unforwardify (letrec-expression-argument-variables e))
	 (map forward-transform-inverse (letrec-expression-bodies e))
	 (forward-transform-inverse (letrec-expression-body e))))
       (else (fuck-up))))

(define (primal x-forward)
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
	      ;; needs work: church
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((and (not *church?*) (vlad-boolean? x-forward))
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((real? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((primitive-procedure? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((nonrecursive-closure? x-forward)
		(unless (and
			 (not (null? (nonrecursive-closure-tags x-forward)))
			 (eq? (first (nonrecursive-closure-tags x-forward))
			      'forward))
		 (run-time-error
		  "Attempt to take primal of a non-forward value" x-forward))
		(let ((b (find-if (lambda (b)
				   (vlad-equal? x-forward
						(primitive-procedure-forward
						 (value-binding-value b))))
				  *value-bindings*)))
		 (if b
		     (value-binding-value b)
		     (let* ((e (forward-transform-inverse
				(new-lambda-expression
				 (nonrecursive-closure-variable x-forward)
				 (nonrecursive-closure-body x-forward))))
			    (x (lambda-expression-variable e))
			    (xs (free-variables e)))
		      (make-nonrecursive-closure
		       xs
		       ;; We don't do add/remove-slots here.
		       (map-vector
			primal (nonrecursive-closure-values x-forward))
		       x
		       (index x xs (lambda-expression-body e)))))))
	       ((recursive-closure? x-forward)
		(unless (and (not (null? (recursive-closure-tags x-forward)))
			     (eq? (first (recursive-closure-tags x-forward))
				  'forward))
		 (run-time-error
		  "Attempt to take primal of a non-forward value" x-forward))
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
				    (new-lambda-expression x e)))
				  (recursive-closure-argument-variables
				   x-forward)
				  (recursive-closure-bodies x-forward))))
			    (xs1 (map-vector
				  unforwardify
				  (recursive-closure-procedure-variables
				   x-forward)))
			    (xs (letrec-recursive-closure-variables
				 (vector->list xs1)
				 (map lambda-expression-variable es)
				 (map lambda-expression-body es))))
		      (make-recursive-closure
		       xs
		       ;; We don't do add/remove-slots here.
		       (map-vector primal
				   (recursive-closure-values x-forward))
		       xs1
		       (list->vector (map lambda-expression-variable es))
		       (list->vector
			(map (lambda (e)
			      (index (lambda-expression-variable e)
				     (append (vector->list xs1) xs)
				     (lambda-expression-body e)))
			     es))
		       (recursive-closure-index x-forward))))))
	       ((bundle? x-forward) (bundle-primal x-forward))
	       ((reverse-tagged-value? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
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

(define (tangent x-forward)
 (let ((forward-cache-entry
	(find-if
	 (lambda (forward-cache-entry)
	  (vlad-equal?
	   (forward-cache-entry-forward forward-cache-entry) x-forward))
	 *forward-cache*)))
  (if (and forward-cache-entry
	   (forward-cache-entry-tangent? forward-cache-entry))
      (forward-cache-entry-tangent forward-cache-entry)
      (let* ((result
	      ;; needs work: church
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((and (not *church?*) (vlad-boolean? x-forward))
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((real? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((primitive-procedure? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((nonrecursive-closure? x-forward)
		(unless (and
			 (not (null? (nonrecursive-closure-tags x-forward)))
			 (eq? (first (nonrecursive-closure-tags x-forward))
			      'forward))
		 (run-time-error
		  "Attempt to take tangent of a non-forward value" x-forward))
		(if (some (lambda (b)
			   (vlad-equal? x-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
			  *value-bindings*)
		    '()
		    (cons*ify (map tangent (base-values x-forward))
			      (rest (nonrecursive-closure-tags x-forward)))))
	       ((recursive-closure? x-forward)
		(unless (and (not (null? (recursive-closure-tags x-forward)))
			     (eq? (first (recursive-closure-tags x-forward))
				  'forward))
		 (run-time-error
		  "Attempt to take tangent of a non-forward value" x-forward))
		(if (some (lambda (b)
			   (vlad-equal? x-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
			  *value-bindings*)
		    '()
		    (cons*ify (map tangent (base-values x-forward))
			      (rest (recursive-closure-tags x-forward)))))
	       ((bundle? x-forward) (bundle-tangent x-forward))
	       ((reverse-tagged-value? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
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
	  (when (forward-cache-entry-tangent? forward-cache-entry) (fuck-up))
	  (set-forward-cache-entry-tangent?! forward-cache-entry #t)
	  (set-forward-cache-entry-tangent! forward-cache-entry result))
	 (else (set! *forward-cache*
		     (cons (make-forward-cache-entry #f #f #t result x-forward)
			   *forward-cache*)))))
       result))))

(define (bundle x x-perturbation)
 (define (tagged-null? tags x)
  (if (null? tags)
      (null? x)
      (case (first tags)
       ((forward) (and (bundle? x)
		       (tagged-null? (rest tags) (bundle-primal x))
		       (tagged-null? (rest tags) (bundle-tangent x))))
       ((reverse)
	(and (reverse-tagged-value? x)
	     (tagged-null? (rest tags) (reverse-tagged-value-primal x))))
       (else (fuck-up)))))
 (define (legitimate*? xs x-perturbations tags)
  ;; XS is a list, X-PERTURBATIONS is a tuple.
  (or (and (null? xs) (tagged-null? tags x-perturbations))
      (and (not (null? xs))
	   (null? (rest xs))
	   (legitimate? (first xs) x-perturbations))
      (and (not (null? xs))
	   (not (null? (rest xs)))
	   (vlad-pair? x-perturbations tags)
	   (legitimate? (first xs) (vlad-car x-perturbations tags))
	   (legitimate*? (rest xs) (vlad-cdr x-perturbations tags) tags))))
 (define (legitimate? x x-perturbation)
  ;; needs work: church
  (or (and (null? x) (null? x-perturbation))
      (and (not *church?*) (vlad-boolean? x) (null? x-perturbation))
      (and (real? x) (real? x-perturbation))
      (and (primitive-procedure? x) (null? x-perturbation))
      (and (nonrecursive-closure? x)
	   (legitimate*?
	    (base-values x) x-perturbation (nonrecursive-closure-tags x)))
      (and (recursive-closure? x)
	   (legitimate*?
	    (base-values x) x-perturbation (recursive-closure-tags x)))
      (and (bundle? x)
	   (bundle? x-perturbation)
	   (legitimate? (bundle-primal x)
			(bundle-primal x-perturbation))
	   (legitimate? (bundle-tangent x)
			(bundle-tangent x-perturbation)))
      (and (reverse-tagged-value? x)
	   (reverse-tagged-value? x-perturbation)
	   (legitimate? (reverse-tagged-value-primal x)
			(reverse-tagged-value-primal x-perturbation)))))
 (define (bundle* xs x-perturbations tags)
  ;; XS is a list, X-PERTURBATIONS is a tuple, the result is a list.
  (cond
   ((null? xs) '())
   ((null? (rest xs)) (list (bundle (first xs) x-perturbations)))
   (else (cons (bundle (first xs) (vlad-car x-perturbations tags))
	       (bundle* (rest xs) (vlad-cdr x-perturbations tags) tags)))))
 (define (bundle x x-perturbation)
  ;; needs work: church
  (cond
   ((null? x) (make-bundle x x-perturbation))
   ((and (not *church?*) (vlad-boolean? x)) (make-bundle x x-perturbation))
   ((real? x) (make-bundle x x-perturbation))
   ((primitive-procedure? x)
    (unless (null? x-perturbation) (fuck-up))
    (primitive-procedure-forward x))
   ((nonrecursive-closure? x)
    (let* ((e (forward-transform
	       (new-lambda-expression (nonrecursive-closure-variable x)
				      (nonrecursive-closure-body x))))
	   (x1 (lambda-expression-variable e))
	   (xs (free-variables e)))
     (make-nonrecursive-closure
      xs
      ;; This should use a generalized add/remove-slots here.
      (list->vector
       (let ((xs (base-variables x))
	     (vs (bundle* (base-values x)
			  x-perturbation
			  (nonrecursive-closure-tags x))))
	(map (lambda (x v)
	      (let ((i (positionp variable=? x xs)))
	       (if i (list-ref vs i) (j* v))))
	     (nonrecursive-closure-variables x)
	     (vector->list (nonrecursive-closure-values x)))))
      x1
      (index x1 xs (lambda-expression-body e)))))
   ((recursive-closure? x)
    (let* ((es (vector->list
		(map-vector (lambda (x1 e)
			     (forward-transform (new-lambda-expression x1 e)))
			    (recursive-closure-argument-variables x)
			    (recursive-closure-bodies x))))
	   (xs1 (map-vector forwardify
			    (recursive-closure-procedure-variables x)))
	   (xs (letrec-recursive-closure-variables
		(vector->list xs1)
		(map lambda-expression-variable es)
		(map lambda-expression-body es))))
     (make-recursive-closure
      xs
      ;; This should use a generalized add/remove-slots here.
      (list->vector
       (let ((xs (base-variables x))
	     (vs (bundle*
		  (base-values x) x-perturbation (recursive-closure-tags x))))
	(map (lambda (x v)
	      (let ((i (positionp variable=? x xs)))
	       (if i (list-ref vs i) (j* v))))
	     (recursive-closure-variables x)
	     (vector->list (recursive-closure-values x)))))
      xs1
      (list->vector (map lambda-expression-variable es))
      (list->vector (map (lambda (e)
			  (index (lambda-expression-variable e)
				 (append (vector->list xs1) xs)
				 (lambda-expression-body e)))
			 es))
      (recursive-closure-index x))))
   ((bundle? x) (make-bundle x x-perturbation))
   ((reverse-tagged-value? x) (make-bundle x x-perturbation))
   (else (fuck-up))))
 ;; needs work: to memoize inside recursion rather than outside
 (let ((forward-cache-entry
	(find-if
	 (lambda (forward-cache-entry)
	  (and (vlad-equal? (forward-cache-entry-primal forward-cache-entry) x)
	       (vlad-equal? (forward-cache-entry-tangent forward-cache-entry)
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
		  (unless (legitimate? x x-perturbation)
		   (run-time-error "The arguments to bundle are illegitimate"
				   x x-perturbation)))
		 (bundle x x-perturbation))))
   (when *memoized?*
    (set! *forward-cache* (cons forward-cache-entry *forward-cache*))))
  (forward-cache-entry-forward forward-cache-entry)))

(define (j* x) (bundle x (zero x)))

;;; *J

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
 (let loop ((tags tags))
  (if (null? tags)
      e
      ((case (first tags)
	((forward) make-j*)
	((reverse) make-*j)
	(else (fuck-up)))
       bs
       (loop (rest tags))))))

(define (make-car bs tags e)
 ;; We no longer do car-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'car) e)
     (case (first tags)
      ((forward)
       (make-bundle-invocation bs
			       (make-car bs (rest tags) (make-primal bs e))
			       (make-car bs (rest tags) (make-tangent bs e))))
      ((reverse) (make-*j bs (make-car bs (rest tags) (make-*j-inverse bs e))))
      (else (fuck-up)))))

(define (make-cdr bs tags e)
 ;; We no longer do cdr-of-cons conversion.
 (if (null? tags)
     (new-application (added-variable bs 'cdr) e)
     (case (first tags)
      ((forward)
       (make-bundle-invocation bs
			       (make-cdr bs (rest tags) (make-primal bs e))
			       (make-cdr bs (rest tags) (make-tangent bs e))))
      ((reverse) (make-*j bs (make-cdr bs (rest tags) (make-*j-inverse bs e))))
      (else (fuck-up)))))

(define (make-cons bs tags e1 e2)
 (if (null? tags)
     (new-application
      (new-application (added-variable bs 'cons-procedure) e1) e2)
     (case (first tags)
      ((forward)
       (make-bundle-invocation bs
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
	       (cond
		((null? xs) '())
		((null? (rest xs))
		 (if (needed? (first xs))
		     (list (make-variable-binding
			    (sensitivityify (first xs))
			    (make-plus bs
				       (sensitivity-access (first xs))
				       (sensitivity-access t))))
		     '()))
		(else
		 (let ((x (parameter->consvar
			   `(cons* ,@(map sensitivityify xs)))))
		  (cons
		   (make-variable-binding x (sensitivity-access t))
		   (let loop ((xs xs) (x x))
		    (if (null? (rest (rest xs)))
			(append
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
			 (if (needed? (second xs))
			     (list (make-variable-binding
				    (sensitivityify (second xs))
				    (make-plus
				     bs
				     (sensitivity-access (second xs))
				     (make-cdr
				      bs
				      (lambda-expression-tags e)
				      (new-variable-access-expression x)))))
			     '()))
			(if (needed? (first xs))
			    (cons
			     (make-variable-binding
			      (sensitivityify (first xs))
			      (make-plus
			       bs
			       (sensitivity-access (first xs))
			       (make-car bs
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
				'()))))))))))
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
	     (else (fuck-up))))
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
	       (make-cons*-bindings
		bs
		'()
		(list (reverseify x) (backpropagatorify x))
		(new-application
		 (reverseify-access (application-callee e))
		 (reverseify-access (application-argument e)))))
	      (else (fuck-up))))
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
		    (make-cons*-bindings
		     bs
		     tags
		     (map sensitivityify ws)
		     (let loop ((fs fs))
		      (if (null? fs)
			  (make-cons* bs tags (map sensitivity-access ws))
			  (make-plus bs
				     (sensitivity-access (first fs))
				     (loop (rest fs)))))))
		   (make-cons
		    bs
		    '()
		    (let loop ((gs gs))
		     (if (null? gs)
			 (make-cons* bs tags (map sensitivity-access zs))
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
 (if (let*? e)
     (let loop ((xs (let*-variables e))
		(es (let*-expressions e))
		(xs0 '())
		(es0 '()))
      (cond
       ((null? xs) (fuck-up))
       ((and (= (length xs) 3)
	     (result-cons? (first xs) (second xs) (third xs)
			   (first es) (second es) (third es)
			   (let*-body e)))
	(if (null? xs0)
	    (unreverseify-access (partial-cons-argument (first es)))
	    (new-let*
	     (reverse xs0)
	     (reverse es0)
	     (unreverseify-access (partial-cons-argument (first es))))))
       ((and (>= (length xs) 3)
	     (cons-split? (first xs) (second xs) (third xs)
			  (first es) (second es) (third es)))
	(loop (rest (rest (rest xs)))
	      (rest (rest (rest es)))
	      (cons (unreverseify (second xs)) xs0)
	      (cons (let ((e (first es)))
		     (cond ((variable-access-expression? e)
			    (unreverseify-access e))
			   ((application? e)
			    (new-application
			     (unreverseify-access (application-callee e))
			     (unreverseify-access (application-argument e))))
			   (else (fuck-up))))
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
       ((application? (first es))
	(loop (rest xs)
	      (rest es)
	      (cons (unreverseify (first xs)) xs0)
	      (cons (new-application
		     (unreverseify-access (application-callee (first es)))
		     (unreverseify-access (application-argument (first es))))
		    es0)))
       (else (fuck-up))))
     (fuck-up)))

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

(define (added-bindings)
 ;; needs work: To replace anonymous gensym with derived gensym.
 (map (lambda (x) (make-alpha-binding x (hensym)))
      (append
       ;; These are magic names.
       (list 'null 'car 'cdr 'cons-procedure)
       (map value-binding-variable *value-bindings*))))

(define (*j v)
 (let ((reverse-cache-entry
	(find-if (lambda (reverse-cache-entry)
		  (vlad-equal?
		   (reverse-cache-entry-primal reverse-cache-entry) v))
		 *reverse-cache*)))
  (unless reverse-cache-entry
   (set! reverse-cache-entry
	 (make-reverse-cache-entry
	  v
	  ;; needs work: church
	  (cond
	   ((null? v) (make-reverse-tagged-value v))
	   ((and (not *church?*) (vlad-boolean? v))
	    (make-reverse-tagged-value v))
	   ((real? v) (make-reverse-tagged-value v))
	   ((primitive-procedure? v) (primitive-procedure-reverse v))
	   ((nonrecursive-closure? v)
	    (let* ((bs (added-bindings))
		   (e (reverse-transform
		       bs
		       (new-lambda-expression
			(nonrecursive-closure-variable v)
			(nonrecursive-closure-body v))
		       (nonrecursive-closure-base-letrec-variables v)
		       '()
		       (base-variables v)))
		   (e (alpha-convert e (free-variables e)))
		   (x (lambda-expression-variable e))
		   (xs (free-variables e)))
	     (make-nonrecursive-closure
	      xs
	      (add/remove-slots
	       *j
	       (map reverseify (nonrecursive-closure-variables v))
	       xs
	       (nonrecursive-closure-values v)
	       bs)
	      x
	      (index
	       x
	       xs
	       (copy-propagate (anf-convert (lambda-expression-body e)))))))
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
			   (vector->list
			    (recursive-closure-procedure-variables v))
			   (base-variables v))))
			(vector-length (recursive-closure-bodies v))))
		   (xs1 (map-vector
			 reverseify
			 (recursive-closure-procedure-variables v)))
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
	       *j
	       (map reverseify (recursive-closure-variables v))
	       xs
	       (recursive-closure-values v)
	       bs)
	      xs1
	      (list->vector (map lambda-expression-variable es))
	      (list->vector
	       (map (lambda (e)
		     (index (lambda-expression-variable e)
			    (append (vector->list xs1) xs)
			    (copy-propagate
			     (anf-convert (lambda-expression-body e)))))
		    es))
	      (recursive-closure-index v))))
	   ((bundle? v) (make-reverse-tagged-value v))
	   ((reverse-tagged-value? v) (make-reverse-tagged-value v))
	   (else (fuck-up)))))
   (when *memoized?*
    (set! *reverse-cache* (cons reverse-cache-entry *reverse-cache*))))
  (reverse-cache-entry-reverse reverse-cache-entry)))

(define (*j-inverse x-reverse)
 (let ((reverse-cache-entry
	(find-if
	 (lambda (reverse-cache-entry)
	  (vlad-equal? (reverse-cache-entry-reverse reverse-cache-entry)
		       x-reverse))
	 *reverse-cache*)))
  (unless reverse-cache-entry
   (set! reverse-cache-entry
	 (make-reverse-cache-entry
	  ;; needs work: church
	  (cond
	   ((null? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((and (not *church?*) (vlad-boolean? x-reverse))
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((real? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((primitive-procedure? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((nonrecursive-closure? x-reverse)
	    (unless (and (not (null? (nonrecursive-closure-tags x-reverse)))
			 (eq? (first (nonrecursive-closure-tags x-reverse))
			      'reverse))
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	    (let ((b (find-if
		      (lambda (b)
		       (vlad-equal?
			x-reverse
			(primitive-procedure-reverse (value-binding-value b))))
		      *value-bindings*)))
	     (if b
		 (value-binding-value b)
		 (let* ((e (reverse-transform-inverse
			    (new-lambda-expression
			     (nonrecursive-closure-variable x-reverse)
			     (nonrecursive-closure-body x-reverse))))
			(x (lambda-expression-variable e))
			(xs (free-variables e)))
		  (make-nonrecursive-closure
		   xs
		   (add/remove-slots
		    *j-inverse
		    (map lax-unreverseify
			 (nonrecursive-closure-variables x-reverse))
		    xs
		    (nonrecursive-closure-values x-reverse)
		    '())
		   x
		   (index
		    x xs (copy-propagate (lambda-expression-body e))))))))
	   ((recursive-closure? x-reverse)
	    (unless (and (not (null? (recursive-closure-tags x-reverse)))
			 (eq? (first (recursive-closure-tags x-reverse))
			      'reverse))
	     (run-time-error
	      "Attempt to take *j-inverse of a non-reverse value" x-reverse))
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
				(new-lambda-expression x e)))
			      (recursive-closure-argument-variables x-reverse)
			      (recursive-closure-bodies x-reverse))))
			(xs1 (map-vector
			      unreverseify
			      (recursive-closure-procedure-variables
			       x-reverse)))
			(xs (letrec-recursive-closure-variables
			     (vector->list xs1)
			     (map lambda-expression-variable es)
			     (map lambda-expression-body es))))
		  (make-recursive-closure
		   xs
		   (add/remove-slots
		    *j-inverse
		    (map lax-unreverseify
			 (recursive-closure-variables x-reverse))
		    xs
		    (recursive-closure-values x-reverse)
		    '())
		   xs1
		   (list->vector (map lambda-expression-variable es))
		   (list->vector
		    (map (lambda (e)
			  (index (lambda-expression-variable e)
				 (append (vector->list xs1) xs)
				 (copy-propagate (lambda-expression-body e))))
			 es))
		   (recursive-closure-index x-reverse))))))
	   ((bundle? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((reverse-tagged-value? x-reverse)
	    (reverse-tagged-value-primal x-reverse))
	   (else (fuck-up)))
	  x-reverse))
   (when *memoized?*
    (set! *reverse-cache* (cons reverse-cache-entry *reverse-cache*))))
  (reverse-cache-entry-primal reverse-cache-entry)))

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
  (else (fuck-up))))

(define (quotable? v)
 (cond ((and (not *unabbreviate-transformed?*) (vlad-forward? v)) #f)
       ((and (not *unabbreviate-transformed?*) (vlad-reverse? v)) #f)
       ((null? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((real? v) #t)
       ((vlad-pair? v '())
	(and (quotable? (vlad-car v '())) (quotable? (vlad-cdr v '()))))
       ((primitive-procedure? v) #f)
       ((nonrecursive-closure? v) #f)
       ((recursive-closure? v) #f)
       ((bundle? v) #f)
       ((reverse-tagged-value? v) #f)
       (else (fuck-up))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((and (not *unabbreviate-transformed?*) (vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  `(bundle ,(loop (primal v) quote?)
			   ,(loop (tangent v) quote?)))
		 (else `(forward ,(loop (primal v) quote?)
				 ,(loop (tangent v) quote?)))))
	  ((and (not *unabbreviate-transformed?*) (vlad-reverse? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  `(*j ,(loop (*j-inverse v) quote?)))
		 (else `(reverse ,(loop (*j-inverse v) quote?)))))
	  ((null? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((vlad-true? v) #t)
	  ((vlad-false? v) #f)
	  ((real? v) v)
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
	  ((bundle? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  `(bundle ,(loop (bundle-primal v) quote?)
			   ,(loop (bundle-tangent v) quote?)))
		 (else `(forward ,(loop (bundle-primal v) quote?)
				 ,(loop (bundle-tangent v) quote?)))))
	  ((reverse-tagged-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (fuck-up))
	     `(*j ,(loop (reverse-tagged-value-primal v) quote?)))
	    (else `(reverse ,(loop (reverse-tagged-value-primal v) quote?)))))
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

(define (tag-check? tags v)
 (or (null? tags)
     (case (first tags)
      ((forward) (and (vlad-forward? v) (tag-check? (rest tags) (primal v))))
      ((reverse)
       (and (vlad-reverse? v) (tag-check? (rest tags) (*j-inverse v))))
      (else (fuck-up)))))

;;; needs work: This evaluator is not tail recursive.

(define (call callee argument)
 (let ((callee (dereference callee)))
  (unless (or (and *church?*
		   (or (vlad-pair? callee '())
		       (vlad-true? callee)
		       (vlad-false? callee)))
	      (vlad-pair? callee '())	;needs work: church
	      (vlad-procedure? callee))
   (run-time-error "Target is not a procedure" callee))
  (when *anal?*
   (unless (tag-check?
	    (cond ((primitive-procedure? callee) '())
		  ((nonrecursive-closure? callee)
		   (nonrecursive-closure-tags callee))
		  ((recursive-closure? callee) (recursive-closure-tags callee))
		  (else (fuck-up)))
	    argument)
    (run-time-error "Argument has wrong type for target" callee argument)))
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
		     (nonrecursive-closure-values callee)))
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
		   (make-recursive-closure
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
   result)))

(define (evaluate e v vs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (cond ((variable-access-expression? e)
	(lookup (variable-access-expression-index e)))
       ((lambda-expression? e)
	(make-nonrecursive-closure
	 (free-variables e)
	 (map-vector lookup (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
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
	      (letrec-expression-bodies-free-variables e) vs xs0 xs1 es i))
	    (vector-length es)))
	  (map-vector lookup
		      (letrec-expression-body-free-variable-indices e)))))
       (else (fuck-up))))

;;; begin stuff that belongs to brownfis

;;; Flow Analysis

;;; b binding
;;; e expression
;;; p predicate or procedure
;;; u proto abstract value
;;; v abstract value
;;; x variable

;;; brownfis -- Should we consider introducing specific notation for
;;;             abstract-environment and -expression bindings?
;;; i.e.
;;; xb eXpression binding
;;; nb eNvironment binding
;;; b  value binding

;;; A novel issue with flow analysis for VLAD is that the AD functions create
;;; new expressions.

(define (recursive-closure-procedure-lambda-expressions v)
 (map-vector (lambda (x e) (new-lambda-expression x e))
	     (recursive-closure-argument-variables v)
	     (recursive-closure-bodies v)))

;;; Expression Alpha Equivalence
;;; This is only used to define value equivalence. alpha-match and
;;; abstract-recursive-closure-alpha-bindings are the only procedures used
;;; outside this section. The former is used for nonrecursive closures and the
;;; later is used for recursive closures.

(define (merge-binding b1 bs)
 (cond ((or (eq? bs #f)
	    (some (lambda (b)
		   (or (and (variable=? (alpha-binding-variable1 b)
					(alpha-binding-variable1 b1))
			    (not (variable=? (alpha-binding-variable2 b)
					     (alpha-binding-variable2 b1))))
		       (and (not (variable=? (alpha-binding-variable1 b)
					     (alpha-binding-variable1 b1)))
			    (variable=? (alpha-binding-variable2 b)
					(alpha-binding-variable2 b1)))))
		  bs))
	#f)
       ((some (lambda (b)
	       (and (variable=? (alpha-binding-variable1 b)
				(alpha-binding-variable1 b1))
		    (variable=? (alpha-binding-variable2 b)
				(alpha-binding-variable2 b1))))
	      bs)
	bs)
       (else (cons b1 bs))))

(define (merge-bindings bs1 bs2)
 (cond ((or (eq? bs1 #f) (eq? bs2 #f)) #f)
       ((null? bs1) bs2)
       (else (merge-bindings (rest bs1) (merge-binding (first bs1) bs2)))))

;;; brownfis -- added

(define (expression-eqv? e1 e2)
 (or (eq? e1 e2)
     (and (constant-expression? e1) (constant-expression? e2)
	  (eq? (constant-expression-value e1) (constant-expression-value e2)))
     (and (variable-access-expression? e1)(variable-access-expression? e2)
	  (variable=? (variable-access-expression-variable e1)
		      (variable-access-expression-variable e2)))
     (and (lambda-expression? e1) (lambda-expression? e2)
	  (variable=? (lambda-expression-variable e1)
		      (lambda-expression-variable e2))
	  (expression-eqv? (lambda-expression-body e1)
			   (lambda-expression-body e2)))
     (and (application? e1) (application? e2)
	  (expression-eqv? (application-callee e1) (application-callee e2))
	  (expression-eqv? (application-argument e1)(application-argument e2)))
     (and (letrec-expression? e1) (letrec-expression? e2)
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
			   (letrec-expression-body e2)))))

(define-structure expression-cache-entry expression result)

(define (compute-alpha-match e1 e2)
 (cond
  ((and (variable-access-expression? e1) (variable-access-expression? e2))
   (list (make-alpha-binding (variable-access-expression-variable e1)
			     (variable-access-expression-variable e2))))
  ((and (lambda-expression? e1) (lambda-expression? e2))
   (let ((bs (alpha-match-memoized (lambda-expression-body e1)
				   (lambda-expression-body e2)))
	 (b (make-alpha-binding (lambda-expression-variable e1)
				(lambda-expression-variable e2))))
    (if (or (eq? bs #f)
	    (some (lambda (b)
		   (or (and (variable=? (alpha-binding-variable1 b)
					(lambda-expression-variable e1))
			    (not
			     (variable=? (alpha-binding-variable2 b)
					 (lambda-expression-variable e2))))
		       (and (not (variable=? (alpha-binding-variable1 b)
					     (lambda-expression-variable e1)))
			    (variable=? (alpha-binding-variable2 b)
					(lambda-expression-variable e2)))))
		  bs))
	#f
	(remove-if (lambda (b)
		    (and (variable=? (alpha-binding-variable1 b)
				     (lambda-expression-variable e1))
			 (variable=? (alpha-binding-variable2 b)
				     (lambda-expression-variable e2))))
		   bs))))
  ((and (application? e1) (application? e2))
   (merge-bindings
    (alpha-match-memoized (application-callee e1)
			  (application-callee e2))
    (alpha-match-memoized (application-argument e1)
			  (application-argument e2))))
  ((and (letrec-expression? e1)
	(letrec-expression? e2)
	(= (length (letrec-expression-procedure-variables e1))
	   (length (letrec-expression-procedure-variables e2))))
   (let loop ((xs1 (letrec-expression-procedure-variables e1))
	      (xs2 (letrec-expression-procedure-variables e2))
	      (bs
	       (merge-bindings
		(reduce
		 merge-bindings
		 (map
		  (lambda (x1 x2 e1 e2)
		   (let ((bs (alpha-match-memoized e1 e2)))
		    (if (or (eq? bs #f)
			    (some (lambda (b)
				   (or
				    (and (variable=?
					  (alpha-binding-variable1 b) x1)
					 (not
					  (variable=?
					   (alpha-binding-variable2 b) x2)))
				    (and (not
					  (variable=?
					   (alpha-binding-variable1 b) x1))
					 (variable=?
					  (alpha-binding-variable2 b) x2))))
				  bs))
			#f
			(remove-if
			 (lambda (b)
			  (and (variable=? (alpha-binding-variable1 b) x1)
			       (variable=? (alpha-binding-variable2 b) x2)))
			 bs))))
		  (letrec-expression-argument-variables e1)
		  (letrec-expression-argument-variables e2)
		  (letrec-expression-bodies e1)
		  (letrec-expression-bodies e2))
		 '())
		(alpha-match-memoized (letrec-expression-body e1)
				      (letrec-expression-body e2)))))
    (cond ((null? xs1) bs)
	  ((or (eq? bs #f)
	       (some (lambda (b)
		      (or (and (variable=? (alpha-binding-variable1 b)
					   (first xs1))
			       (not (variable=? (alpha-binding-variable2 b)
						(first xs2))))
			  (and (not (variable=? (alpha-binding-variable1 b)
						(first xs1)))
			       (variable=? (alpha-binding-variable2 b)
					   (first xs2)))))
		     bs))
	   #f)
	  (else (loop
		 (rest xs1)
		 (rest xs2)
		 (remove-if
		  (lambda (b)
		   (and (variable=? (alpha-binding-variable1 b) (first xs1))
			(variable=? (alpha-binding-variable2 b) (first xs2))))
		  bs))))))
  (else #f)))

(define *alpha-match-cache-hits* 0)
(define *hits-constant* 0)
(define *hits-variable* 0)
(define *hits-lambda* 0)
(define *hits-application* 0)
(define *hits-letrec* 0)
(define *alpha-match-cache-misses* 0)
(define *misses-constant* 0)
(define *misses-variable* 0)
(define *misses-lambda* 0)
(define *misses-application* 0)
(define *misses-letrec* 0)

(define (update-hits! e)
 (set! *alpha-match-cache-hits* (+ *alpha-match-cache-hits* 1))
 (cond ((constant-expression? e) (set! *hits-constant* (+ *hits-constant* 1)))
       ((variable-access-expression? e)
	(set! *hits-variable* (+ *hits-variable* 1)))
       ((lambda-expression? e) (set! *hits-lambda* (+ *hits-lambda* 1)))
       ((application? e) (set! *hits-application* (+ *hits-application* 1)))
       ((letrec-expression? e) (set! *hits-letrec* (+ *hits-letrec* 1)))
       (else (panic "Invalid expression!"))))

(define (update-misses! e)
 (set! *alpha-match-cache-misses* (+ *alpha-match-cache-misses* 1))
 (cond ((constant-expression? e)
	(set! *misses-constant* (+ *misses-constant* 1)))
       ((variable-access-expression? e)
	(set! *misses-variable* (+ *misses-variable* 1)))
       ((lambda-expression? e) (set! *misses-lambda* (+ *misses-lambda* 1)))
       ((application? e)
	(set! *misses-application* (+ *misses-application* 1)))
       ((letrec-expression? e) (set! *misses-letrec* (+ *misses-letrec* 1)))
       (else (panic "Invalid expression!"))))

(define (reset-cache-performance)
 (set! *alpha-match-cache-hits* 0)
 (set! *hits-constant* 0)
 (set! *hits-variable* 0)
 (set! *hits-lambda* 0)
 (set! *hits-application* 0)
 (set! *hits-letrec* 0)
 (set! *alpha-match-cache-misses* 0)
 (set! *misses-constant* 0)
 (set! *misses-variable* 0)
 (set! *misses-lambda* 0)
 (set! *misses-application* 0)
 (set! *misses-letrec* 0))

(define (report-cache-performance)
 (let ((total-calls (+ *alpha-match-cache-hits* *alpha-match-cache-misses*))
       (total-constant (+ *hits-constant* *misses-constant*))
       (total-variable (+ *hits-variable* *misses-variable*))
       (total-lambda (+ *hits-lambda* *misses-lambda*))
       (total-application (+ *hits-application* *misses-application*))
       (total-letrec (+ *hits-letrec* *misses-letrec*))
       (div (lambda (x y) (if (zero? y) #f (/ x y)))))
  (format #t "Total alpha-match calls: ~s~%" total-calls)
  (format #t "Total alpha-match hit/miss     = ~s/~s (~s/~s)~%"
	  *alpha-match-cache-hits* *alpha-match-cache-misses*
	  (div *alpha-match-cache-hits* total-calls)
	  (div *alpha-match-cache-misses* total-calls))
  (format #t "  constant-expression hit/miss = ~s/~s (~s/~s)~%"
	  *hits-constant* *misses-constant*
	  (div *hits-constant* total-constant)
	  (div *misses-constant* total-constant))
  (format #t "  variable-access   hit/miss   = ~s/~s (~s/~s)~%"
	  *hits-variable* *misses-variable*
	  (div *hits-variable* total-variable)
	  (div *misses-variable* total-variable))
  (format #t "  lambda-expression hit/miss   = ~s/~s (~s/~s)~%"
	  *hits-lambda* *misses-lambda*
	  (div *hits-lambda* total-lambda) (div *misses-lambda* total-lambda))
  (format #t "  application hit/miss         = ~s/~s (~s/~s)~%"
	  *hits-application* *misses-application*
	  (div *hits-application* total-application)
	  (div *misses-application* total-application))
  (format #t "  letrec-expression hit/miss   = ~s/~s (~s/~s)~%"
	  *hits-letrec* *misses-letrec*
	  (div *hits-letrec* total-letrec)
	  (div *misses-letrec* total-letrec))))

(define alpha-match-memoized-old
 (let ((cache '()))
  (define (cache-lookup e1 e2)
   (let ((entry-e1
	  (find-if
	   (lambda (entry)
	    (expression-eqv? (expression-cache-entry-expression entry) e1))
	   cache)))
    (if (not (eq? #f entry-e1))
	(let ((entry-e2
	       (find-if
		(lambda (entry)
		 (expression-eqv?
		  (expression-cache-entry-expression entry) e2))
		(expression-cache-entry-result entry-e1))))
	 (if (not (eq? #f entry-e2))
	     entry-e2
	     #f))
	#f)))
  (define (cache-result! e1 e2 result)
   (let ((entry-e1
	  (find-if
	   (lambda (entry)
	    (expression-eqv? (expression-cache-entry-expression entry) e1))
	   cache)))
    (if (not (eq? #f entry-e1))
	(let ((entry-e2
	       (find-if
		(lambda (entry)
		 (expression-eqv?
		  (expression-cache-entry-expression entry) e2))
		(expression-cache-entry-result entry-e1))))
	 (if (not (eq? #f entry-e2))
	     (set-expression-cache-entry-result! entry-e2 result)
	     (set-expression-cache-entry-result!
	      entry-e1
	      (cons (make-expression-cache-entry e2 result)
		    (expression-cache-entry-result entry-e1)))))
	(set! cache
	      (cons
	       (make-expression-cache-entry
		e1 (list (make-expression-cache-entry e2 result)))
	       cache)))))
  (lambda (e1 e2)
   (let ((entry (cache-lookup e1 e2)))
    (if (not (eq? #f entry))
	(begin
	 (update-hits! e1)
	 (expression-cache-entry-result entry))
	(let ((result (compute-alpha-match e1 e2)))
	 (update-misses! e1)
	 (cache-result! e1 e2 result)
	 (cache-result! e2 e1 result)
	 result))))))

(define (expression-type-index e)
 (cond ((constant-expression? e) 0)
       ((variable-access-expression? e) 1)
       ((lambda-expression? e) 2)
       ((application? e) 3)
       ((letrec-expression? e) 4)
       (else (panic "Invalid expression!"))))

(define (swap-alpha-bindings bs)
 (if (eq? #f bs)
     #f
     (map (lambda (b) (make-alpha-binding (alpha-binding-variable2 b)
					  (alpha-binding-variable1 b)))
	  bs)))

(define alpha-match-memoized
 (let ((cache (make-vector 5 '())))
  ;; an implicit assumption is that e1 and e2 must be of same type
  (define (cache-lookup e1 e2)
   (collect-time-in-buckets
    'alpha-match-lookup
    (lambda ()
     (let* ((type-e1 (expression-type-index e1))
	    (entry-e1
	     (find-if
	      (lambda (entry)
	       (expression-eqv? (expression-cache-entry-expression entry) e1))
	      (vector-ref cache type-e1))))
      (if (not (eq? #f entry-e1))
	  (let ((entry-e2
		 (find-if
		  (lambda (entry)
		   (expression-eqv?
		    (expression-cache-entry-expression entry) e2))
		  (expression-cache-entry-result entry-e1))))
	   (if (not (eq? #f entry-e2))
	       entry-e2
	       #f))
	  #f)))))
  (define (cache-result! e1 e2 result)
   (let* ((type-e1 (expression-type-index e1))
	  (entry-e1
	   (find-if
	    (lambda (entry)
	     (expression-eqv? (expression-cache-entry-expression entry) e1))
	    (vector-ref cache type-e1))))
    (if (not (eq? #f entry-e1))
	(let ((entry-e2
	       (find-if
		(lambda (entry)
		 (expression-eqv?
		  (expression-cache-entry-expression entry) e2))
		(expression-cache-entry-result entry-e1))))
	 (if (not (eq? #f entry-e2))
	     (set-expression-cache-entry-result! entry-e2 result)
	     (set-expression-cache-entry-result!
	      entry-e1
	      (cons (make-expression-cache-entry e2 result)
		    (expression-cache-entry-result entry-e1)))))
	(vector-set! cache
		     type-e1
		     (cons
		      (make-expression-cache-entry
		       e1 (list (make-expression-cache-entry e2 result)))
		      (vector-ref cache type-e1))))))
  (lambda (e1 e2)
   (if (not (= (expression-type-index e1) (expression-type-index e2)))
       #f
       (let ((entry (cache-lookup e1 e2)))
	(if (not (eq? #f entry))
	    (begin
	     (update-hits! e1)
	     (expression-cache-entry-result entry))
	    (let ((result (compute-alpha-match e1 e2)))
	     (update-misses! e1)
	     (cache-result! e1 e2 result)
	     (cache-result! e2 e1 (swap-alpha-bindings result))
	     result)))))))

;;; brownfis -- end added

(define (alpha-match-not-memoized e1 e2)
 (cond
  ((and (variable-access-expression? e1) (variable-access-expression? e2))
   (list (make-alpha-binding (variable-access-expression-variable e1)
			     (variable-access-expression-variable e2))))
  ((and (lambda-expression? e1) (lambda-expression? e2))
   (let ((bs (alpha-match-not-memoized (lambda-expression-body e1)
				       (lambda-expression-body e2)))
	 (b (make-alpha-binding (lambda-expression-variable e1)
				(lambda-expression-variable e2))))
    (if (or (eq? bs #f)
	    (some (lambda (b)
		   (or (and (variable=? (alpha-binding-variable1 b)
					(lambda-expression-variable e1))
			    (not (variable=? (alpha-binding-variable2 b)
					     (lambda-expression-variable e2))))
		       (and (not (variable=? (alpha-binding-variable1 b)
					     (lambda-expression-variable e1)))
			    (variable=? (alpha-binding-variable2 b)
					(lambda-expression-variable e2)))))
		  bs))
	#f
	(remove-if (lambda (b)
		    (and (variable=? (alpha-binding-variable1 b)
				     (lambda-expression-variable e1))
			 (variable=? (alpha-binding-variable2 b)
				     (lambda-expression-variable e2))))
		   bs))))
  ((and (application? e1) (application? e2))
   (merge-bindings
    (alpha-match-not-memoized (application-callee e1)
			      (application-callee e2))
    (alpha-match-not-memoized (application-argument e1)
			      (application-argument e2))))
  ((and (letrec-expression? e1)
	(letrec-expression? e2)
	(= (length (letrec-expression-procedure-variables e1))
	   (length (letrec-expression-procedure-variables e2))))
   (let loop ((xs1 (letrec-expression-procedure-variables e1))
	      (xs2 (letrec-expression-procedure-variables e2))
	      (bs
	       (merge-bindings
		(reduce
		 merge-bindings
		 (map
		  (lambda (x1 x2 e1 e2)
		   (let ((bs (alpha-match-not-memoized e1 e2)))
		    (if (or (eq? bs #f)
			    (some (lambda (b)
				   (or (and (variable=?
					     (alpha-binding-variable1 b) x1)
					    (not
					     (variable=?
					      (alpha-binding-variable2 b) x2)))
				       (and (not
					     (variable=?
					      (alpha-binding-variable1 b) x1))
					    (variable=?
					     (alpha-binding-variable2 b) x2))))
				  bs))
			#f
			(remove-if
			 (lambda (b)
			  (and (variable=? (alpha-binding-variable1 b) x1)
			       (variable=? (alpha-binding-variable2 b) x2)))
			 bs))))
		  (letrec-expression-argument-variables e1)
		  (letrec-expression-argument-variables e2)
		  (letrec-expression-bodies e1)
		  (letrec-expression-bodies e2))
		 '())
		(alpha-match-not-memoized (letrec-expression-body e1)
					  (letrec-expression-body e2)))))
    (cond ((null? xs1) bs)
	  ((or (eq? bs #f)
	       (some (lambda (b)
		      (or (and (variable=? (alpha-binding-variable1 b)
					   (first xs1))
			       (not (variable=? (alpha-binding-variable2 b)
						(first xs2))))
			  (and (not (variable=? (alpha-binding-variable1 b)
						(first xs1)))
			       (variable=? (alpha-binding-variable2 b)
					   (first xs2)))))
		     bs))
	   #f)
	  (else (loop
		 (rest xs1)
		 (rest xs2)
		 (remove-if
		  (lambda (b)
		   (and (variable=? (alpha-binding-variable1 b) (first xs1))
			(variable=? (alpha-binding-variable2 b) (first xs2))))
		  bs))))))
  (else #f)))

(define (alpha-match e1 e2)
 (collect-time-in-buckets
  'alpha-match
  (lambda ()
   (if *memoize-alpha-matching?*
       (alpha-match-memoized e1 e2)
       (alpha-match-not-memoized e1 e2)))))

(define (nonrecursive-closure-alpha-bindings-not-memoized u1 u2)
 (alpha-match (new-lambda-expression (nonrecursive-closure-variable u1)
				     (nonrecursive-closure-body u1))
	      (new-lambda-expression (nonrecursive-closure-variable u2)
				     (nonrecursive-closure-body u2))))

(define nonrecursive-closure-alpha-bindings-memoized
 ;; cache: expression -> variable -> expression -> variable -> bindings
 (let ((cache '()))
  (define (lookup-in-cache x1 e1 x2 e2)
   ;; match e1
   (let ((result (find-if (lambda (p) (eq? (car p) e1)) cache)))
    (if (not (eq? #f result))
	;; match x1
	(let ((result (find-if (lambda (p) (eq? (car p) x1)) (cdr result))))
	 (if (not (eq? #f result))
	     ;; match e2
	     (let ((result (find-if (lambda (p) (eq? (car p) e2))
				    (cdr result))))
	      (if (not (eq? #f result))
		  ;; match x2
		  (let ((result (find-if (lambda (p) (eq? (car p) x2))
					 (cdr result))))
		   (if (not (eq? #f result))
		       result
		       #f))
		  #f))
	     #f))
	#f)))
  (define (create-cache-entry result . &xs)
   (if (null? &xs)
       result
       (list (cons (first &xs) (apply create-cache-entry result (rest &xs))))))
  (define (store-in-cache! x1 e1 x2 e2 result)
   (let ((result-e1 (find-if (lambda (p) (eq? (car p) e1)) cache)))
    (if (not (eq? #f result-e1))
	(let ((result-x1 (find-if (lambda (p) (eq? (car p) x1))
				  (cdr result-e1))))
	 (if (not (eq? #f result-x1))
	     (let ((result-e2 (find-if (lambda (p) (eq? (car p) e2))
				       (cdr result-x1))))
	      (if (not (eq? #f result-e2))
		  (let ((result-x2 (find-if (lambda (p) (eq? (car p) x2))
					    (cdr result-e2))))
		   (if (not (eq? #f result-x2))
		       (set-cdr! result-x2 result)
		       (set-cdr! result-e2
				 (append (create-cache-entry result x2)
					 (cdr result-e2)))))
		  (set-cdr! result-x1
			    (append (create-cache-entry result e2 x2)
				    (cdr result-x1)))))
	     (set-cdr! result-e1
		       (append (create-cache-entry result x1 e2 x2)
			       (cdr result-e1)))))
	(set! cache (append (create-cache-entry result e1 x1 e2 x2) cache)))))
  (lambda (u1 u2)
   (let* ((x1 (nonrecursive-closure-variable u1))
	  (e1 (nonrecursive-closure-body u1))
	  (x2 (nonrecursive-closure-variable u2))
	  (e2 (nonrecursive-closure-body u2))
	  (result (lookup-in-cache x1 e1 x2 e2)))
    (if (eq? #f result)
	(let ((result
	       (alpha-match
		(new-lambda-expression (nonrecursive-closure-variable u1)
				       (nonrecursive-closure-body u1))
		(new-lambda-expression (nonrecursive-closure-variable u2)
				       (nonrecursive-closure-body u2)))))
	 (store-in-cache! x1 e1 x2 e2 result)
	 (store-in-cache! x2 e2 x1 e1 (swap-alpha-bindings result))
	 result)
	(cdr result))))))

(define (nonrecursive-closure-alpha-bindings u1 u2)
 (collect-time-in-buckets
  'nonrecursive-closure-alpha-bindings
  (lambda ()
   (if *memoize-nonrecursive-alpha-matching?*
       (nonrecursive-closure-alpha-bindings-memoized u1 u2)
       (nonrecursive-closure-alpha-bindings-not-memoized u1 u2)))))

(define (recursive-closure-alpha-bindings u1 u2)
 (define (make-letrec-expression-from-recursive-closure u)
  (new-letrec-expression
   (vector->list (recursive-closure-procedure-variables u))
   (vector->list (recursive-closure-argument-variables u))
   (vector->list (recursive-closure-bodies u))
   (new-variable-access-expression
    (vector-ref (recursive-closure-procedure-variables u)
		(recursive-closure-index u)))))
 (collect-time-in-buckets
  'recursive-closure-alpha-bindings
  (lambda ()
   (alpha-match
    (make-letrec-expression-from-recursive-closure u1)
    (make-letrec-expression-from-recursive-closure u2)))))

(define (recursive-closure-alpha-bindings-memoized u1 u2)
 (define (make-letrec-expression-from-recursive-closure u)
  (new-letrec-expression
   (vector->list (recursive-closure-procedure-variables u))
   (vector->list (recursive-closure-argument-variables u))
   (vector->list (recursive-closure-bodies u))
   (new-variable-access-expression
    (vector-ref (recursive-closure-procedure-variables u)
		(recursive-closure-index u)))))
 (collect-time-in-buckets
  'recursive-closure-alpha-bindings
  (lambda ()
   (alpha-match
    (make-letrec-expression-from-recursive-closure u1)
    (make-letrec-expression-from-recursive-closure u2)))))

;;; Abstract-Analysis Access

(define (expression-abstract-flow e bs)
 (abstract-expression-binding-abstract-flow
  ;; needs work: Can make abstract-analysis access O(1) instead of O(n).
  ;; needs work: Do we need identity or alpha equivalence here?
  (let ((aeb (find-if
	      (lambda (b) (eq? e (abstract-expression-binding-expression b)))
	      bs)))
   ;; debugging
   (when (not (abstract-expression-binding? aeb))
    (format #t "No matching abstract flow!~%")
    (pp (abstract->concrete e)) (newline)
    (pp (externalize-abstract-analysis bs)) (newline))
   aeb)))

;;; Cyclicization of (Proto) Abstract Values

(define (cyclicize-proto-abstract-value-internal u vs)
 (cond ((null? u) u)
       ((eq? u #t) u)
       ((eq? u #f) u)
       ((real? u) u)
       ((eq? u 'real) u)
       ((primitive-procedure? u) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 (map-vector (lambda (v) (cyclicize-abstract-value-internal v vs))
		     (nonrecursive-closure-values u))
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 (map-vector (lambda (v) (cyclicize-abstract-value-internal v vs))
		     (recursive-closure-values u))
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (fuck-up))))

(define (cyclicize-abstract-value-internal v vs)
 (cond ((up? v) (list-ref vs (up-index v)))
       ((null? v) v)
       (else (let ((v1 (cons #f #f)))
	      (let loop ((us v) (v2 v1))
	       (set-car! v2
			 (cyclicize-proto-abstract-value-internal
			  (first us) (cons v1 vs)))
	       (cond ((null? (rest us)) (set-cdr! v2 '()) v1)
		     (else (set-cdr! v2 (cons #f #f))
			   (loop (rest us) (cdr v2)))))))))

(define (cyclicize-proto-abstract-value u)
 (cyclicize-proto-abstract-value-internal u '()))

(define (cyclicize-abstract-value v) (cyclicize-abstract-value-internal v '()))

;;; Uncyclicization of (Proto) Abstact Values

(define (uncyclicize-proto-abstract-value-internal u vs)
 (cond ((null? u) u)
       ((eq? u #t) u)
       ((eq? u #f) u)
       ((real? u) u)
       ((eq? u 'real) u)
       ((primitive-procedure? u) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 (map-vector (lambda (v) (uncyclicize-abstract-value-internal v vs))
		     (nonrecursive-closure-values u))
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 (map-vector (lambda (v) (uncyclicize-abstract-value-internal v vs))
		     (recursive-closure-values u))
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (fuck-up))))

(define (uncyclicize-abstract-value-internal v vs)
 (cond ((up? v) v)
       ((memq v vs) (make-up (positionq v vs)))
       (else (map (lambda (u)
		   (uncyclicize-proto-abstract-value-internal u (cons v vs)))
		  v))))

(define (uncyclicize-proto-abstract-value u)
 (uncyclicize-proto-abstract-value-internal u '()))

(define (uncyclicize-abstract-value v)
 (uncyclicize-abstract-value-internal v '()))

;;; (Proto) Abstract-Value Subset, Equivalence, and Union

(define (every-c c f . ls)
 (if (null? (first ls))
     c
     (let ((c (apply f c (map first ls))))
      (if (eq? c #f) #f (apply every-c c f (map rest ls))))))

(define (some-c c f . ls)
 (if (null? (first ls))
     #f
     (let ((c-prime (apply f c (map first ls))))
      (if (eq? c-prime #f) (apply some-c c f (map rest ls)) c-prime))))

(define (remove-if-not-c c p l)
 (if (null? l)
     (list c '())
     (let ((result (p c (first l))))
      (if (eq? result #f)
	  (remove-if-not-c c p (rest l))
	  (let ((result (remove-if-not-c result p (rest l))))
	   (list (first result) (cons (first l) (second result))))))))

(define (abstract-value-subset?-new v1 v2)
 (set! *num-calls-abstract-value-subset*
       (+ *num-calls-abstract-value-subset* 1))
 (when #f (format #t "(~s,~s)~%" (externalize-abstract-value v1)
		  (externalize-abstract-value v2)))
 (collect-total-time-spent-in
  (lambda (t) (set! *time-in-subset* (+ *time-in-subset* t)))
  (lambda ()
   (not
    (eq?
     #f
     (let loop? ((v1 v1) (v2 v2) (cs '()))
      (set! *num-calls-abstract-value-subset-loop?*
	    (+ *num-calls-abstract-value-subset-loop?* 1))
      (when (and *debug?* (> *debug-level* 4))
       (format #t "(subset?~%")
       (pp (externalize-abstract-value v1)) (newline)
       (pp (externalize-abstract-value v2))
       (format #t ")~%"))
      (cond
       ((null? v1) cs)
       ((null? v2) #f)
       ((some (lambda (c)
	       (and (set-equalp? eq? v1 (car c)) (set-equalp? eq? v2 (cdr c))))
	      cs)
	cs)
       (else
	(let ((cs (cons (cons v1 v2) cs)))
	 (every-c
	  cs
	  (lambda (cs u1)
	   (cond ((null? u1)
		  (some-c cs (lambda (cs u2) (if (null? u2) cs #f)) v2))
		 ((eq? u1 #t)
		  (some-c cs (lambda (cs u2) (if (eq? u2 #t) cs #f)) v2))
		 ((eq? u1 #f)
		  (some-c cs (lambda (cs u2) (if (eq? u2 #f) cs #f)) v2))
		 ((real? u1)
		  (some-c
		   cs
		   (lambda (cs u2)
		    (if (or (and (real? u2) (= u1 u2)) (eq? u2 'real)) cs #f))
		   v2))
		 ((eq? u1 'real)
		  (some-c cs (lambda (cs u2) (if (eq? u2 'real) cs #f)) v2))
		 ((primitive-procedure? u1)
		  (some-c
		   cs
		   (lambda (cs u2)
		    (if (and (primitive-procedure? u2) (eq? u1 u2)) cs #f))
		   v2))
		 ((nonrecursive-closure? u1)
		  (let ((vs1 (nonrecursive-closure-values u1)))
		   (if
		    (= (vector-length vs1) 0)
		    (some-c
		     cs
		     (lambda (cs u2)
		      (if (and (nonrecursive-closure? u2)
			       (= (vector-length
				   (nonrecursive-closure-values u2))
				  0)
			       (nonrecursive-closure-match? u1 u2))
			  cs
			  #f))
		     v2)
		    (some-c
		     cs
		     (lambda (cs i)
		      (let* ((cs-and-us
			      (remove-if-not-c
			       cs
			       (lambda (cs u2)
				(if (and (nonrecursive-closure? u2)
					 (nonrecursive-closure-match? u1 u2))
				    (let
				      ((vs2-matching
					(nonrecursive-closure-values-matching
					 u1 u2)))
				     (every-c
				      cs
				      (lambda (cs j)
				       (if (= i j)
					   cs
					   (loop? (vector-ref vs1 j)
						  (vector-ref vs2-matching j)
						  cs)))
				      (enumerate (vector-length vs1))))
				    #f))
			       v2))
			     (cs (first cs-and-us))
			     (us-matching-all-but-u1_i (second cs-and-us))
			     (v1-new (vector-ref vs1 i))
			     (v2-new
			      (reduce
			       abstract-value-union
			       (map
				(lambda (u)
				 (vector-ref
				  (nonrecursive-closure-values-matching u1 u)
				  i))
				us-matching-all-but-u1_i)
			       (empty-abstract-value))))
		       (loop? v1-new v2-new cs)))
		     (enumerate (vector-length vs1))))))
		 ;; needs work: update this with stuff from
		 ;;             nonrecursive-closure
		 ((recursive-closure? u1)
		  (let ((vs1 (recursive-closure-values u1)))
		   (if
		    (= (vector-length vs1) 0)
		    (some-c
		     cs
		     (lambda (cs u2)
		      (if (and (recursive-closure? u2)
			       (= (vector-length (recursive-closure-values u2))
				  0)
			       (recursive-closure-match? u1 u2))
			  cs
			  #f))
		     v2)
		    (some-c
		     cs
		     (lambda (cs i)
		      (let* ((cs-and-us
			      (remove-if-not-c
			       cs
			       (lambda (cs u2)
				(if (and (recursive-closure? u2)
					 (recursive-closure-match? u1 u2))
				    (let ((vs2-matching
					   (recursive-closure-values-matching
					    u1 u2)))
				     (every-c
				      cs
				      (lambda (cs j)
				       (if (= i j)
					   cs
					   (loop? (vector-ref vs1 j)
						  (vector-ref vs2-matching j)
						  cs)))
				      (enumerate (vector-length vs1))))
				    #f))
			       v2))
			     (cs (first cs-and-us))
			     (us-matching-all-but-u1_i (second cs-and-us)))
		       (loop? (vector-ref vs1 i)
			      (reduce
			       abstract-value-union
			       (map
				(lambda (u)
				 (vector-ref
				  (recursive-closure-values-matching u1 u)
				  i))
				us-matching-all-but-u1_i)
			       (empty-abstract-value))
			      cs)))
		     (enumerate (vector-length vs1))))))
		 ((bundle? u1)
		  (panic (string-append "abstract-value-subset? not defined "
					" (yet) for bundles!")))
		 ((reverse-tagged-value? u1)
		  (panic (string-append "abstract-value-subset? not defined "
					" (yet) for reverse-tagged-values!")))
		 (else #f)))
	  v1))))))))))

(define (abstract-value-subset?-old v1 v2)
 (set! *num-calls-abstract-value-subset*
       (+ *num-calls-abstract-value-subset* 1))
 (when (and *debug?* (> *debug-level* 4))
  (format #t "subset-top!~%"))
 (collect-time-in-buckets
  'abstract-value-subset?
  (lambda ()
   (let loop? ((v1 v1) (v2 v2) (cs '()))
    (set! *num-calls-abstract-value-subset-loop?*
	  (+ *num-calls-abstract-value-subset-loop?* 1))
    (when (and *debug?* (> *debug-level* 4))
     (format #t "(subset?~%")
     (pp (externalize-abstract-value v1)) (newline)
     (pp (externalize-abstract-value v2))
     (format #t ")~%"))
    (cond
     ((null? v1) #t)
     ((null? v2) #f)
     ((some (lambda (c)
	     (and (set-equalp? eq? v1 (car c)) (set-equalp? eq? v2 (cdr c))))
	    cs)
      #t)
     (else
      (let ((cs (cons (cons v1 v2) cs)))
       (every
	(lambda (u1)
	 (cond ((null? u1) (some null? v2))
	       ((eq? u1 #t) (some (lambda (u2) (eq? u2 #t)) v2))
	       ((eq? u1 #f) (some (lambda (u2) (eq? u2 #f)) v2))
	       ((real? u1)
		(some (lambda (u2)
		       (or (and (real? u2) (= u1 u2)) (eq? u2 'real)))
		      v2))
	       ((eq? u1 'real) (some (lambda (u2) (eq? u2 'real)) v2))
	       ((primitive-procedure? u1)
		(some (lambda (u2) (and (primitive-procedure? u2) (eq? u1 u2)))
		      v2))
	       ((nonrecursive-closure? u1)
		(let ((vs1 (nonrecursive-closure-values u1)))
		 (if
		  (= (vector-length vs1) 0)
		  (some
		   (lambda (u2)
		    (and (nonrecursive-closure? u2)
			 (= (vector-length (nonrecursive-closure-values u2)) 0)
			 (nonrecursive-closure-match? u1 u2)))
		   v2)
		  (some-n
		   (lambda (i)
		    (let* ((us-matching-all-but-u1_i
			    ;; to-do: instrument
			    (collect-time-in-buckets
			     'subset?-matching-us
			     (lambda ()
			      (remove-if-not
			       (lambda (u2)
				(if (and (nonrecursive-closure? u2)
					 (nonrecursive-closure-match? u1 u2))
				    (let
				      ((vs2-matching
					(nonrecursive-closure-values-matching
					 u1 u2)))
				     (every-n
				      (lambda (j)
				       (if (= i j)
					   #t
					   (loop?
					    (vector-ref vs1 j)
					    (vector-ref vs2-matching j)
					    cs)))
				      (vector-length vs1)))
				    #f))
			       v2))))
			   (v1-new (vector-ref vs1 i))
			   (v2-new
			    (reduce
			     abstract-value-union
			     (map
			      (lambda (u)
			       (vector-ref
				(nonrecursive-closure-values-matching u1 u)
				i))
			      us-matching-all-but-u1_i)
			     (empty-abstract-value))))
		     (loop? v1-new v2-new cs)))
		   (vector-length vs1)))))
	       ;; needs work: update this with stuff from nonrecursive-closure
	       ((recursive-closure? u1)
		(let ((vs1 (recursive-closure-values u1)))
		 (if
		  (= (vector-length vs1) 0)
		  (some
		   (lambda (u2)
		    (and (recursive-closure? u2)
			 (= (vector-length (recursive-closure-values u2)) 0)
			 (recursive-closure-match? u1 u2)))

		   v2)
		  (some-n
		   (lambda (i)
		    (let ((us-matching-all-but-u1_i
			   (remove-if-not
			    (lambda (u2)
			     (if (and (recursive-closure? u2)
				      (recursive-closure-match? u1 u2))
				 (let ((vs2-matching
					(recursive-closure-values-matching
					 u1 u2)))
				  (every-n
				   (lambda (j)
				    (if (= i j)
					#t
					(loop?
					 (vector-ref vs1 j)
					 (vector-ref vs2-matching j)
					 cs)))
				   (vector-length vs1)))
				 #f))
			    v2)))
		     (loop? (vector-ref vs1 i)
			    (reduce
			     abstract-value-union
			     (map
			      (lambda (u)
			       (vector-ref
				(recursive-closure-values-matching u1 u)
				i))
			      us-matching-all-but-u1_i)
			     (empty-abstract-value))
			    cs)))
		   (vector-length vs1)))))
	       ((bundle? u1)
		(panic (string-append "abstract-value-subset? not defined "
				      " (yet) for bundles!")))
	       ((reverse-tagged-value? u1)
		(panic (string-append "abstract-value-subset? not defined "
				      " (yet) for reverse-tagged-values!")))
	       (else #f)))
	v1))))))))

(define (abstract-value-subset? v1 v2)
 (if *new-subset*
     (abstract-value-subset?-new v1 v2)
     (let ((result (abstract-value-subset?-old v1 v2)))
      (when *debug?* (format #t ")~%"))
      result)))

(define (proto-abstract-value-subset? u1 u2)
 (abstract-value-subset? (list u1) (list u2)))

(define (proto-abstract-value-superset? u1 u2)
 (proto-abstract-value-subset? u2 u1))

(define (proto-abstract-value-in-abstract-value? u v)
 (abstract-value-subset? (list u) v))

(define (abstract-value-proper-subset? v1 v2)
 (and (abstract-value-subset? v1 v2) (not (abstract-value-subset? v2 v1))))

(define (proto-abstract-value=? u1 u2)
 (and (proto-abstract-value-subset? u1 u2)
      (proto-abstract-value-subset? u2 u1)))

(define (abstract-value=? v1 v2)
 (and (abstract-value-subset? v1 v2) (abstract-value-subset? v2 v1)))

(define (empty-abstract-value) '())

;;; Abstract Value Union

(define (reorder-environment-to-match bs xs1 xs2 vs2)
 (list->vector
  (map (lambda (x1)
	(vector-ref
	 vs2 (positionq
	      (alpha-binding-variable2
	       (find-if (lambda (b) (eq? x1 (alpha-binding-variable1 b))) bs))
	      xs2)))
       xs1)))

(define (nonrecursive-closure-match? u1 u2)
 (if *use-alpha-equivalence?*
     (not (eq? (nonrecursive-closure-alpha-bindings u1 u2) #f))
     (and (variable=? (nonrecursive-closure-variable u1)
		      (nonrecursive-closure-variable u2))
	  ; 	  (eq? (nonrecursive-closure-body u1)
	  ; 	       (nonrecursive-closure-body u2)))))
	  (expression-eqv? (nonrecursive-closure-body u1)
			   (nonrecursive-closure-body u2)))))

(define (nonrecursive-closure-values-matching u1 u2)
 (if *use-alpha-equivalence?*
     (reorder-environment-to-match (nonrecursive-closure-alpha-bindings u1 u2)
				   (nonrecursive-closure-variables u1)
				   (nonrecursive-closure-variables u2)
				   (nonrecursive-closure-values u2))
     (nonrecursive-closure-values u2)))

(define (recursive-closure-match? u1 u2)
 (if *use-alpha-equivalence?*
     (and (= (recursive-closure-index u1) (recursive-closure-index u2))
	  (not (eq? (recursive-closure-alpha-bindings u1 u2) #f)))
     (and (= (recursive-closure-index u1) (recursive-closure-index u2))
	  (every-vector eq?
			(recursive-closure-argument-variables u1)
			(recursive-closure-argument-variables u2))
	  (every-vector eq?
			(recursive-closure-procedure-variables u1)
			(recursive-closure-procedure-variables u2))
	  ; 	  (every-vector eq?
	  ; 			(recursive-closure-bodies u1)
	  ; 			(recursive-closure-bodies u2)))))
	  (every-vector expression-eqv?
			(recursive-closure-bodies u1)
			(recursive-closure-bodies u2)))))

(define (recursive-closure-values-matching u1 u2)
 (if *use-alpha-equivalence?*
     (reorder-environment-to-match (recursive-closure-alpha-bindings u1 u2)
				   (recursive-closure-variables u1)
				   (recursive-closure-variables u2)
				   (recursive-closure-values u2))
     (recursive-closure-values u2)))

;; needs work: to support both alpha/eq? equivalence--now supports alpha only
(define (naive-nonrecursive-closure-coalescing-strategy us)
 (let ((u1 (first us))
       (u2 (second us)))
  (cons (make-nonrecursive-closure
	 (nonrecursive-closure-variables u1)
	 (abstract-environment-union
	  (nonrecursive-closure-values u1)
	  (nonrecursive-closure-values-matching u1 u2))
	 (nonrecursive-closure-variable u1)
	 (nonrecursive-closure-body u1))
	(rest (rest us)))))

;; needs work: to support both alpha/eq? equivalence--now supports alpha only
(define (naive-recursive-closure-coalescing-strategy us)
 (let ((u1 (first us))
       (u2 (second us)))
  (cons (make-recursive-closure
	 (recursive-closure-variables u1)
	 (abstract-environment-union
	  (recursive-closure-values u1)
	  (recursive-closure-values-matching u1 u2))
	 (recursive-closure-procedure-variables u1)
	 (recursive-closure-argument-variables u1)
	 (recursive-closure-bodies u1)
	 (recursive-closure-index u1))
	(rest (rest us)))))

;;; k:  maximum number of matching proto-abstract values we wish to have in us.
;;; us: a list of matching proto-abstract values
;;; coalesce-once: a procedure taking a list of proto-abstract values and
;;;                returning a list with strictly less proto-abstract values
;;;                and a potentially wider extension.
;;;
;;; Note that the concept of "matching" proto-abstract values depends on what
;;; sort of values are being considered:
;;;  - all real values match
;;;  - nonrecursive closures match when nonrecursive-closure-match? is true
;;;  - recursive closures match when recursive-closure-match? is true
;;; Matching isn't enforced in this procedure; rather, it is expected that the
;;; caller provide a list (us) of matching proto-abstract values and that the
;;; caller also provide a function (coalesce-once) which returns only lists
;;; of matching proto-abstract values.
(define (limit-to-k-matching-proto-abstract-values k us coalesce-once)
 (if (<= (length us) k)
     us
     (limit-to-k-matching-proto-abstract-values
      k (coalesce-once us) coalesce-once)))

;;; Depth limits

(define (all-paths-from-abstract-value-internal v vs)
 (if (memq v vs)
     '()
     (reduce append
	     (all-values
	      (map
	       (lambda (l) (cons v l))
	       (all-paths-from-proto-abstract-value-internal
		(a-member-of v) (cons v vs))))
	     '())))

(define (all-paths-from-abstract-value v)
 (all-paths-from-abstract-value-internal v '()))

(define (all-paths-from-proto-abstract-value-internal u vs)
 ;; {non,}recursive-closures are the only branching nonterminal
 ;; proto-abstract values.
 (cond ((nonrecursive-closure? u)
	(if (= (vector-length (nonrecursive-closure-values u)) 0)
	    (list (list u))
	    (reduce
	     append
	     (all-values
	      (map
	       (lambda (l) (cons u l))
	       (all-paths-from-abstract-value-internal
		(a-member-of (vector->list (nonrecursive-closure-values u)))
		vs)))
	     '())))
       ((recursive-closure? u)
	(if (= (vector-length (recursive-closure-values u)) 0)
	    (list (list u))
	    (reduce
	     append
	     (all-values
	      (map
	       (lambda (l) (cons u l))
	       (all-paths-from-abstract-value-internal
		(a-member-of (vector->list (recursive-closure-values u)))
		vs)))
	     '())))
       (else (list (list u)))))

(define (all-paths-from-proto-abstract-value u)
 (all-paths-from-proto-abstract-value-internal u '()))

(define (abstract-value-depth path)
 (cond ((null? path) 0)
       ((and (list? (first path))
	     ;; () makes list? true, so guard against it
	     (not (null? (first path))))
	(+ 1 (abstract-value-depth (rest path))))
       (else (abstract-value-depth (rest path)))))

(define (matching-nonrecursive-closure-depth path)
 ;; it is assumed that path starts with an abstract value
 (cond ((null? path) 0)
       ((null? (rest path)) 0)
       ((nonrecursive-closure? (second path))
	(count-if (lambda (u-or-v)
		   (and (nonrecursive-closure? u-or-v)
			(nonrecursive-closure-match? u-or-v (second path))))
		  (rest path)))
       (else 0)))

(define (path-of-depth-greater-than-k k depth u-or-v)
 (let loop ((u-or-v u-or-v) (path '()))
  (let ((add-to-path (lambda (u-or-v) (append path (list u-or-v)))))
   ;; if u-or-v is an abstract value...
   (if (and (list? u-or-v) (not (null? u-or-v)))
       ;; if u-or-v is already on path...
       (if (memq u-or-v path)
	   (if (> (depth path) k) path #f)
	   (let inner ((us u-or-v))
	    (if (null? us)
		(if (> (depth (add-to-path u-or-v)) k) (add-to-path u-or-v) #f)
		(let ((result (loop (first us) (add-to-path u-or-v))))
		 (if (eq? #f result)
		     (inner (rest us))
		     result)))))
       (cond ((or (null? u-or-v)
		  (boolean? u-or-v)
		  (abstract-real? u-or-v)
		  (primitive-procedure? u-or-v))
	      (if (> (depth (add-to-path u-or-v)) k) (add-to-path u-or-v) #f))
	     ((nonrecursive-closure? u-or-v)
	      (let inner ((vs (vector->list
			       (nonrecursive-closure-values u-or-v))))
	       (if (null? vs)
		   (if (> (depth (add-to-path u-or-v)) k)
		       (add-to-path u-or-v)
		       #f)
		   (let ((result (loop (first vs) (add-to-path u-or-v))))
		    (if (eq? #f result)
			(inner (rest vs))
			result)))))
	     ((recursive-closure? u-or-v)
	      (let inner ((vs (vector->list
			       (recursive-closure-values u-or-v))))
	       (if (null? vs)
		   (if (> (depth (add-to-path u-or-v)) k)
		       (add-to-path u-or-v)
		       #f)
		   (let ((result (loop (first vs) (add-to-path u-or-v))))
		    (if (eq? #f result)
			(inner (rest vs))
			result)))))
	     (else (panic "This part not (yet) implemented!")))))))

(define (path-of-greatest-depth depth u-or-v)
 (let ((paths (all-paths-from-abstract-value u-or-v)))
  (set! *num-paths-looked-at* (+ *num-paths-looked-at* (length paths)))
  (set! *total-size-paths-looked-at*
	(+ *total-size-paths-looked-at* (reduce + (map length paths) 0)))
;;; (let ((paths (if (and (list? u-or-v) (not (null? u-or-v)))
;;;		  (all-paths-from-abstract-value u-or-v)
;;;		  (all-paths-from-proto-abstract-value u-or-v))))
  (if (not (null? paths))
      (let loop ((paths (rest paths))
		 (max-path (first paths))
		 (max-depth (depth (first paths))))
       (if (null? paths)
	   max-path
	   (let ((path-depth (depth (first paths))))
	    (if (> path-depth max-depth)
		(loop (rest paths) (first paths) path-depth)
		(loop (rest paths) max-path max-depth)))))
      '())))

(define (find-path-to-collapse k depth u-or-v)
 (if *new-find-path?*
     (path-of-depth-greater-than-k k depth u-or-v)
     (let ((result (path-of-greatest-depth depth u-or-v)))
      (if (> (depth result) k) result #f))))

(define (limit-depth-to k depth u-or-v reduce-depth!)
 (set! *num-calls-limit-depth-to* (+ *num-calls-limit-depth-to* 1))
 (let ((path (collect-time-in-buckets
	      'find-path-to-collapse
	      (lambda () (find-path-to-collapse k depth u-or-v)))))
  (if (eq? #f path)
      u-or-v
      (limit-depth-to k
		      depth
		      (collect-time-in-buckets
		       'reduce-depth!
		       (lambda () (reduce-depth! k path)))
		      reduce-depth!))))

(define (reduce-abstract-value-depth! k path)
 ;; case: first in path is u
 ;;       first in path is v
 ;;
 ;; ... v1 u1 v2 u2 -> ... v1 u1 v1 (ensuring that v1 has all in v2)
 ;; case: - nothing in path prior to v1--return v1-new
 ;;       - u0 in path prior to v1--set u0 to point to v1-new and return first
 ;;         element in path
 (let ((l (length path)))
  (if (< l 4)
      (panic "This really shouldn't happen!")
      (let ((v1 (list-ref path (- l 4)))
	    (u1 (list-ref path (- l 3)))
	    (v2 (list-ref path (- l 2))))
       (if (nonrecursive-closure? u1)
	   (vector-set! (nonrecursive-closure-values u1)
			(positionq
			 v2 (vector->list (nonrecursive-closure-values u1)))
			v1)
	   (vector-set! (recursive-closure-values u1)
			(positionq
			 v2 (vector->list (recursive-closure-values u1)))
			v1))
       (let ((v1-new (abstract-value-union v1 v2)))
	(set-car! v1 (car v1-new))
	(set-cdr! v1 (cdr v1-new)))))))

(define (decrement-free-ups v)
 (define (decrement-free-ups v k)
  (define (proto-decrement-free-ups u)
   (cond ((null? u) u)
	 ((boolean? u) u)
	 ((abstract-real? u) u)
	 ((primitive-procedure? u) u)
	 ((nonrecursive-closure? u)
	  (make-nonrecursive-closure
	   (nonrecursive-closure-variables u)
	   (map-vector (lambda (v) (decrement-free-ups v (+ k 1)))
		       (nonrecursive-closure-values u))
	   (nonrecursive-closure-variable u)
	   (nonrecursive-closure-body u)))
	 ((recursive-closure? u)
	  (make-recursive-closure
	   (recursive-closure-variables u)
	   (map-vector (lambda (v) (decrement-free-ups v (+ k 1)))
		       (recursive-closure-values u))
	   (recursive-closure-procedure-variables u)
	   (recursive-closure-argument-variables u)
	   (recursive-closure-bodies u)
	   (recursive-closure-index u)))
	 (else (fuck-up))))
  (if (up? v)
      (if (> (up-index v) k) (make-up (- (up-index v) 1)) (up-index v))
      (map proto-decrement-free-ups v)))
 (decrement-free-ups v 0))

; (define (reduce-abstract-value-depth-functionally k path)
;  (define (proto-restrict-depth-of-tree-to k u)
;   ...)
;  (define (restrict-depth-of-tree-to k v)
;   ;; what if v is up?
;   (if (= k 1)
;       (let* ((nonrecursive-us (remove-if-not nonrecursive-closure? v))
; 	     (recursive-us (remove-if-not recursive-closure? v))
; 	     (vs (remove-if
; 		  up?
; 		  (reduce
; 		   append
; 		   (append
; 		    (map (lambda (u)
; 			  (vector->list (nonrecursive-closure-values u)))
; 			 nonrecursive-us)
; 		    (map (lambda (u)
; 			  (vector->list (recursive-closure-values u)))
; 			 recursive-us))
; 		   '())))
; 	     (vs-prime (decrement-free-ups (reduce append vs '())))
; 	     (...)))))
;  (let ((v (first path))
;        (v-uncyc (uncyclicize-abstract-value v))
;        (...))
;   ...))

;;; We will reduce the depth of only the path provided, and we'll reduce that
;;; by only 1.
;;; - The path must start with an abstract value v0.
;;; - The path must end with the sequence v_j-1 u_j-1 v_j u_j. (j>=1)
;;;   This will be transformed to v_j-1' u_j-1' v_j-1', where v_j-1'
;;;   = (non-depth-limited-abstract-value-union v_j-1 v_j)
;;; - Each abstract value and proto-abstract value on the path must be
;;;   replaced with a new one (one that's not eq?).
;;; - Each reference to an abstract value on the path must be replaced
;;;   with a reference to the new abstract value.
;;; Needed:
;;; - non-depth-limited-abstract-value-union v1 v2 -- abstract-value-union
;;;   w/no depth limit
;;; -
;;; - replace-abstract-value v-old v-new -- all references to v-old replaced
;;;   with references to v-new

(define (reduce-abstract-value-depth!-2 k path)
 ;; path starts with a value when:
 ;; (and (> (length path) 0) (list? (first path)) (not (null? first path)))
 (when (or (= (length path) 0) (not (list? (first path))) (null? (first path)))
  (panic "reduce-abstract-value-depth!-2 error!"))
 ;; v0 ... v1 u1 v2 u2 -> v0' ... v1' u1 v1' (ensuring that v1' has all in v2)
 ;; case: - nothing in path prior to v1--return v1-new
 ;;       - u0 in path prior to v1--set u0 to point to v1-new and return first
 ;;         element in path
 (when (< (length path) 4)
  (panic "This really shouldn't happen!"))
 (let* ((l (length path))
	(uj (list-ref path (- l 1)))
	(vj (list-ref path (- l 2)))
	(uj-1 (list-ref path (- l 3)))
	(vj-1 (list-ref path (- l 4)))
	(vj-1-new (cons #f #f))
	(uj-1-new (replaceq-in-u vj vj-1-new uj-1))
	(vj-1-tmp (replaceq-in-v-internal
		   vj-1
		   vj-1-new
		   (list-replace vj-1 (positionq uj-1 vj-1) uj-1-new)
		   (list vj-1-new))))
  (set-car! vj-1-new (car vj-1-tmp))
  (set-cdr! vj-1-new (cdr vj-1-tmp))
  ;; this non-depth-limited-abstract-value-union could mess with backlinks
  (let ((vj-1-tmp (non-depth-limited-abstract-value-union vj-1-new vj)))
   (set-car! vj-1-new (car vj-1-tmp))
   (set-cdr! vj-1-new (cdr vj-1-tmp))
   ;; c = child, p = parent
   (let loop ((vc-new vj-1-new)
	      (vc-old vj-1)
	      (path (rest (rest (rest (rest (reverse path)))))))
    (cond ((null? path) vc-new)
	  ((null? (rest path)) (panic "Path should be of even length!"))
	  (else
	   (let* ((up (first path))
		  (vp (second path))
		  (up-new (replaceq-in-u vc-old vc-new up))
		  (vp-new (cons #f #f))
		  (vp-tmp (replaceq-in-v
			   vp
			   vp-new
			   (list-replace vp (positionq up vp) up-new))))
	    (set-car! vp-new (car vp-tmp))
	    (set-cdr! vp-new (cdr vp-tmp))
	    (loop vp-new vp (rest (rest path))))))))))

(define (replaceq-in-u-internal v-old v-new u vs)
 (cond ((null? u) u)
       ((boolean? u) u)
       ((abstract-real? u) u)
       ((primitive-procedure? u) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 (map-vector
	  (lambda (v)
	   (if (eq? v v-old) v-new (replaceq-in-v-internal v-old v-new v vs)))
	  (nonrecursive-closure-values u))
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 (map-vector
	  (lambda (v)
	   (if (eq? v v-old) v-new (replaceq-in-v-internal v-old v-new v vs)))
	  (recursive-closure-values u))
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (fuck-up))))

(define (replaceq-in-v-internal v-old v-new v vs)
 (cond ((memq v vs) v)
       ((eq? v v-old) v-new)
       (else
	(map (lambda (u) (replaceq-in-u-internal v-old v-new u (cons v vs)))
	     v))))

(define (replaceq-in-u v-old v-new u)
 (replaceq-in-u-internal v-old v-new u '()))

(define (replaceq-in-v v-old v-new v)
 (replaceq-in-v-internal v-old v-new v '()))

(define (reduce-abstract-value-depth!-3 k path)
 ;; path starts with a value when:
 ;; (and (> (length path) 0) (list? (first path)) (not (null? first path)))
 (when (or (= (length path) 0) (not (list? (first path))) (null? (first path)))
  (panic "reduce-abstract-value-depth!-2 error!"))
 ;; v0 ... v1 u1 v2 u2 -> v0' ... v1' u1 v1' (ensuring that v1' has all in v2)
 ;; case: - nothing in path prior to v1--return v1-new
 ;;       - u0 in path prior to v1--set u0 to point to v1-new and return first
 ;;         element in path
 (when (< (length path) 4)
  (panic "This really shouldn't happen!"))
 (let* ((l (length path))
	(vs-above (but-last (but-last (every-other path))))
	(vs-above-bindings (map (lambda (v) (cons v v)) vs-above))
	(uj (list-ref path (- l 1)))
	(vj (list-ref path (- l 2)))
	(uj-1 (list-ref path (- l 3)))
	(vj-1 (list-ref path (- l 4)))
	(vj-1-new (cons #f #f))
	(vj-1-tmp (replaceq-in-v-no-destroy-backlinks
		   vj-1 (cons (cons vj vj-1-new) vs-above-bindings))))
  (set-car! vj-1-new (car vj-1-tmp))
  (set-cdr! vj-1-new (cdr vj-1-tmp))
  ;; this non-depth-limited-abstract-value-union could mess with backlinks
  (let ((vj-1-tmp (non-depth-limited-abstract-value-union vj-1-new vj)))
   (set-car! vj-1-new (car vj-1-tmp))
   (set-cdr! vj-1-new (cdr vj-1-tmp))
   ;; c = child, p = parent
   (let loop ((vc-new vj-1-new)
	      (vc-old vj-1)
	      (path (rest (rest (rest (rest (reverse path))))))
	      (vs-bindings vs-above-bindings))
    ;; As we step up the path, we keep all those abstract-values which appear
    ;; above vp in the tree rooted at (first path) constant when they happen to
    ;; appear in the tree rooted at vp.  We do this so as not to clobber
    ;; backlinks.  We can't simply do
    ;;                               (replaceq-in-v-no-destroy-backlinks
    ;;                                (first path) (list (cons vj-1 vj-1-new)))
    ;; because there might be backlinks in vj-1-new to values appearing in
    ;; path above vj-1.
    (cond ((null? path) vc-new)
	  ((null? (rest path)) (panic "Path should be of even length!"))
	  (else
	   (let* ((vp (second path))
		  (vp-new
		   (replaceq-in-v-no-destroy-backlinks
		    vp (cons (cons vc-old vc-new) (but-last vs-bindings)))))
	    (loop vp-new vp (rest (rest path)) (but-last vs-bindings)))))))))

(define (replaceq-in-u-no-destroy-backlinks u v-bindings)
 (cond ((null? u) u)
       ((boolean? u) u)
       ((abstract-real? u) u)
       ((primitive-procedure? u) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 (map-vector
	  (lambda (v) (replaceq-in-v-no-destroy-backlinks v v-bindings))
	  (nonrecursive-closure-values u))
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 (map-vector
	  (lambda (v) (replaceq-in-v-no-destroy-backlinks v v-bindings))
	  (recursive-closure-values u))
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (fuck-up))))

(define (replaceq-in-v-no-destroy-backlinks v v-bindings)
 (let ((lookup (assq v v-bindings)))
  (if (not (eq? #f lookup))
      (cdr lookup)
      (let* ((v-prime (cons #f #f))
	     (v-tmp (map (lambda (u)
			  (replaceq-in-u-no-destroy-backlinks
			   u (cons (cons v v-prime) v-bindings)))
			 v)))
       (set-car! v-prime (car v-tmp))
       (set-cdr! v-prime (cdr v-tmp))
       v-prime))))

(define (reduce-abstract-value-depth!-4 k path)
 ;; path starts with a value when:
 ;; (and (> (length path) 0) (list? (first path)) (not (null? first path)))
 (when (or (= (length path) 0) (not (list? (first path))) (null? (first path)))
  (panic "reduce-abstract-value-depth!-2 error!"))
 ;; v0 ... v1 u1 v2 u2 -> v0' ... v1' u1 v1' (ensuring that v1' has all in v2)
 ;; case: - nothing in path prior to v1--return v1-new
 ;;       - u0 in path prior to v1--set u0 to point to v1-new and return first
 ;;         element in path
 (when (< (length path) 4)
  (panic "This really shouldn't happen!"))
 (let* ((l (length path))
	(vs-above (but-last (but-last (every-other path))))
	(vs-above-bindings (map (lambda (v) (cons v v)) vs-above))
	(uj (list-ref path (- l 1)))
	(vj (list-ref path (- l 2)))
	(uj-1 (list-ref path (- l 3)))
	(vj-1 (list-ref path (- l 4)))
	(vj-1-new (cons #f #f))
	(vj-1-tmp
	 (replaceq-in-v-no-destroy-backlinks-2
	  vj vj-1-new vj-1 (cons (cons vj-1-new vj-1-new) vs-above-bindings))))
  (set-car! vj-1-new (car vj-1-tmp))
  (set-cdr! vj-1-new (cdr vj-1-tmp))
  ;; this non-depth-limited-abstract-value-union could mess with backlinks
  (let ((vj-1-tmp (non-depth-limited-abstract-value-union vj-1-new vj)))
   (set-car! vj-1-new (car vj-1-tmp))
   (set-cdr! vj-1-new (cdr vj-1-tmp))
   (replaceq-in-v-no-destroy-backlinks-2 vj-1 vj-1-new (first path) '()))))

(define (reduce-abstract-value-depth!-5 k path)
 (set! *num-calls-reduce-depth!* (+ *num-calls-reduce-depth!* 1))
 ;; path starts with a value when:
 ;; (and (> (length path) 0) (list? (first path)) (not (null? first path)))
 (when (or (= (length path) 0) (not (list? (first path))) (null? (first path)))
  (panic "reduce-abstract-value-depth!-2 error!"))
 ;; v0 ... v1 u1 v2 u2 -> v0' ... v1' u1 v1' (ensuring that v1' has all in v2)
 ;; case: - nothing in path prior to v1--return v1-new
 ;;       - u0 in path prior to v1--set u0 to point to v1-new and return first
 ;;         element in path
 (when (< (length path) 4)
  (panic "This really shouldn't happen!"))
 (let* ((l (length path))
	(vs-above (but-last (but-last (every-other path))))
	(vs-above-bindings (map (lambda (v) (cons v v)) vs-above))
	(uj (list-ref path (- l 1)))
	(vj (list-ref path (- l 2)))
	(uj-1 (list-ref path (- l 3)))
	(vj-1 (list-ref path (- l 4)))
	(vj-1-new (replaceq-in-v-no-destroy-backlinks-2
		   vj vj-1 vj-1 vs-above-bindings)))
  (let ((vj-1-new (union-to-potentially-circular-abstract-value vj-1-new vj)))
   (replaceq-in-v-no-destroy-backlinks-2 vj-1 vj-1-new (first path) '()))))

(define (replaceq-in-u-no-destroy-backlinks-2 v-old v-new u v-bindings)
 (cond ((null? u) u)
       ((boolean? u) u)
       ((abstract-real? u) u)
       ((primitive-procedure? u) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 (map-vector
	  (lambda (v)
	   (replaceq-in-v-no-destroy-backlinks-2 v-old v-new v v-bindings))
	  (nonrecursive-closure-values u))
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 (map-vector
	  (lambda (v)
	   (replaceq-in-v-no-destroy-backlinks-2 v-old v-new v v-bindings))
	  (recursive-closure-values u))
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (fuck-up))))

(define (replaceq-in-v-no-destroy-backlinks-2 v-old v-new v v-bindings)
 ;; (format #t "replaceq-in-v(~s,~s,~s)~%" (externalize-abstract-value v-old)
 ;;	 (externalize-abstract-value v-new) (externalize-abstract-value v))
 (let ((lookup (assq v v-bindings)))
  (cond
   ((null? v) v)
   ((not (eq? #f lookup)) (cdr lookup))
   ((eq? v v-old)
    (replaceq-in-v-no-destroy-backlinks-2 v-old v-new v-new v-bindings))
   (else
    (let* ((v-prime (cons #f #f))
	   (v-tmp (map (lambda (u)
			(replaceq-in-u-no-destroy-backlinks-2
			 v-old v-new u (cons (cons v v-prime) v-bindings)))
		       v)))
     (set-car! v-prime (car v-tmp))
     (set-cdr! v-prime (cdr v-tmp))
     v-prime)))))

;;; End Depth limits

(define (widen-abstract-value v)
 ;; *l4* *l5*
 ;; to-do: instrument
 (collect-time-in-buckets
  'widen-abstract-value
  (lambda ()
   (let* ((null-us (remove-if-not null? v))
	  (boolean-us (remove-if-not boolean? v))
	  (real-us (remove-if-not abstract-real? v))
	  (real-us
	   (if (not *l2*)
	       real-us
	       (limit-to-k-matching-proto-abstract-values
		*l2* real-us (lambda (us) '(real)))))
	  (primitive-procedure-us (remove-if-not primitive-procedure? v))
	  (nonrecursive-closure-us (remove-if-not nonrecursive-closure? v))
	  (nonrecursive-closure-us
	   (if (not *l3*)
	       nonrecursive-closure-us
	       (collect-time-in-buckets
		'widen-nonrecursive-closure
		(lambda ()
		 (let ((nonrecursive-closure-uss
			(transitive-equivalence-classesp
			 nonrecursive-closure-match? nonrecursive-closure-us)))
		  (reduce
		   append
		   (map (lambda (us)
			 ;; needs work: factor out choice of coalescing
			 ;;             strategy
			 (limit-to-k-matching-proto-abstract-values
			  *l3*
			  us
			  naive-nonrecursive-closure-coalescing-strategy))
			nonrecursive-closure-uss)
		   '()))))))
	  (recursive-closure-us (remove-if-not recursive-closure? v))
	  (recursive-closure-us
	   (if (not *l4*)
	       recursive-closure-us
	       (collect-time-in-buckets
		'widen-recursive-closure
		(lambda ()
		 (let ((recursive-closure-uss
			(transitive-equivalence-classesp
			 recursive-closure-match? recursive-closure-us)))
		  (reduce
		   append
		   (map (lambda (us)
			 ;; needs work: factor out choice of coalescing
			 ;;             strategy
			 (limit-to-k-matching-proto-abstract-values
			  *l4* us naive-recursive-closure-coalescing-strategy))
			recursive-closure-uss)
		   '()))))))
	  (result
	   (append null-us
		   boolean-us
		   real-us
		   primitive-procedure-us
		   nonrecursive-closure-us
		   recursive-closure-us))
	  (result
	   (if #t
	       (replaceq-in-v-no-destroy-backlinks-2 v result result '())
	       result)))
    (if (not *l5*)
	result
	(collect-time-in-buckets
	 'widen-limit-depth
	 (lambda ()
	  (limit-depth-to
	   *l5*
	   (if *matching-nonrecursive-closure-depth?*
	       matching-nonrecursive-closure-depth
	       abstract-value-depth)
	   result
	   reduce-abstract-value-depth!-5))))))))

(define (generic-abstract-value-union v1 v2)
 (cond
  ((null? v1) v2)
  ((null? v2) v1)
  ((proto-abstract-value-in-abstract-value? (first v1) v2)
   (generic-abstract-value-union (rest v1) v2))
  (else (cons (first v1)
	      (generic-abstract-value-union
	       (rest v1)
	       (removep proto-abstract-value-superset? (first v1) v2))))))

(define (generic-abstract-value-union-qobi v1 v2)
 (let loop ((us (append v1 v2)) (v (append v1 v2)))
  (cond ((null? us) v)
	((abstract-value-subset? (list (first us)) (removeq (first us) v))
	 (loop (rest us) (removeq (first us) v)))
	(else (loop (rest us) v)))))

(define (abstract-value-union v1 v2)
 (set! *num-calls-abstract-value-union* (+ *num-calls-abstract-value-union* 1))
 (let ((result-1 (generic-abstract-value-union v1 v2))
       (result-2 (generic-abstract-value-union-qobi v1 v2)))
  ;; debugging
  (when (and #t (some (lambda (u1) (not (memq u1 result-2))) result-1))
   (format #t
	   (string-append "*** generic-abstract-value-union{,-qobi} give "
			  "different results:~%"
			  "    generic-abstract-value-union: ~%"))
   (pp (externalize-abstract-value result-1)) (newline)
   (format #t "    generic-abstract-value-union-qobi: ~%")
   (pp (externalize-abstract-value result-2)) (newline)
   ;; debugging
   (when (and *debug?* (> *debug-level* 3))
    (fuck-up)))
  (widen-abstract-value result-1)))

(define (union-to-potentially-circular-abstract-value v-circ v)
 (let* ((result (generic-abstract-value-union v-circ v))
	(result (replaceq-in-v-no-destroy-backlinks-2
		 v-circ result result '())))
  (let ((l5 *l5*))
   (set! *l5* #f)
   (let ((result (widen-abstract-value result)))
    (set! *l5* l5)
    result))))

(define (non-depth-limited-abstract-value-union v1 v2)
 (let ((result-1 (generic-abstract-value-union v1 v2))
       (result-2 (generic-abstract-value-union-qobi v1 v2)))
  ;; debugging
  (when (and #t (some (lambda (u1) (not (memq u1 result-2))) result-1))
   (format #t
	   (string-append "*** generic-abstract-value-union{,-qobi} give "
			  "different results:~%"
			  "    generic-abstract-value-union: ~%"))
   (pp (externalize-abstract-value result-1)) (newline)
   (format #t "    generic-abstract-value-union-qobi: ~%")
   (pp (externalize-abstract-value result-2)) (newline)
   ;; debugging
   (when (and *debug?* (> *debug-level* 3))
    (fuck-up)))
  (let ((l5 *l5*))
   (set! *l5* #f)
   (let ((result (widen-abstract-value result-1)))
    (set! *l5* l5)
    result))))

;;; Abstract-Environment Subset, Equivalence, and Union

(define (abstract-environment-subset? vs1 vs2)
 (every-vector abstract-value-subset? vs1 vs2))

(define (abstract-environment=? vs1 vs2)
 (and (abstract-environment-subset? vs1 vs2)
      (abstract-environment-subset? vs2 vs1)))

(define (abstract-environment-proper-subset? vs1 vs2)
 (and (abstract-environment-subset? vs1 vs2)
      (not (abstract-environment-subset? vs2 vs1))))

(define (abstract-environment-union vs1 vs2)
 (map-vector abstract-value-union vs1 vs2))

;;; Abstract-Flow Equivalence and Union

(define (abstract-flow=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp?
  (lambda (b1 b2)
   (and (abstract-environment=?
	 (abstract-environment-binding-abstract-values b1)
	 (abstract-environment-binding-abstract-values b2))
	(abstract-value=? (abstract-environment-binding-abstract-value b1)
			  (abstract-environment-binding-abstract-value b2))))
  bs1
  bs2))

(define (empty-abstract-flow) '())

;;; brownfis -- added
(define (duplicatesp? p xs)
 (and (not (null? xs))
      (or (memp p (first xs) (rest xs)) (duplicatesp? p (rest xs)))))

(define (restrict-number-of-abstract-flow-elements-to k bs)
 ;; This function introduces the imprecision in abstract-flow-union.
 ;; needs work: Can implement more intelligent strategies.
 (when #f
  (format #t "restricting to ~s elements: ~s~%"
	  k (externalize-abstract-flow bs)))
 (if (<= (length bs) k)
     bs
     (restrict-number-of-abstract-flow-elements-to
      k
      (cons (make-abstract-environment-binding
	     (abstract-environment-union
	      (abstract-environment-binding-abstract-values (first bs))
	      (abstract-environment-binding-abstract-values (second bs)))
	     (abstract-value-union
	      (abstract-environment-binding-abstract-value (first bs))
	      (abstract-environment-binding-abstract-value (second bs))))
	    (rest (rest bs))))))

;;; needs work: Can this result in a flow having abstract-environment-bindings
;;;             with abstract environments e1, e2 such that
;;;             (abstract-environment-subset? e1 e2) => #t?
;;;     answer: Yes, and why exactly shouldn't this happen?
(define (abstract-flow-union bs1 bs2)
 ;; This is one place where imprecision can be introduced.
 (let ((bs
	(if (null? bs1)
	    bs2
	    (let ((b2 (find-if
		       (lambda (b2)
			(abstract-environment=?
			 (abstract-environment-binding-abstract-values
			  (first bs1))
			 (abstract-environment-binding-abstract-values b2)))
		       bs2)))
	     (if b2
		 (abstract-flow-union
		  (rest bs1)
		  (cons (make-abstract-environment-binding
			 (abstract-environment-binding-abstract-values b2)
			 (abstract-value-union
			  (abstract-environment-binding-abstract-value
			   (first bs1))
			  (abstract-environment-binding-abstract-value b2)))
			(removeq b2 bs2)))
		 (cons (first bs1) (abstract-flow-union (rest bs1) bs2)))))))
  (if (and *l1* (> (length bs) *l1*))
      (restrict-number-of-abstract-flow-elements-to *l1* bs)
      bs)))

;;; Abstract-Analysis Equivalence and Union

(define (abstract-analysis=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp?
  (lambda (b1 b2)
   (and
    ;; needs work: Do we need identity or alpha equivalence here?
    (eq? (abstract-expression-binding-expression b1)
	 (abstract-expression-binding-expression b2))
    (abstract-flow=? (abstract-expression-binding-abstract-flow b1)
		     (abstract-expression-binding-abstract-flow b2))))
  bs1
  bs2))

(define (empty-abstract-analysis) '())

(define (abstract-analysis-union bs1 bs2)
 (set! *num-calls-abstract-analysis-union*
       (+ *num-calls-abstract-analysis-union* 1))
 (set! *num-abstract-expression-bindings-in-analysis-unions*
       (+ *num-abstract-expression-bindings-in-analysis-unions*
	  (length bs1) (length bs2)))
 (define (abstract-analysis-union bs1 bs2)
  (if (null? bs1)
      bs2
      (let ((b2 (find-if
		 (lambda (b2)
		  ;; needs work: Do we need identity or alpha equivalence here?
		  (eq? (abstract-expression-binding-expression (first bs1))
		       (abstract-expression-binding-expression b2)))
		 bs2)))
       (if b2
	   (abstract-analysis-union
	    (rest bs1)
	    (let ((result
		   (cons (make-abstract-expression-binding
			  (abstract-expression-binding-expression b2)
			  (abstract-flow-union
			   (abstract-expression-binding-abstract-flow
			    (first bs1))
			   (abstract-expression-binding-abstract-flow b2)))
			 (removeq b2 bs2))))
	     result))
	   (cons (first bs1) (abstract-analysis-union (rest bs1) bs2))))))
 (abstract-analysis-union bs1 bs2))

;;; Flow Analysis

(define (letrec-expression-recursive-closure-variables e)
 (letrec-recursive-closure-variables
  (letrec-expression-procedure-variables e)
  (letrec-expression-argument-variables e)
  (letrec-expression-bodies e)))

(define (minimal-elements <? s)
 ;; belongs in QobiScheme
 (remove-if (lambda (e) (some (lambda (e-prime) (<? e-prime e)) s)) s))

(define (create-abstract-analysis e vs)
 (set! *num-calls-create-abstract-analysis*
       (+ *num-calls-create-abstract-analysis* 1))
 (let ((xs (free-variables e)))
  (when (not (= (vector-length vs) (length (free-variables e))))
   (format #t "xs=~s~%" xs)
   (format #t "vs=~s~%" (map-vector externalize-abstract-value vs))
   (panic "create-abstract-analysis: xs and vs should be of same length!")))
 (list
  (make-abstract-expression-binding
   e (list (make-abstract-environment-binding vs (empty-abstract-value))))))

(define (vlad-value->abstract-value v)
 (cond ((null? v) (list v))
       ((boolean? v) (list v))
       ((abstract-real? v) (list v))
       ((primitive-procedure? v) (list v))
       ((nonrecursive-closure? v)
	(list (make-nonrecursive-closure
	       (nonrecursive-closure-variables v)
	       (map-vector vlad-value->abstract-value
			   (nonrecursive-closure-values v))
	       (nonrecursive-closure-variable v)
	       (nonrecursive-closure-body v))))
       ((recursive-closure? v)
	(list (make-recursive-closure
	       (recursive-closure-variables v)
	       (map-vector vlad-value->abstract-value
			   (recursive-closure-values v))
	       (recursive-closure-procedure-variables v)
	       (recursive-closure-argument-variables v)
	       (recursive-closure-bodies v)
	       (recursive-closure-index v))))
       (else (panic "Not a vlad value!"))))

;;; brownfis: The set of expressions that the initial abstract analysis needs
;;;           to map is the set of all (reachable) subexpressions of e plus
;;;           any expressions in a closure corresponding to a constant that is
;;;           either abstract-vlad-true or abstract-vlad-false, according to
;;;           the church encoding of booleans.  We need not concern ourselves
;;;           with those expressions making the body of closures corresponding
;;;           to constant pairs for this reason--these expressions are never
;;;           executed.  We must concern ourselves with constant Church-encoded
;;;           booleans for precisely this reason, as the evaluation of an
;;;           if-expression in the church encoding is simply a matter of
;;;           applying a boolean to two arguments, #t returning the first and
;;;           #f returning the second.
(define (empty-analysis-for-expression e)
 (cons (make-abstract-expression-binding e (empty-abstract-flow))
       (cond ((variable-access-expression? e) (empty-abstract-analysis))
	     ((lambda-expression? e)
	      (empty-analysis-for-expression (lambda-expression-body e)))
	     ((application? e)
	      (append (empty-analysis-for-expression (application-callee e))
		      (empty-analysis-for-expression
		       (application-argument e))))
	     ((letrec-expression? e)
	      (append (empty-analysis-for-expression
		       (letrec-expression-body e))
		      (reduce append
			      (map empty-analysis-for-expression
				   (letrec-expression-bodies e))
			      (empty-abstract-flow))))
	     (else (fuck-up)))))

(define (initial-abstract-analysis e bs)
 (abstract-analysis-union
  (if *church?*
      (abstract-analysis-union
       (empty-analysis-for-expression
	(new-lambda-expression (nonrecursive-closure-variable vlad-true)
			       (nonrecursive-closure-body vlad-true)))
       (empty-analysis-for-expression
	(new-lambda-expression (nonrecursive-closure-variable vlad-false)
			       (nonrecursive-closure-body vlad-false))))
      '())
  (let loop ((e e) (vs (list->vector
			(map
			 (lambda (x)
			  ;; here I am
			  (vlad-value->abstract-value
			   (value-binding-value
			    (find-if
			     (lambda (b)
			      (variable=? x (value-binding-variable b)))
			     bs))))
			 (free-variables e)))))
   ;; brownfis -- There is a subtle bug at play here.  We only wish to create
   ;;             one abstract-expression-binding with a non-empty
   ;;             abstract flow--that of the initial expression on which flow
   ;;             analysis is being performed.  As it stands, this
   ;;             implementation *tries* to do so for the body of every
   ;;             constant nonrecursive closure (#t/#f).  This ends up causing
   ;;             an error, as there is one free variable in the closure-body
   ;;             of #t/#f--a.  To guard against this, I've had the reduce
   ;;             portion loop on the lambda expression which formed the
   ;;             closure, not on the closure itself.  Otherwise, we'd need to
   ;;             supply an abstract value for the free variable, but there is
   ;;             no such abstract value at this point of the analysis.
   (abstract-analysis-union
    (append
     (create-abstract-analysis e vs)
     (rest
      (let loop ((e e))
       (cons (make-abstract-expression-binding e (empty-abstract-flow))
	     (cond ((variable-access-expression? e) (empty-abstract-analysis))
		   ((lambda-expression? e) (loop (lambda-expression-body e)))
		   ((application? e)
		    (append (loop (application-callee e))
			    (loop (application-argument e))))
		   ((letrec-expression? e)
		    (append (loop (letrec-expression-body e))
			    (reduce append
				    (map loop (letrec-expression-bodies e))
				    (empty-abstract-flow))))
		   (else (fuck-up)))))))
    (reduce
     abstract-analysis-union
     (vector->list
      (map-vector
       (lambda (v)
	(reduce
	 abstract-analysis-union
	 (map (lambda (u)
	       (cond ((null? u) (empty-abstract-analysis))
		     ((eq? u #t) (empty-abstract-analysis))
		     ((eq? u #f) (empty-abstract-analysis))
		     ((real? u) (empty-abstract-analysis))
		     ((eq? u 'real) (empty-abstract-analysis))
		     ((primitive-procedure? u) (empty-abstract-analysis))
		     ((nonrecursive-closure? u)
		      (loop (new-lambda-expression
			     (nonrecursive-closure-variable u)
			     (nonrecursive-closure-body u))
			    (nonrecursive-closure-values u)))
		     ((recursive-closure? u) (panic "error2"))
		     (else (format #t "u=~s~%" u) (panic "error3"))))
	      v)
	 (empty-abstract-analysis)))
       vs))
     (empty-abstract-analysis))))))

(define (abstract-value-in-matching-abstract-environment e vs bs)
 ;; vs is an abstract environment. bs is an abstract analysis. We want to find
 ;; an abstract value for e when e is evaluated in the abstract environment vs.
 ;; By corollary 1 we can choose any abstract-environment binding with a wider
 ;; abstract environment. We could compute the intersection of all such. Such
 ;; an intersection only depends on the narrowest such. We find the narrowest
 ;; such and pick the first arbitrarily since we lack the ability to intersect
 ;; abstract values. This will always choose an abstract-environment binding
 ;; with an equivalent abstract environment, if there is one, since it will be
 ;; the narrowest among the wider ones.
 (let* ((bs (minimal-elements
	     (lambda (b1 b2)
	      (abstract-environment-proper-subset?
	       (abstract-environment-binding-abstract-values b1)
	       (abstract-environment-binding-abstract-values b2)))
	     (remove-if-not
	      (lambda (b)
	       (when (not (vector? vs)) (panic "vs not a vector!"))
	       (when (not (vector?
			   (abstract-environment-binding-abstract-values b)))
		(panic "aeb-abstract-values not a vector!"))
	       (abstract-environment-subset?
		vs (abstract-environment-binding-abstract-values b)))
	      (expression-abstract-flow e bs)))))
  (if (null? bs)
      (begin
       (set!
	*num-calls-abstract-value-in-matching-abstract-environment-miss*
	(+ *num-calls-abstract-value-in-matching-abstract-environment-miss*
	   1))
       (empty-abstract-value))
      (begin
       (set!
	*num-calls-abstract-value-in-matching-abstract-environment-hit*
	(+ *num-calls-abstract-value-in-matching-abstract-environment-hit*
	   1))
       (abstract-environment-binding-abstract-value (first bs))))))

(define (map-vector-nondeterministic f v . &rest)
 (list->vector (apply map f (vector->list v) (map vector->list &rest))))

;;; here I am new
(define (multiply-out-nonrecursive-closure vs e)
 (set! *num-calls-multiply-out-nonrecursive-closure*
       (+ *num-calls-multiply-out-nonrecursive-closure* 1))
 (if #t					;debugging
     (let ((result
	    (all-values (make-nonrecursive-closure
			 (free-variables e)
			 (map-vector-nondeterministic
			  (lambda (v) (list (a-member-of v)))
			  vs)
			 (lambda-expression-variable e)
			 (lambda-expression-body e)))))
      (set! *num-nonrecursive-closures-multiplied-out*
	    (+ *num-nonrecursive-closures-multiplied-out* (length result)))
      result)
     (list (make-nonrecursive-closure
	    (free-variables e)
	    vs
	    (lambda-expression-variable e)
	    (lambda-expression-body e)))))

(define (multiply-out-recursive-closure xs vs xs-procedures xs-arguments es i)
 (set! *num-calls-multiply-out-recursive-closure*
       (+ *num-calls-multiply-out-recursive-closure* 1))
 (if #t					;debugging
     (let ((result
	    (all-values (make-recursive-closure
			 xs
			 (map-vector-nondeterministic
			  (lambda (v) (list (a-member-of v)))
			  vs)
			 xs-procedures
			 xs-arguments
			 es
			 i))))
      (set! *num-recursive-closures-multiplied-out*
	    (+ *num-recursive-closures-multiplied-out* (length result)))
      result)
     (list (make-recursive-closure xs vs xs-procedures xs-arguments es i))))

(define (abstract-apply-nonrecursive-closure p u1 u2)
 (let ((xs (nonrecursive-closure-variables u1)))
  (p (nonrecursive-closure-body u1)
     (list->vector
      ;; brownfis -- This has a subtle error.  The assumption present in this
      ;;             code is that (nonrecursive-closure-variable u1) is in
      ;;             (free-variables (nonrecursive-closure-body u1)); this,
      ;;             however, is NOT ALWAYS the case.  I now will check for it.
      (map (lambda (x)
	    (if (variable=? x (nonrecursive-closure-variable u1))
		(list u2)
		(vector-ref (nonrecursive-closure-values u1)
			    (positionq x xs))))
;;;	   (sort-variables (cons (nonrecursive-closure-variable u1) xs)))))))
	   (free-variables (nonrecursive-closure-body u1)))))))

(define (abstract-apply-recursive-closure p u1 u2)
 (let ((e (vector-ref (recursive-closure-procedure-lambda-expressions u1)
		      (recursive-closure-index u1)))
       (xs-procedures
	(vector->list (recursive-closure-procedure-variables u1)))
       (x-argument (vector-ref (recursive-closure-argument-variables u1)
			       (recursive-closure-index u1)))
       (xs (if #t
	       (recursive-closure-variables u1)
	       ;; old code
	       (letrec-recursive-closure-variables
		(abstract-recursive-closure-variables u1)
		(map lambda-expression-variable
		     (abstract-recursive-closure-expressions u1))
		(map lambda-expression-body
		     (abstract-recursive-closure-expressions u1))))))
  (p (lambda-expression-body e)
     (list->vector
      (map (lambda (x)
	    (cond
	     ((variable=? x (lambda-expression-variable e)) (list u2))
	     ((memp variable=? x xs-procedures)
	      (multiply-out-recursive-closure
	       (recursive-closure-variables u1)
	       (recursive-closure-values u1)
	       (recursive-closure-procedure-variables u1)
	       (recursive-closure-argument-variables u1)
	       (recursive-closure-bodies u1)
	       (positionq x xs-procedures)))
	     (else (vector-ref (recursive-closure-values u1)
			       (positionq x xs)))))
	   (free-variables (lambda-expression-body e)))))))

(define (abstract-apply v1 v2 bs)
 ;; bs is an analysis.
 (reduce
  abstract-value-union
  (map
   (lambda (u1)
    (reduce
     abstract-value-union
     (map (lambda (u2)
	   (cond ((primitive-procedure? u1)
		  ((primitive-procedure-abstract-procedure u1) u2))
		 ((nonrecursive-closure? u1)
		  (abstract-apply-nonrecursive-closure
		   (lambda (e vs)
		    (abstract-value-in-matching-abstract-environment e vs bs))
		   u1
		   u2))
		 ((recursive-closure? u1)
		  (abstract-apply-recursive-closure
		   (lambda (e vs)
		    (abstract-value-in-matching-abstract-environment e vs bs))
		   u1
		   u2))
		 ;; needs work: The target might not be a procedure. Need to
		 ;;             return concrete bottom in this case.
		 ;;             This calls for a compile-time-warning!
		 (else (empty-abstract-value))))
	  v2)
     (empty-abstract-value)))
   v1)
  (empty-abstract-value)))

(define (abstract-apply-prime v1 v2)
 (reduce
  abstract-analysis-union
  (map
   (lambda (u1)
    (reduce abstract-analysis-union
	    (map (lambda (u2)
		  (cond ((primitive-procedure? u1) (empty-abstract-analysis))
			((nonrecursive-closure? u1)
			 (abstract-apply-nonrecursive-closure
			  create-abstract-analysis u1 u2))
			((recursive-closure? u1)
			 (abstract-apply-recursive-closure
			  create-abstract-analysis u1 u2))
			(else (empty-abstract-analysis))))
		 v2)
	    (empty-abstract-analysis)))
   v1)
  (empty-abstract-analysis)))

(define (update-abstract-analysis bs)
 ;; The abstract evaluator induces an abstract analysis. This updates the
 ;; abstract values of all of the abstract-environment bindings of all of the
 ;; abstract expression bindings in the abstract analysis. The updated abstract
 ;; value is calculated by abstract evaluation in the abstract environment of
 ;; the abstract-environment binding. Recursive calls to the abstract evaluator
 ;; are replaced with abstract-value-in-matching-abstract-environment.
 (abstract-analysis-union
  (time
   "update-part-1: ~a~%"
   (lambda ()
    (map
     (lambda (b1)
      (make-abstract-expression-binding
       (abstract-expression-binding-expression b1)
       (map
	(lambda (b2)
	 (set! *num-abstract-environment-bindings*
	       (+ *num-abstract-environment-bindings* 1))
	 (let* ((e (abstract-expression-binding-expression b1))
		(xs (free-variables e))
		(vs (abstract-environment-binding-abstract-values b2)))
	  (when *debug?*
	   (format #t "update1: e=~s~%" (abstract->concrete e))
	   (format #t "environment: ~s~%"
		   (externalize-abstract-environment xs vs))
	   (when (and (lambda-expression? e)
		      (let*? (lambda-expression-body e)))
	    (let ((vs (map-vector uncyclicize-abstract-value vs))
		  (v (uncyclicize-abstract-value
		      (abstract-environment-binding-abstract-value b2))))
	     (write-object-to-file vs "saddle-environment.vlad")
	     (write-object-to-file v "saddle-value.vlad")
	     (write-object-to-file e "saddle-expression.vlad")
	     (format #t "expression=~s~%" e)
	     (format #t "environment=~%~s~%" vs)
	     (format #t "value=~%~s~%" v))))
	  (when (not (= (vector-length vs) (length (free-variables e))))
	   (format #t "xs=~s~%" xs)
	   (format #t "vs=~s~%" (map-vector externalize-abstract-value vs))
	   (panic (string-append "update-abstract-analysis: xs and vs should "
				 "be of same length!"))))
	 (let*
	   ((e (abstract-expression-binding-expression b1))
	    (vs (abstract-environment-binding-abstract-values b2))
	    (v (abstract-environment-binding-abstract-value b2))
	    (v-new
	     (cond
	      ((variable-access-expression? e) (vector-ref vs 0))
	      ((lambda-expression? e) (multiply-out-nonrecursive-closure vs e))
	      ((application? e)
	       (let ((xs (free-variables e)))
		(abstract-apply
		 ;; tag 2
		 (abstract-value-in-matching-abstract-environment
		  (application-callee e)
		  ;; tag 2a
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-callee e))))
		  bs)
		 ;; tag 3
		 (abstract-value-in-matching-abstract-environment
		  (application-argument e)
		  ;; tag 3a
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-argument e))))
		  bs)
		 bs)))
	      ((letrec-expression? e)
	       (abstract-value-in-matching-abstract-environment
		(letrec-expression-body e)
		;; tag 1
		(let ((xs (free-variables e)))
		 (list->vector
		  (map
		   (lambda (x)
		    (if (memp variable=?
			      x
			      (letrec-expression-procedure-variables e))
			(multiply-out-recursive-closure
			 (letrec-expression-recursive-closure-variables e)
			 (list->vector
			  (map
			   (lambda (x) (vector-ref vs (positionq x xs)))
			   (letrec-expression-recursive-closure-variables e)))
			 (list->vector
			  (letrec-expression-procedure-variables e))
			 (list->vector
			  (letrec-expression-argument-variables e))
			 (list->vector (letrec-expression-bodies e))
			 (positionp
			  variable=?
			  x
			  (letrec-expression-procedure-variables e)))
			(vector-ref vs (positionq x xs))))
		   (free-variables (letrec-expression-body e)))))
		bs))
	      (else (fuck-up)))))
	  (if *include-prior-values?*
	      (if (abstract-value-subset? v-new v)
		  b2
		  (make-abstract-environment-binding
		   vs (abstract-value-union v v-new)))
	      (make-abstract-environment-binding vs v-new))))
	(abstract-expression-binding-abstract-flow b1))))
     bs)))
  (time
   "update-part-2: ~a~%"
   (lambda ()
    (reduce
     abstract-analysis-union
     (map
      (lambda (b)
       (let ((e (abstract-expression-binding-expression b)))
	(reduce
	 abstract-analysis-union
	 (map
	  (lambda (b)
	   (let ((vs (abstract-environment-binding-abstract-values b)))
	    (cond
	     ((variable-access-expression? e) (empty-abstract-analysis))
	     ((lambda-expression? e) (empty-abstract-analysis))
	     ((application? e)
	      (let ((xs (free-variables e)))
	       (abstract-analysis-union
		(abstract-analysis-union
		 (create-abstract-analysis
		  (application-callee e)
		  ;; tag 2a
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-callee e)))))
		 (create-abstract-analysis
		  (application-argument e)
		  ;; tag 3a
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-argument e))))))
		(abstract-apply-prime
		 ;; tag 2
		 (abstract-value-in-matching-abstract-environment
		  (application-callee e)
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-callee e))))
		  bs)
		 ;; tag 3
		 (abstract-value-in-matching-abstract-environment
		  (application-argument e)
		  (list->vector
		   (map (lambda (x) (vector-ref vs (positionq x xs)))
			(free-variables (application-argument e))))
		  bs)))))
	     ((letrec-expression? e)
	      (create-abstract-analysis
	       (letrec-expression-body e)
	       ;; tag 1
	       (let ((xs (free-variables e)))
		(list->vector
		 (map
		  (lambda (x)
		   (if (memp variable=?
			     x
			     (letrec-expression-procedure-variables e))
		       (multiply-out-recursive-closure
			(letrec-expression-recursive-closure-variables e)
			(list->vector
			 (map
			  (lambda (x) (vector-ref vs (positionq x xs)))
			  (letrec-expression-recursive-closure-variables e)))
			(list->vector
			 (letrec-expression-procedure-variables e))
			(list->vector (letrec-expression-argument-variables e))
			(list->vector (letrec-expression-bodies e))
			(positionp
			 variable=?
			 x
			 (letrec-expression-procedure-variables e)))
		       (vector-ref vs (positionq x xs))))
		  (free-variables (letrec-expression-body e)))))))
	     (else (fuck-up)))))
	  (abstract-expression-binding-abstract-flow b))
	 (empty-abstract-analysis))))
      bs)
     (empty-abstract-analysis))))))

;;; brownfis -- Instrumentation

(define (instrument-reset)
 (set! *num-calls-abstract-value-union* 0)
 (set! *num-paths-looked-at* 0)
 (set! *total-size-paths-looked-at* 0)
 (set! *num-calls-limit-depth-to* 0)
 (set! *num-calls-reduce-depth!* 0)
 ; (set! *num-calls-abstract-value-subset* 0)
 (set! *num-calls-abstract-value-subset-loop?* 0)
 (set! *num-calls-free-variables* 0)
 ;; update--part 1
 (set! *num-abstract-environment-bindings* 0)
 (set! *num-calls-abstract-value-in-matching-abstract-environment-hit* 0)
 (set! *num-calls-abstract-value-in-matching-abstract-environment-miss* 0)
 (set! *num-calls-multiply-out-nonrecursive-closure* 0)
 (set! *num-nonrecursive-closures-multiplied-out* 0)
 (set! *num-calls-multiply-out-recursive-closure* 0)
 (set! *num-recursive-closures-multiplied-out* 0)
 ;; update--part 2
 (set! *num-calls-abstract-analysis-union* 0)
 (set! *num-abstract-expression-bindings-in-analysis-unions* 0)
 (set! *num-calls-create-abstract-analysis* 0)
 (set! *time-in-widen* 0)
 (set! *time-in-l2* 0)
 (set! *time-in-l3* 0)
 (set! *time-in-l4* 0)
 (set! *time-in-l5* 0)
 ; (set! *time-in-subset* 0)
 (set! *time-in-generic-union* 0)
 (set! *time-in-match-us* 0)
 (set! *time-in-union-us* 0)
 (set! *time-in-loop* 0))

(define (instrument-report)
 (format #t "*num-calls-abstract-value-union*=~s~%"
	 *num-calls-abstract-value-union*)
 (format #t "*num-paths-looked-at*=~s~%" *num-paths-looked-at*)
 (format #t "*total-size-paths-looked-at*=~s~%" *total-size-paths-looked-at*)
 (format #t "*num-calls-limit-depth-to*=~s~%" *num-calls-limit-depth-to*)
 (format #t "*num-calls-reduce-depth!*=~s~%" *num-calls-reduce-depth!*)
 (format #t "*num-calls-abstract-value-subset*=~s~%"
	 *num-calls-abstract-value-subset*)
 (format #t "*num-calls-abstract-value-subset-loop?*=~s~%"
	 *num-calls-abstract-value-subset-loop?*)
 (format #t "*num-calls-free-variables*=~s~%" *num-calls-free-variables*)
 ;; update--part 1
 (format #t "*num-abstract-environment-bindings*=~s~%"
	 *num-abstract-environment-bindings*)
 (format
  #t
  "*num-calls-abstract-value-in-matching-abstract-environment-hit*=~s~%"
  *num-calls-abstract-value-in-matching-abstract-environment-hit*)
 (format
  #t
  "*num-calls-abstract-value-in-matching-abstract-environment-miss*=~s~%"
  *num-calls-abstract-value-in-matching-abstract-environment-miss*)
 (format #t "*num-calls-multiply-out-nonrecursive-closure*=~s~%"
	 *num-calls-multiply-out-nonrecursive-closure*)
 (format #t "*num-nonrecursive-closures-multiplied-out*=~s~%"
	 *num-nonrecursive-closures-multiplied-out*)
 (format #t "*num-calls-multiply-out-recursive-closure*=~s~%"
	 *num-calls-multiply-out-recursive-closure*)
 (format #t "*num-recursive-closures-multiplied-out*=~s~%"
	 *num-recursive-closures-multiplied-out*)
 ;; update--part 2
 (format #t "*num-calls-abstract-analysis-union*=~s~%"
	 *num-calls-abstract-analysis-union*)
 (format #t "*num-abstract-expression-bindings-in-analysis-unions*=~s~%"
	 *num-abstract-expression-bindings-in-analysis-unions*)
 (format #t "*num-calls-create-abstract-analysis*=~s~%"
	 *num-calls-create-abstract-analysis*)
 (if (zero? *time-in-widen*)
     (let* ((time-in-difference (- *time-in-widen*
				   *time-in-l2*
				   *time-in-l3*
				   *time-in-l4*
				   *time-in-l5*)))
      (format #t "time in widen: ~s~%" *time-in-widen*)
      (format #t "  time in l2: ~s~%" *time-in-l2*)
      (format #t "  time in l3: ~s~%" *time-in-l3*)
      (format #t "  time in l4: ~s~%" *time-in-l4*)
      (format #t "  time in l5: ~s~%" *time-in-l5*)
      (format #t "  time in difference: ~s~%" time-in-difference))
     (let* ((time-in-difference (- *time-in-widen*
				   *time-in-l2*
				   *time-in-l3*
				   *time-in-l4*
				   *time-in-l5*))
	    (time-in-l2-norm (/ *time-in-l2* *time-in-widen*))
	    (time-in-l3-norm (/ *time-in-l3* *time-in-widen*))
	    (time-in-l4-norm (/ *time-in-l4* *time-in-widen*))
	    (time-in-l5-norm (/ *time-in-l5* *time-in-widen*))
	    (time-in-difference-norm
	     (/ time-in-difference *time-in-widen*)))
      (format #t "time in widen: ~s~%" *time-in-widen*)
      (format #t "  time in l2: ~s (~s)~%" *time-in-l2* time-in-l2-norm)
      (format #t "  time in l3: ~s (~s)~%" *time-in-l3* time-in-l3-norm)
      (format #t "  time in l4: ~s (~s)~%" *time-in-l4* time-in-l4-norm)
      (format #t "  time in l5: ~s (~s)~%" *time-in-l5* time-in-l5-norm)
      (format #t "  time in difference: ~s (~s)~%"
	      time-in-difference time-in-difference-norm)))
 (format #t "time in generic-union: ~s~%" *time-in-generic-union*)
 (format #t "time in subset?: ~s~%" *time-in-subset*)
 (format #t "  time in match-us: ~s~%" *time-in-match-us*)
 (format #t "  time in union-us: ~s~%" *time-in-union-us*)
 (format #t "  time in loop: ~s~%" *time-in-loop*))

(define (abstract-value-size v)
 (let outer ((v v) (vs-above '()))
  (if (memq v vs-above)
      (list 0 0)
      (let inner
	((vs-to-explore
	  (reduce
	   append
	   (map
	    (lambda (u)
	     (cond ((nonrecursive-closure? u)
		    (vector->list (nonrecursive-closure-values u)))
		   ((recursive-closure? u)
		    (vector->list (recursive-closure-values u)))
		   (else '())))
	    v)
	   '()))
	 (num-vs 1)
	 (num-us (length v)))
       (if (null? vs-to-explore)
	   (list num-vs num-us)
	   (let ((result (outer (first vs-to-explore) (cons v vs-above))))
	    (inner (rest vs-to-explore)
		   (+ num-vs (first result))
		   (+ num-us (second result)))))))))

(define (abstract-environment-binding-values b)
 (cons (abstract-environment-binding-abstract-value b)
       (vector->list (abstract-environment-binding-abstract-values b))))

(define (abstract-flow-values bs)
 (reduce append (map abstract-environment-binding-values bs) '()))

(define (abstract-expression-binding-values b)
 (abstract-flow-values (abstract-expression-binding-abstract-flow b)))

(define (abstract-analysis-values bs)
 (reduce append (map abstract-expression-binding-values bs) '()))

(define (collect-total-time-spent-in add-to-collection-variable! thunk)
 (let* ((start (clock-sample))
	(result (thunk))
	(end (clock-sample)))
  (add-to-collection-variable! (- end start))
  result))

(define (collect-time-in-buckets bucket thunk)
 (let ((i (positionq bucket *bucket-names*)))
  (if (eq? #f i)
      (thunk)
      (begin
       (set! *bucket-stack* (cons i *bucket-stack*))
       (let* ((start (clock-sample))
	      (result (thunk))
	      (end (clock-sample))
	      (time-elapsed (- end start)))
	(set! *bucket-stack* (rest *bucket-stack*))
	(when (not (null? *bucket-stack*))
	 (let ((j (first *bucket-stack*)))
	  (vector-set!
	   *time-buckets* j (- (vector-ref *time-buckets* j) time-elapsed))))
	(vector-set!
	 *time-buckets* i (+ (vector-ref *time-buckets* i) time-elapsed))
	result)))))

(define (report-bucket-times)
 (let ((total-time
	(reduce-vector
	 + (map-vector (lambda (x) (if (positive? x) x 0)) *time-buckets*) 0)))
  (format #t "Total time in all buckets: ~a~%"
	  (number->string-of-length-and-precision total-time 8 2))
  (for-each
   (lambda (bucket-name bucket)
    (format
     #t "  time in ~s=~a (~a% total)~%"
     bucket-name
     (number->string-of-length-and-precision bucket 8 2)
     (if (and (positive? bucket) (positive? total-time))
	 (number->string-of-length-and-precision
	  (* 100 (/ bucket total-time)) 6 2)
	 #f)))
   *bucket-names*
   (vector->list *time-buckets*))))

(define (shared-structures-in-v? v)
 (panic "Not (yet) implemented!"))

;;; brownfis -- end of Instrumentation

(define (flow-analysis e bs0)
 (set! *num-updates* 0)
 (time
  "Total flow analysis time: ~a~%"
  (lambda ()
   (let
     ((result
       (collect-time-in-buckets
	'all
	(lambda ()
	 (let loop ((bs (initial-abstract-analysis e bs0)))
	  (when (= *num-updates* 0)
	   (let
	     ((num-expressions (length bs))
	      (num-constant-expressions
	       (count-if
		(lambda (b)
		 (constant-expression?
		  (abstract-expression-binding-expression b)))
		bs))
	      (num-variable-access-expressions
	       (count-if
		(lambda (b)
		 (variable-access-expression?
		  (abstract-expression-binding-expression b)))
		bs))
	      (num-lambda-expressions
	       (count-if
		(lambda (b)
		 (lambda-expression?
		  (abstract-expression-binding-expression b)))
		bs))
	      (num-applications
	       (count-if
		(lambda (b)
		 (application? (abstract-expression-binding-expression b)))
		bs))
	      (num-letrec-expressions
	       (count-if
		(lambda (b)
		 (letrec-expression?
		  (abstract-expression-binding-expression b)))
		bs)))
	    (format #t "Number of expressions: ~s~%" num-expressions)
	    (format #t "  constant expressions: ~s~%" num-constant-expressions)
	    (format #t "  variable-access expressions: ~s~%"
		    num-variable-access-expressions)
	    (format #t "  lambda expressions: ~s~%" num-lambda-expressions)
	    (format #t "  applications: ~s~%" num-applications)
	    (format #t "  letrec expressions: ~s~%" num-letrec-expressions)))
	  (set! *num-updates* (+ *num-updates* 1))
	  (instrument-reset)
	  (reset-cache-performance)
	  (format #t "(Iteration ~s:~%" *num-updates*)
	  ;; debugging
	  (when (= *num-updates* 86)
	   ;; turn everything on...
	   (set! *track-flow-analysis?* #t)
	   (set! *only-updated-bindings?* #t)
	   (set! *debug?* #t)
	   (set! *debug-level* 5))
	  (let* ((bs-prime (time "time-elapsed=~a~%"
				 (lambda () (update-abstract-analysis bs))))
		 (vs (abstract-analysis-values bs-prime))
		 (vs-sizes
		  (map (lambda (v) (first (abstract-value-size v))) vs))
		 (vs-max-size (reduce max vs-sizes 0))
		 (vs-total-size (reduce + vs-sizes 0)))
	   (instrument-report)
	   (report-bucket-times)
	   (report-cache-performance)
	   (if *debug?*
	       (begin
		(format #t "max abstract value size: ~s~%" vs-max-size)
		(format #t "total abstract value size: ~s~%" vs-total-size)
		(format #t "largest abstract-value: ~s)~%"
			(externalize-abstract-value
			 (list-ref vs (positionq vs-max-size vs-sizes)))))
	       (begin
		(format #t "max abstract value size: ~s~%" vs-max-size)
		(format #t "total abstract value size: ~s)~%" vs-total-size)))
	   (when *track-flow-analysis?*
	    (pp (externalize-abstract-analysis
		 (cond
		  (*only-initialized-flows?*
		   (remove-if
		    (lambda (b)
		     (null? (abstract-expression-binding-abstract-flow b)))
		    bs-prime))
		  (*only-updated-bindings?*
		   (remove-if
		    (lambda (b)
		     (let ((e (abstract-expression-binding-expression b)))
		      (abstract-flow=?
		       (expression-abstract-flow e bs)
		       (abstract-expression-binding-abstract-flow b))))
		    bs-prime))
		  (else bs-prime))))
	    (newline))
	   (if (abstract-analysis=? bs bs-prime)
	       (begin
		(format #t "Analysis reached after ~s updates.~%"
			*num-updates*)
		(instrument-report)
		bs)
	       (loop bs-prime))))))))
    (report-bucket-times)
    result))))

;;; brownfis added:

;;; needs work: this is just a temporary fix
(define (compile-time-warning message . us)
 (when *warn?*
  ((if *pp?* pp write) message) (newline)
  (for-each
   (lambda (u)
    ((if *pp?* pp write) (externalize-proto-abstract-value u)) (newline))
   us)))

;;; Abstract basis

(define (abstract-vlad-list? u tags)
 (cond ((null? tags)
	(or (null? u)
	    (and (vlad-pair? u tags)
		 (every (lambda (u) (abstract-vlad-list? u tags))
			(abstract-vlad-cdr u tags)))))
       (else (panic "abstract-vlad-list? doesn't handle tagged values yet!"))))

(define (abstract-vlad-car v tags)
 ;; needs work: church
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take abstract-vlad-car of a non-pair" v))
	(vector-ref (nonrecursive-closure-values v) 0))
       (else (case (first tags)
	      ((forward)
	       (abstract-bundle
		(abstract-vlad-car (abstract-primal v) (rest tags))
		(abstract-vlad-car (abstract-tangent v) (rest tags))))
	      ((reverse)
	       (abstract-*j
		(abstract-vlad-car (abstract-*j-inverse v) (rest tags))))
	      (else (fuck-up))))))

(define (abstract-vlad-cdr v tags)
 ;; needs work: church
 (cond ((null? tags)
	(unless (vlad-pair? v tags)
	 (run-time-error "Attempt to take abstract-vlad-cdr of a non-pair" v))
	(vector-ref (nonrecursive-closure-values v) 1))
       (else (case (first tags)
	      ((forward)
	       (abstract-bundle
		(abstract-vlad-cdr (abstract-primal v) (rest tags))
		(abstract-vlad-cdr (abstract-tangent v) (rest tags))))
	      ((reverse)
	       (abstract-*j
		(abstract-vlad-cdr (abstract-*j-inverse v) (rest tags))))
	      (else (fuck-up))))))

(define (abstract-real? u) (or (real? u) (eq? u 'real)))

(define (abstract-zero u) (panic "abstract-zero not implemented!"))

(define (abstract-plus u) (panic "abstract-plus not implemented!"))

(define (abstract-primal u) (panic "abstract-primal not implemented!"))

(define (abstract-tangent u) (panic "abstract-tangent not implemented!"))

(define (abstract-bundle u1 u2) (panic "abstract-bundle not implemented!"))

(define (abstract-j* u) (panic "abstract-j* not implemented!"))

(define (abstract-*j u) (panic "abstract-*j not implemented!"))

(define (abstract-*j-inverse u) (panic "abstract-*j-inverse not implemented!"))

(define (abstract-unary f s) (lambda (u) (list (f u))))

(define (abstract-unary-real f s)
 (lambda (u)
  (cond
   ((real? u) (list (f u)))
   ((abstract-real? u) '(real))
   (else
    (compile-time-warning (format #f "Argument to ~a might be invalid" s) u)
    '()))))

(define (abstract-unary-predicate f s)
 (lambda (u) (list (if (f u) vlad-true vlad-false))))

(define (abstract-unary-real-predicate f s)
 (lambda (u)
  (cond
   ((real? u) (list (if (f u) vlad-true vlad-false)))
   ((abstract-real? u) (list vlad-true vlad-false))
   (else
    (compile-time-warning (format #f "Argument to ~a might be invalid" s) u)
    '()))))

(define (abstract-binary f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v1 (abstract-vlad-car u '())) (v2 (abstract-vlad-cdr u '())))
     (reduce abstract-value-union
	     (map (lambda (u1)
		   (reduce abstract-value-union
			   (map (lambda (u2) (list (f u1 u2))) v2)
			   (empty-abstract-value)))
		  v1)
	     (empty-abstract-value))))
   (else (compile-time-warning (format #f "Argument to ~a is not a pair" s) u)
	 '()))))

(define (abstract-binary-real f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v1 (abstract-vlad-car u '())) (v2 (abstract-vlad-cdr u '())))
     (reduce
      abstract-value-union
      (map
       (lambda (u1)
	(reduce
	 abstract-value-union
	 (map
	  (lambda (u2)
	   (cond ((and (real? u1) (real? u2)) (list (f u1 u2)))
		 ((and (abstract-real? u1) (abstract-real? u2)) '(real))
		 (else (compile-time-warning
			(format #f "Argument to ~a might be invalid" s) u)
		       '())))
	  v2)
	 (empty-abstract-value)))
       v1)
      (empty-abstract-value))))
   (else (compile-time-warning (format #f "Argument to ~a is not a pair" s) u)
	 '()))))

(define (abstract-binary-real-predicate f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v1 (abstract-vlad-car u '())) (v2 (abstract-vlad-cdr u '())))
     (reduce
      abstract-value-union
      (map
       (lambda (u1)
	(reduce
	 abstract-value-union
	 (map
	  (lambda (u2)
	   (cond ((and (real? u1) (real? u2))
		  (list (if (f u1 u2) vlad-true vlad-false)))
		 ((and (abstract-real? u1) (abstract-real? u2))
		  (list vlad-true vlad-false))
		 (else (compile-time-warning
			(format #f "Argument to ~a might be invalid" s) u)
		       '())))
	  v2)
	 (empty-abstract-value)))
       v1)
      (empty-abstract-value))))
   (else (compile-time-warning (format #f "Argument to ~a is not a pair" s) u)
	 '()))))

(define (abstract-ternary f s)
 (lambda (u123)
  (cond ((vlad-pair? u123 '())
	 (let ((v1 (abstract-vlad-car u123 '()))
	       (v23 (abstract-vlad-cdr u123 '())))
	  (reduce
	   abstract-value-union
	   (map
	    (lambda (u1)
	     (reduce
	      abstract-value-union
	      (map
	       (lambda (u23)
		(cond ((vlad-pair? u23 '())
		       (let ((v2 (abstract-vlad-car u23 '()))
			     (v3 (abstract-vlad-cdr u23 '())))
			(reduce
			 abstract-value-union
			 (map
			  (lambda (u2)
			   (reduce
			    abstract-value-union
			    (map
			     (lambda (u3) (list (f u1 u2 u3)))
			     v3)
			    (empty-abstract-value)))
			  v2)
			 (empty-abstract-value))))
		      (else
		       (compile-time-warning
			(format #t "Argument to ~a might not be a triple" s)
			u123))))
	       v23)
	      (empty-abstract-value)))
	    v1)
	   (empty-abstract-value))))
	(else (compile-time-warning
	       (format #f "Argument to ~a is not a triple" s) u123)
	      '()))))

;;; Pretty printer for abstract

(define-structure union proto-abstract-values)

(define (externalize-proto-abstract-value u)
 (cond ((vlad-true? u) #t)
       ((vlad-false? u) #f)
       ((abstract-real? u) u)
       ;; needs work: How to properly distinguish between abstract lists/tuples
       ;; v = (cons v1 v2)
       ((vlad-pair? u '())
	(let ((v1 (abstract-vlad-car u '()))
	      (v2 (abstract-vlad-cdr u '())))
	 (cons (externalize-abstract-value v1)
	       (externalize-abstract-value v2))))
       ((nonrecursive-closure? u)
	(list 'nonrecursive-closure
	      (externalize-abstract-environment
	       (nonrecursive-closure-variables u)
	       (nonrecursive-closure-values u))
	      (abstract->concrete
	       (new-lambda-expression
		(nonrecursive-closure-variable u)
		(nonrecursive-closure-body u)))))
       ((recursive-closure? u)
	(list 'recursive-closure
	      (externalize-abstract-environment
	       (recursive-closure-variables u) (recursive-closure-values u))
	      (vector->list
	       (map-vector (lambda (x1 e) (list x1 (abstract->concrete e)))
			   (recursive-closure-procedure-variables u)
			   (recursive-closure-procedure-lambda-expressions u)))
	      (vector-ref (recursive-closure-procedure-variables u)
			  (recursive-closure-index u))))
       ((null? u) u)
       ((list? u)
	(run-time-error (format #f "Not a proto-abstract-value: ~a" u)))
       (else (externalize u))))

(define (externalize-abstract-value v)
 (let ((v (uncyclicize-abstract-value v)))
  (cond ((integer? v) `((up ,v)))
	((up? v) v)
	((list? v)
	 (cond ((null? v) (list->vector v))
	       ((= (length v) 1) (externalize-proto-abstract-value (first v)))
	       (else (make-union (map externalize-proto-abstract-value v)))))
	(else (panic (format #f "Not an abstract value: ~s" v))))))

(define (externalize-abstract-environment xs vs)
 ;; debugging
 (when (not (= (length xs) (vector-length vs)))
  (format #t "xs=~s~%" xs)
  (format #t "vs=~s~%" (map-vector externalize-abstract-value vs))
  (panic "xs and vs should be of same length!"))
 (map (lambda (x v) (list x (externalize-abstract-value v)))
      xs (vector->list vs)))

(define (externalize-abstract-environment-binding xs b)
 (list (externalize-abstract-environment
	xs (abstract-environment-binding-abstract-values b))
       (externalize-abstract-value
	(abstract-environment-binding-abstract-value b))))

(define (externalize-abstract-flow xs bs)
 (map (lambda (b) (externalize-abstract-environment-binding xs b)) bs))

(define (externalize-abstract-expression-binding b)
 (list (abstract->concrete (abstract-expression-binding-expression b))
       (externalize-abstract-flow
	(free-variables (abstract-expression-binding-expression b))
	(abstract-expression-binding-abstract-flow b))))

(define (externalize-abstract-analysis bs)
 (map externalize-abstract-expression-binding bs))

;;; end stuff that belongs to brownfis

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

(define (unary-predicate f s)
 (lambda (x) (if (f (dereference x)) vlad-true vlad-false)))

(define (unary-real f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x))))

(define (unary-real-predicate f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (f x) vlad-true vlad-false))))

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

(define (binary-real-predicate f s)
 (lambda (x)
  (let ((x (dereference x)))
   (unless (vlad-pair? x '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (dereference (vlad-car x '())))
	 (x2 (dereference (vlad-cdr x '()))))
    (unless (and (real? x1) (real? x2))
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (if (f x1 x2) vlad-true vlad-false)))))

(define (ternary f s)
 (lambda (x)
  (let ((x123 (dereference x)))
   (unless (vlad-pair? x123 '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (vlad-car x123 '())) (x23 (dereference (vlad-cdr x123 '()))))
    (unless (vlad-pair? x23 '())
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (f x1 (vlad-car x23 '()) (vlad-cdr x23 '()))))))

(define (define-primitive-procedure
	 x procedure abstract-procedure forward reverse)
 (set! *value-bindings*
       (cons (make-value-binding
	      x (make-primitive-procedure
		 x procedure abstract-procedure forward reverse 0))
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
       (if *church?*
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
       (if *church?*
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
 (define-primitive-procedure '+
  (binary-real + "+")
  (abstract-binary-real + "+")
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
  (abstract-binary-real - "-")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (- x1 x2) (- (perturbation x1) (perturbation x2)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (- x1 x2))
	   (lambda ((sensitivity y))
	    (cons '() (cons (sensitivity y) (- 0 (sensitivity y)))))))))
 (define-primitive-procedure '*
  (binary-real * "*")
  (abstract-binary-real * "*")
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
  (abstract-binary-real divide "/")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle
      (/ x1 x2)
      (/ (- (* x2 (perturbation x1)) (* x1 (perturbation x2))) (* x2 x2)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (/ x1 x2))
	   (lambda ((sensitivity y))
	    (cons '()
		  (cons (/ (sensitivity y) x2)
			(- 0 (/ (* x1 (sensitivity y)) (* x2 x2))))))))))
 (define-primitive-procedure 'sqrt
  (unary-real sqrt "sqrt")
  (abstract-unary-real sqrt "sqrt")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (sqrt x) (/ (perturbation x) (* 2 (sqrt x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (sqrt x))
	   (lambda ((sensitivity y))
	    (cons '() (/ (sensitivity y) (* 2 (sqrt x)))))))))
 (define-primitive-procedure 'exp
  (unary-real exp "exp")
  (abstract-unary-real exp "exp")
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
  (abstract-unary-real log "log")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (log x) (/ (perturbation x) x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (log x))
	   (lambda ((sensitivity y)) (cons '() (/ (sensitivity y) x)))))))
 (define-primitive-procedure 'sin
  (unary-real sin "sin")
  (abstract-unary-real sin "sin")
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
  (abstract-unary-real cos "cos")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (cos x) (- 0 (* (sin x) (perturbation x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (cos x))
	   (lambda ((sensitivity y))
	    (cons '() (- 0 (* (sin x) (sensitivity y)))))))))
 (define-primitive-procedure 'atan
  (binary-real atan "atan")
  (abstract-binary-real atan "atan")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (atan x2 x1)
	     (/ (- (* x1 (perturbation x2)) (* x2 (perturbation x1)))
		(+ (* x1 x1) (* x2 x2))))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (atan x2 x1))
	   (lambda ((sensitivity y))
	    (cons '()
		  (cons (- 0
			   (/ (* x2 (sensitivity y))
			      (+ (* x1 x1) (* x2 x2))))
			(/ (* x1 (sensitivity y))
			   (+ (* x1 x1) (* x2 x2))))))))))
 (define-primitive-procedure '=
  (binary-real-predicate = "=")
  (abstract-binary-real-predicate = "=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))) (bundle (= x1 x2) '())))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (= x1 x2))
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure '<
  (binary-real-predicate < "<")
  (abstract-binary-real-predicate < "<")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))) (bundle (< x1 x2) '())))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (< x1 x2))
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure '>
  (binary-real-predicate > ">")
  (abstract-binary-real-predicate > ">")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))) (bundle (> x1 x2) '())))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (> x1 x2))
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure '<=
  (binary-real-predicate <= "<=")
  (abstract-binary-real-predicate <= "<=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))) (bundle (<= x1 x2) '())))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (<= x1 x2))
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure '>=
  (binary-real-predicate >= ">=")
  (abstract-binary-real-predicate >= ">=")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))) (bundle (>= x1 x2) '())))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (>= x1 x2))
	   (lambda ((sensitivity y)) (cons '() (cons (zero x1) (zero x2))))))))
 (define-primitive-procedure 'zero?
  (unary-real-predicate zero? "zero?")
  (abstract-unary-real-predicate zero? "zero?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (zero? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?")
  (abstract-unary-real-predicate positive? "positive?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (positive? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (positive? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?")
  (abstract-unary-real-predicate negative? "negative?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (negative? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (negative? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'null?
  (unary-predicate null? "null?")
  (abstract-unary-predicate null? "null?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (null? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'boolean?
  (unary-predicate vlad-boolean? "boolean?")
  (abstract-unary-predicate vlad-boolean? "boolean?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (boolean? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'real?
  (unary-predicate real? "real?")
  (abstract-unary-predicate real? "real?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (real? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'pair?
  (unary-predicate (lambda (x) (vlad-pair? x '())) "pair?")
  (abstract-unary-predicate (lambda (x) (vlad-pair? x '())) "pair?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (pair? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?")
  (abstract-unary-predicate vlad-procedure? "procedure?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (procedure? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (procedure? x))
	   (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'forward?
  (unary-predicate vlad-forward? "forward?")
  (abstract-unary-predicate vlad-forward? "forward?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (forward? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'reverse?
  (unary-predicate vlad-reverse? "reverse?")
  (abstract-unary-predicate vlad-reverse? "reverse?")
  '(lambda ((forward x))
    (let ((x (primal (forward x)))) (bundle (reverse? x) '())))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (reverse? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (unless *church?*
  (define-primitive-procedure 'if-procedure
   (ternary (lambda (x1 x2 x3) (if (dereference x1) x2 x3)) "if-procedure")
   (abstract-ternary
    (lambda (x1 x2 x3)
     (unless (boolean? (dereference x1))
      (run-time-error
       (format #f "Argument to if-procedure not boolean: ") x1))
     (if (dereference x1) x2 x3))
    "if-procedure")
   '(lambda ((forward x))
     (let (((cons* x1 x2 x3) (primal (forward x)))
	   ((cons* (perturbation x1) (perturbation x2) (perturbation x3))
	    (tangent (forward x))))
      (if-procedure
       x1 (bundle x2 (perturbation x2)) (bundle x3 (perturbation x3)))))
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
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write")
  (abstract-unary (lambda (x)
		   ((if *pp?* pp write) (externalize-proto-abstract-value x))
		   (newline)
		   x)
		  "write")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (write x) (perturbation x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write x))
	   (lambda ((sensitivity y)) (cons '() (sensitivity y)))))))
 (define-primitive-procedure 'zero
  (unary zero "zero")
  (abstract-unary abstract-zero "zero")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (zero x) (zero (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'plus
  (binary plus "plus")
  (abstract-binary abstract-plus "plus")
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons (perturbation x1) (perturbation x2)) (tangent (forward x))))
     (bundle (plus x1 x2) (plus (perturbation x1) (perturbation x2)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (plus x1 x2))
	   (lambda ((sensitivity y))
	    (cons '() (cons (sensitivity y) (sensitivity y))))))))
 (define-primitive-procedure 'primal
  (unary primal "primal")
  (abstract-unary abstract-primal "primal")
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  ((perturbation x-forward) (tangent (forward x-forward))))
     (bundle (primal x-forward) (primal (perturbation x-forward)))))
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward))))
     (cons (*j (primal x-forward))
	   (lambda ((sensitivity y)) (cons '() (j* (sensitivity y))))))))
 (define-primitive-procedure 'tangent
  (unary tangent "tangent")
  (abstract-unary abstract-tangent "tangent")
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
  (abstract-binary abstract-bundle "bundle")
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
 (define-primitive-procedure 'j*
  (unary j* "j*")
  (abstract-unary abstract-j* "j*")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (j* x) (j* (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (j* x))
	   (lambda ((sensitivity (forward y)))
	    (cons '() (primal (sensitivity (forward y)))))))))
 (define-primitive-procedure '*j
  (unary *j "*j")
  (abstract-unary abstract-*j "*j")
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
  (abstract-unary abstract-*j-inverse "*j-inverse")
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
