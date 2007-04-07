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
;;;  1. zero, plus, primal, tangent, bundle, *j, and *j-inverse should be
;;;     lazy.
;;;  2. does making plus lazy eliminate the need to special case for generic
;;;     zeros?
;;;  3. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  4. We removed -wizard because macro expansion required (ignore) and
;;;     (consvar x1 x2). Someday we need to put it back in.
;;;  5. For now, we don't optimize away null tangents.

;;; Church Pairs
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

(define-structure application callee argument free-variable-indices)

(define-structure letrec-expression
 bodies-free-variables
 bodies-free-variable-indices		;vector
 body-free-variables
 body-free-variable-indices		;vector
 procedure-variables
 argument-variables
 bodies
 body)

(define-structure cons-expression tags car cdr free-variable-indices)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 name procedure abstract-procedure forward reverse meter)

;;; The index-{expression,environment} slots are used solely to index
;;; aggregate proto abstract values during flow analysis.

(define-structure nonrecursive-closure
 variables
 values					;vector
 variable
 body
 index-expression
 index-environment)			;vector

(define-structure recursive-closure
 variables
 values					;vector
 procedure-variables			;vector
 argument-variables			;vector
 bodies					;vector
 index
 index-expression
 index-environment)			;vector

(define-structure bundle primal tangent)

(define-structure reverse-tagged-value primal)

(define-structure tagged-pair
 tags
 car
 cdr
 index-expression
 index-environment)			;vector

(define-structure forward-cache-entry primal? primal tangent? tangent forward)

(define-structure reverse-cache-entry primal reverse)

;;; A proto abstract value is
;;; - (),
;;; - #t,
;;; - #f,
;;; - a real,
;;; - real,
;;; - a primitive procedure,
;;; - a nonrecursive closure,
;;; - a recursive closure,
;;; - a bundle, or
;;; - a tagged pair.

;;; An abstract value is a list of proto abstract values or an up.

(define-structure up index)

;;; A flow is a list of environment bindings. An analysis is a list of
;;; expression bindings. All of the environments in the environment bindings of
;;; a given flow must map the same set of variables, namely precisely the free
;;; variables in the expression binding that contains that flow. Thus we
;;; represent the environment in an environment binding as a vector of values
;;; in the canonical order of the free variables.

;;; Note that both the abstract values in the abstract environment of an
;;; abstract environment binding as well as the abstract value in an
;;; abstract environment binding must be closed, i.e. they may not contain
;;; free deBruin references because there are no enclosing abstract values.

(define-structure environment-binding values value)

(define-structure expression-binding expression flow)

;;; Variables

(define *gensym* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *forward-cache* '())

(define *reverse-cache* '())

(define *num-updates* 0)

(define *lookup-misses* 0)

(define *start-time* #f)

(define *expression-list* '())

;;; Parameters

(define *include-path* '())

(define *church-booleans?* #f)

(define *church-pairs?* #f)

(define *letrec-as-y?* #f)

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

(define *anal?* #t)

(define *pp?* #f)

(define *x* #f)

(define *memoized?* #f)

(define *flow-size-limit* #f)

(define *real-limit* #f)

(define *closure-limit* #f)

(define *closure-depth-limit* #f)

(define *bundle-limit* #f)

(define *bundle-depth-limit* #f)

(define *tagged-pair-limit* #f)

(define *tagged-pair-depth-limit* #f)

(define *warn?* #t)

(define *expression-equality* 'structural)

(define *method-for-removing-redundant-proto-abstract-values* 'structural)

;;; Procedures

;;; Error Handing

(define (compile-time-warning message . us)
 (when *warn?*
  (display message)
  (newline)
  (for-each
   (lambda (u)
    ((if *pp?* pp write) (externalize-proto-abstract-value u)) (newline))
   us))
 (empty-abstract-value))

(define (compile-time-error message . arguments)
 (apply format stderr-port message arguments)
 (newline stderr-port)
 (exit -1))

(define (run-time-error message . vs)
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
 (newline stderr-port)
 (for-each (lambda (v)
	    ((if *pp?* pp write) (externalize v) stderr-port)
	    (newline stderr-port))
	   vs)
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

;;; VLAD datastructures

(define vlad-true #t)

(define vlad-false #f)

(define (vlad-true? v)
 (if *church-booleans?*
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
 (if *church-booleans?*
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
 (or (and (closure? v)
	  (not (null? (closure-tags v)))
	  (eq? (first (closure-tags v)) 'forward))
     (bundle? v)
     (and (not *church-pairs?*)
	  (tagged-pair? v)
	  (not (null? (tagged-pair-tags v)))
	  (eq? (first (tagged-pair-tags v)) 'forward))))

(define (vlad-reverse? v)
 (or (and (closure? v)
	  (not (null? (closure-tags v)))
	  (eq? (first (closure-tags v)) 'reverse))
     (reverse-tagged-value? v)
     (and (not *church-pairs?*)
	  (tagged-pair? v)
	  (not (null? (tagged-pair-tags v)))
	  (eq? (first (tagged-pair-tags v)) 'reverse))))

(define (vlad-pair? v tags)
 (if *church-pairs?*
     (if (null? tags)
	 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
	 (and
	  (nonrecursive-closure? v)
	  (not (vlad-forward? v))
	  (not (vlad-reverse? v))
	  (= (length (nonrecursive-closure-variables v)) 2)
	  (let*? (nonrecursive-closure-body v))
	  (= (length (let*-variables (nonrecursive-closure-body v))) 2)
	  (application?
	   (first (let*-expressions (nonrecursive-closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee
	    (first (let*-expressions (nonrecursive-closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee
	     (first (let*-expressions (nonrecursive-closure-body v)))))
	   (nonrecursive-closure-variable v))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument
	    (first (let*-expressions (nonrecursive-closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-argument
	     (first (let*-expressions (nonrecursive-closure-body v)))))
	   (first (nonrecursive-closure-variables v)))
	  (application?
	   (second (let*-expressions (nonrecursive-closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-callee
	    (second (let*-expressions (nonrecursive-closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-callee
	     (second (let*-expressions (nonrecursive-closure-body v)))))
	   (first (let*-variables (nonrecursive-closure-body v))))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (application-argument
	    (second (let*-expressions (nonrecursive-closure-body v)))))
	  (variable=?
	   (variable-access-expression-variable
	    (application-argument
	     (second (let*-expressions (nonrecursive-closure-body v)))))
	   (second (nonrecursive-closure-variables v)))
	  ;; Technically not needed since in ANF.
	  (variable-access-expression?
	   (let*-body (nonrecursive-closure-body v)))
	  (variable=? (variable-access-expression-variable
		       (let*-body (nonrecursive-closure-body v)))
		      (second (let*-variables (nonrecursive-closure-body v)))))
	 (case (first tags)
	  ((forward) (vlad-pair? (primal v) (rest tags)))
	  ((reverse) (vlad-pair? (*j-inverse v) (rest tags)))
	  (else (internal-error))))
     (and (tagged-pair? v) (equal? (tagged-pair-tags v) tags))))

(define (vlad-car v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take car of a non-pair" v))
 (if *church-pairs?*
     (cond ((null? tags) (vector-ref (nonrecursive-closure-values v) 0))
	   (else (case (first tags)
		  ((forward) (bundle (vlad-car (primal v) (rest tags))
				     (vlad-car (tangent v) (rest tags))))
		  ((reverse) (*j (vlad-car (*j-inverse v) (rest tags))))
		  (else (internal-error)))))
     (tagged-pair-car v)))

(define (vlad-cdr v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take cdr of a non-pair" v))
 (if *church-pairs?*
     (cond ((null? tags) (vector-ref (nonrecursive-closure-values v) 1))
	   (else (case (first tags)
		  ((forward) (bundle (vlad-cdr (primal v) (rest tags))
				     (vlad-cdr (tangent v) (rest tags))))
		  ((reverse) (*j (vlad-cdr (*j-inverse v) (rest tags))))
		  (else (internal-error)))))
     (tagged-pair-cdr v)))

(define (create-tagged-pair tags v1 v2)
 ;; We intentionally don't give the index-expression and index-environment
 ;; since these are only used during flow analysis.
 (make-tagged-pair tags v1 v2 #f #f))

(define (vlad-cons v1 v2)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (if *church-pairs?*
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
		  (new-variable-access-expression 'x2)))
       ;; needs work: to fill in index-expression
       #f
       vs))
     (create-tagged-pair '() v1 v2)))

(define (listify xs tags)
 (if *church-pairs?*
     (if (null? tags)
	 (let loop ((xs xs))
	  (if (null? xs) '() (vlad-cons (first xs) (loop (rest xs)))))
	 (case (first tags)
	  ((forward) (bundle (listify (map primal xs) (rest tags))
			     (listify (map tangent xs) (rest tags))))
	  ((reverse) (*j (listify (map *j-inverse xs) (rest tags))))
	  (else (internal-error))))
     (let loop ((xs xs))
      (if (null? xs)
	  (let loop ((tags tags))
	   (if (null? tags)
	       '()
	       ((case (first tags)
		 ((forward) j*)
		 ((reverse) *j)
		 (else (internal-error)))
		(loop (rest tags)))))
	  (create-tagged-pair tags (first xs) (loop (rest xs)))))))

(define (vlad-procedure? v)
 (and (or (primitive-procedure? v) (closure? v))
      (not (vlad-pair? v '()))
      (not (vlad-true? v))
      (not (vlad-false? v))))

(define (vlad-equal? v1 v2)
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (and (not *church-booleans?*)
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
			(recursive-closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (vlad-equal? (bundle-primal v1) (bundle-primal v2))
	  (vlad-equal? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (vlad-equal? (reverse-tagged-value-primal v1)
		       (reverse-tagged-value-primal v2)))
     (and (not *church-pairs?*)
	  (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (vlad-equal? (tagged-pair-car v1) (tagged-pair-car v2))
	  (vlad-equal? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))))

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
	 (else (internal-error))))
       (else (internal-error))))

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
 (unless (perturbation-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ((perturbation) (second x))
   ((alpha) (loop (second x)))
   (else (internal-error)))))

(define (unforwardify x)
 (unless (forward-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ((forward) (second x))
   ((alpha) (loop (second x)))
   (else (internal-error)))))

(define (unsensitivityify x)
 (unless (sensitivity-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ((sensitivity) (second x))
   ((alpha) (loop (second x)))
   (else (internal-error)))))

(define (unbackpropagatorify x)
 (unless (backpropagator-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ((backpropagator) (second x))
   ((alpha) (loop (second x)))
   (else (internal-error)))))

(define (unreverseify x)
 (unless (reverse-variable? x) (internal-error))
 (let loop ((x x))
  (unless (pair? x) (internal-error))
  (case (first x)
   ((reverse) (second x))
   ((alpha) (loop (second x)))
   (else (internal-error)))))

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

(define (new-application e1 e2) (make-application e1 e2 #f))

(define (create-application bs tags e . es)
 (new-application e (make-cons* bs tags es)))

(define (new-let* xs es e)
 (if (null? xs)
     e
     (new-application
      ;; needs work
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

(define (create-cons-expression tags e1 e2)
 (make-cons-expression tags e1 e2 #f))

(define (new-cons-expression e1 e2) (create-cons-expression '() e1 e2))

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
 `(let* (,@(if *church-pairs?*
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
	    (create-cons-expression
	     (cons-expression-tags e) (second result1) (second result2)))))
    (else (internal-error))))))

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
	 ((cons-expression? e)
	  (union-variables (loop (cons-expression-car e))
			   (loop (cons-expression-cdr e))))
	 (else (internal-error))))))

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
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))
		     #f))
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
   (create-cons-expression (cons-expression-tags e)
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
	   (inner (first result)
		  (rest xs1)
		  (rest xs2)
		  (rest es)
		  (cons (make-variable-binding
			 (first xs1)
			 (new-lambda-expression
			  (first xs2) (anf-result result)))
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
		   (create-cons-expression
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
	(create-cons-expression (cons-expression-tags e)
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
	(unionp vlad-equal?
		(constants-in (application-callee e))
		(constants-in (application-argument e))))
       ((letrec-expression? e)
	(unionp vlad-equal?
		(reduce (lambda (vs1 vs2) (unionp vlad-equal? vs1 vs2))
			(map constants-in (letrec-expression-bodies e))
			'())
		(constants-in (letrec-expression-body e))))
       ((cons-expression? e)
	(unionp vlad-equal?
		(constants-in (cons-expression-car e))
		(constants-in (cons-expression-cdr e))))
       (else (internal-error))))

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
       ((cons-expression? e)
	(create-cons-expression (cons-expression-tags e)
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
       ;; needs work: flow analysis requires tagged pairs to have
       ;;             index-expression and index-environment slots
       ((pair? v) (vlad-cons (internalize (car v)) (internalize (cdr v))))
       (else (internal-error))))

(define (macro-expand e)
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
		(every (lambda (b)
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
    (else `(let (,(first (second e))) (let* ,(rest (second e)) ,(third e))))))
  ((if)
   (unless (= (length e) 4) (compile-time-error "Invalid expression: ~s" e))
   (if *church-booleans?*
       `((,(second e) (cons (lambda () ,(third e)) (lambda () ,(fourth e)))))
       ;; needs work: to ensure that you don't shadow if-procedure
       `((if-procedure
	  ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))))
  ;; needs work: to ensure that you don't shadow cons-procedure
  ((cons)
   (unless (= (length e) 3) (compile-time-error "Invalid expression: ~s" e))
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
	 (else (let ((x (gensym)))
		`(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e)))))))))
  (else (case (length (rest e))
	 ((0) `(,(first e) (cons* ,@(rest e))))
	 ((1) e)
	 (else `(,(first e) (cons* ,@(rest e))))))))

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
     ((cons) (cond (*church-pairs?* (loop (macro-expand e) xs))
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
     (if *church-pairs?*
	 (concrete->abstract-expression (macro-expand e))
	 (new-cons-expression (concrete->abstract-expression (second e))
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
	(e (copy-propagate (anf-convert (alpha-convert e (free-variables e)))))
	(xs (free-variables e))
	(bs (append bs *value-bindings*)))
  (list
   (index #f xs e)
   (map (lambda (x)
	 (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))
	xs))))

(define (abstract-parse e)
 (let* ((e (concrete->abstract-expression e))
	(bs (map (lambda (v) (make-value-binding (gensym) v))
		 (constants-in e)))
	(e (constant-convert bs e))
	(e (if #f			;debugging
	       (copy-propagate
		(anf-convert (alpha-convert e (free-variables e))))
	       (alpha-convert e (free-variables e))))
	(xs (free-variables e))
	(bs (append bs *value-bindings*)))
  (list
   (abstract-index (lambda (x)
		    (unless (memp variable=? x xs) (internal-error))
		    (positionp variable=? x xs))
		   e)
   (map (lambda (x)
	 (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))
	xs))))

;;; AD

(define (zero x)
 (cond ((null? x) '())
       ((and (not *church-booleans?*) (vlad-boolean? x)) '())
       ((real? x) 0)
       ((primitive-procedure? x) '())
       ((closure? x) (listify (map zero (base-values x)) (closure-tags x)))
       ((bundle? x)
	(make-bundle (zero (bundle-primal x)) (zero (bundle-tangent x))))
       ((reverse-tagged-value? x)
	(make-reverse-tagged-value (zero (reverse-tagged-value-primal x))))
       ((and (not *church-pairs?*) (tagged-pair? x))
	(create-tagged-pair (tagged-pair-tags x)
			    (zero (vlad-car x (tagged-pair-tags x)))
			    (zero (vlad-cdr x (tagged-pair-tags x)))))
       (else (internal-error))))

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

(define (plus-internal x1 x2)
 (cond
  ((vlad-forward? x1)
   (bundle (plus-internal (primal x1) (primal x2))
	   (plus-internal (tangent x1) (tangent x2))))
  ((vlad-reverse? x1) (*j (plus-internal (*j-inverse x1) (*j-inverse x2))))
  ((null? x1) '())
  ((real? x1) (+ x1 x2))
  (else (vlad-cons (plus-internal (vlad-car x1 '()) (vlad-car x2 '()))
		   (plus-internal (vlad-cdr x1 '()) (vlad-cdr x2 '()))))))

(define (plus x1 x2)
 (when *anal?*
  (unless (conform? x1 x2)
   (run-time-error "The arguments to plus are nonconformant" x1 x2)))
 (plus-internal x1 x2))

;;; Base variables

(define (closure? u) (or (nonrecursive-closure? u) (recursive-closure? u)))

(define (closure-variables u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-variables u))
       ((recursive-closure? u) (recursive-closure-variables u))
       (else (internal-error))))

(define (closure-tags u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-tags u))
       ((recursive-closure? u) (recursive-closure-tags u))
       (else (internal-error))))

(define (forward-uptag-variables xs1 xs2)
 (map (lambda (x1)
       (unless (one (lambda (x2) (variable=? x1 (unforwardify x2))) xs2)
	(internal-error))
       (find-if (lambda (x2) (variable=? x1 (unforwardify x2))) xs2))
      xs1))

(define (reverse-uptag-variables xs1 xs2)
 (map (lambda (x1)
       (unless (one (lambda (x2) (variable=? x1 (lax-unreverseify x2))) xs2)
	(internal-error))
       (find-if (lambda (x2) (variable=? x1 (lax-unreverseify x2))) xs2))
      xs1))

(define (base-variables x)
 (cond
  ((primitive-procedure? x) '())
  ((closure? x)
   (let ((xs (closure-variables x)))
    (if (null? (closure-tags x))
	xs
	(case (first (closure-tags x))
	 ((forward) (forward-uptag-variables (base-variables (primal x)) xs))
	 ((reverse)
	  (reverse-uptag-variables (base-variables (*j-inverse x)) xs))
	 (else (internal-error))))))
  (else (internal-error))))

(define (base-values x)
 (let ((xs (closure-variables x)) (vs (closure-values x)))
  (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
       (base-variables x))))

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
	 (else (internal-error))))))
  (else (internal-error))))

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
	      (else (internal-error))))))
       (else (internal-error))))

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
       (else (internal-error))))))

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
       (else (internal-error))))))

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
       ((cons-expression? e)
	(create-cons-expression (cons 'forward (cons-expression-tags e))
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
   (unless (and (not (null? (cons-expression-tags e)))
		(eq? (first (cons-expression-tags e)) 'forward))
    (internal-error))
   (create-cons-expression
    (rest (cons-expression-tags e))
    (forward-transform-inverse (cons-expression-car e))
    (forward-transform-inverse (cons-expression-cdr e))))
  (else (internal-error))))

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
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((and (not *church-booleans?*) (vlad-boolean? x-forward))
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
			primal
			(nonrecursive-closure-values x-forward))
		       x
		       (index x xs (lambda-expression-body e))
		       ;; needs work: tangent of bundle gives the
		       ;;             index-expression and index-environment of
		       ;;             the primal
		       (nonrecursive-closure-index-expression x-forward)
		       (nonrecursive-closure-index-environment x-forward))))))
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
		       (recursive-closure-index x-forward)
		       ;; needs work: tangent of bundle gives the
		       ;;             index-expression and index-environment of
		       ;;             the primal
		       (recursive-closure-index-expression x-forward)
		       (recursive-closure-index-environment x-forward))))))
	       ((bundle? x-forward) (bundle-primal x-forward))
	       ((reverse-tagged-value? x-forward)
		(run-time-error
		 "Attempt to take primal of a non-forward value" x-forward))
	       ((and (not *church-pairs?*) (tagged-pair? x-forward))
		(unless (and
			 (not (null? (tagged-pair-tags x-forward)))
			 (eq? (first (tagged-pair-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take primal of a non-forward value" x-forward))
		;; needs work: tangent of bundle gives the index-expression
		;;             and index-environment of the primal
		(create-tagged-pair (rest (tagged-pair-tags x-forward))
				    (primal (tagged-pair-car x-forward))
				    (primal (tagged-pair-cdr x-forward))))
	       (else (internal-error))))
	     (forward-cache-entry
	      (find-if (lambda (forward-cache-entry)
			(vlad-equal?
			 (forward-cache-entry-forward forward-cache-entry)
			 x-forward))
		       *forward-cache*)))
       (when *memoized?*
	(cond
	 (forward-cache-entry
	  (when (forward-cache-entry-primal? forward-cache-entry)
	   (internal-error))
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
	      (cond
	       ((null? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((and (not *church-booleans?*) (vlad-boolean? x-forward))
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((real? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((primitive-procedure? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((closure? x-forward)
		(unless (and (not (null? (closure-tags x-forward)))
			     (eq? (first (closure-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take tangent of a non-forward value" x-forward))
		(if (some (lambda (b)
			   (vlad-equal? x-forward
					(primitive-procedure-forward
					 (value-binding-value b))))
			  *value-bindings*)
		    '()
		    (listify (map tangent (base-values x-forward))
			     (rest (closure-tags x-forward)))))
	       ((bundle? x-forward) (bundle-tangent x-forward))
	       ((reverse-tagged-value? x-forward)
		(run-time-error
		 "Attempt to take tangent of a non-forward value" x-forward))
	       ((and (not *church-pairs?*) (tagged-pair? x-forward))
		(unless (and
			 (not (null? (tagged-pair-tags x-forward)))
			 (eq? (first (tagged-pair-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take tangent of a non-forward value" x-forward))
		;; needs work: tangent of bundle gives the index-expression and
		;;             index-environment of the primal
		(create-tagged-pair (rest (tagged-pair-tags x-forward))
				    (tangent (tagged-pair-car x-forward))
				    (tangent (tagged-pair-cdr x-forward))))
	       (else (internal-error))))
	     (forward-cache-entry
	      (find-if (lambda (forward-cache-entry)
			(vlad-equal?
			 (forward-cache-entry-forward forward-cache-entry)
			 x-forward))
		       *forward-cache*)))
       (when *memoized?*
	(cond
	 (forward-cache-entry
	  (when (forward-cache-entry-tangent? forward-cache-entry)
	   (internal-error))
	  (set-forward-cache-entry-tangent?! forward-cache-entry #t)
	  (set-forward-cache-entry-tangent! forward-cache-entry result))
	 (else (set! *forward-cache*
		     (cons (make-forward-cache-entry #f #f #t result x-forward)
			   *forward-cache*)))))
       result))))

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
      (else (internal-error)))))

(define (legitimate-list? xs x-perturbations tags)
 (or (and (null? xs) (tagged-null? tags x-perturbations))
     (and (not (null? xs))
	  (vlad-pair? x-perturbations tags)
	  (legitimate? (first xs) (vlad-car x-perturbations tags))
	  (legitimate-list? (rest xs) (vlad-cdr x-perturbations tags) tags))))

(define (legitimate? x x-perturbation)
 (or (and (null? x) (null? x-perturbation))
     (and (not *church-booleans?*) (vlad-boolean? x) (null? x-perturbation))
     (and (real? x) (real? x-perturbation))
     (and (primitive-procedure? x) (null? x-perturbation))
     (and (closure? x)
	  (legitimate-list? (base-values x) x-perturbation (closure-tags x)))
     (and (bundle? x)
	  (bundle? x-perturbation)
	  (legitimate? (bundle-primal x)
		       (bundle-primal x-perturbation))
	  (legitimate? (bundle-tangent x)
		       (bundle-tangent x-perturbation)))
     (and (reverse-tagged-value? x)
	  (reverse-tagged-value? x-perturbation)
	  (legitimate? (reverse-tagged-value-primal x)
		       (reverse-tagged-value-primal x-perturbation)))
     (and (not *church-pairs?*)
	  (tagged-pair? x)
	  (tagged-pair? x-perturbation)
	  (equal? (tagged-pair-tags x) (tagged-pair-tags x-perturbation))
	  (legitimate? (tagged-pair-car x) (tagged-pair-car x-perturbation))
	  (legitimate? (tagged-pair-cdr x)
		       (tagged-pair-cdr x-perturbation)))))

(define (bundle-list xs x-perturbations tags)
 (if (null? xs)
     '()
     (cons (bundle-internal (first xs) (vlad-car x-perturbations tags))
	   (bundle-list (rest xs) (vlad-cdr x-perturbations tags) tags))))

(define (bundle-internal x x-perturbation)
 (cond
  ((null? x) (make-bundle x x-perturbation))
  ((and (not *church-booleans?*) (vlad-boolean? x))
   (make-bundle x x-perturbation))
  ((real? x) (make-bundle x x-perturbation))
  ((primitive-procedure? x)
   (unless (null? x-perturbation) (internal-error))
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
	    (vs (bundle-list (base-values x)
			     x-perturbation
			     (nonrecursive-closure-tags x))))
       (map (lambda (x v)
	     (let ((i (positionp variable=? x xs)))
	      (if i (list-ref vs i) (j* v))))
	    (nonrecursive-closure-variables x)
	    (vector->list (nonrecursive-closure-values x)))))
     x1
     (index x1 xs (lambda-expression-body e))
     ;; needs work: tangent of bundle gives the index-expression and
     ;;             index-environment of the primal
     (nonrecursive-closure-index-expression x)
     (nonrecursive-closure-index-environment x))))
  ((recursive-closure? x)
   (let* ((es (vector->list
	       (map-vector (lambda (x e)
			    (forward-transform (new-lambda-expression x e)))
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
	    (vs (bundle-list
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
     (recursive-closure-index x)
     ;; needs work: tangent of bundle gives the index-expression and
     ;;             index-environment of the primal
     (recursive-closure-index-expression x)
     (recursive-closure-index-environment x))))
  ((bundle? x) (make-bundle x x-perturbation))
  ((reverse-tagged-value? x) (make-bundle x x-perturbation))
  ((and (not *church-pairs?*) (tagged-pair? x))
   ;; needs work: tangent of bundle gives the index-expression and
   ;;             index-environment of the primal
   (create-tagged-pair
    (cons 'forward (tagged-pair-tags x))
    (bundle-internal (tagged-pair-car x) (tagged-pair-car x-perturbation))
    (bundle-internal (tagged-pair-cdr x) (tagged-pair-cdr x-perturbation))))
  (else (internal-error))))

(define (bundle x x-perturbation)
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
		 (bundle-internal x x-perturbation))))
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
 ;; needs work: direct tags
 (let loop ((tags tags))
  (if (null? tags)
      e
      ((case (first tags)
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
      ((forward)
       (make-bundle-invocation bs
			       (make-cdr bs (rest tags) (make-primal bs e))
			       (make-cdr bs (rest tags) (make-tangent bs e))))
      ((reverse) (make-*j bs (make-cdr bs (rest tags) (make-*j-inverse bs e))))
      (else (internal-error)))))

(define (make-cons bs tags e1 e2)
 (if *church-pairs?*
     (if (null? tags)
	 (new-application
	  (new-application (added-variable bs 'cons-procedure) e1) e2)
	 (case (first tags)
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
     (create-cons-expression tags e1 e2)))

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
		      (create-cons-expression
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
	  (cons (create-cons-expression
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
 (if *church-pairs?*
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
      (append (if *church-pairs?*
		  (list 'null 'car 'cdr 'cons-procedure)
		  (list 'null))
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
	  (cond
	   ((null? v) (make-reverse-tagged-value v))
	   ((and (not *church-booleans?*) (vlad-boolean? v))
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
	       x xs (copy-propagate (anf-convert (lambda-expression-body e))))
	      (nonrecursive-closure-index-expression v)
	      (nonrecursive-closure-index-environment v))))
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
	      (recursive-closure-index v)
	      (recursive-closure-index-expression v)
	      (recursive-closure-index-environment v))))
	   ((bundle? v) (make-reverse-tagged-value v))
	   ((reverse-tagged-value? v) (make-reverse-tagged-value v))
	   ((and (not *church-pairs?*) (tagged-pair? v))
	    (create-tagged-pair (cons 'reverse (tagged-pair-tags v))
				(*j (tagged-pair-car v))
				(*j (tagged-pair-cdr v))))
	   (else (internal-error)))))
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
	  (cond
	   ((null? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((and (not *church-booleans?*) (vlad-boolean? x-reverse))
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
		   (index x xs (copy-propagate (lambda-expression-body e)))
		   (nonrecursive-closure-index-expression x-reverse)
		   (nonrecursive-closure-index-environment x-reverse))))))
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
		   (recursive-closure-index x-reverse)
		   (recursive-closure-index-expression x-reverse)
		   (recursive-closure-index-environment x-reverse))))))
	   ((bundle? x-reverse)
	    (run-time-error
	     "Attempt to take *j-inverse of a non-reverse value" x-reverse))
	   ((reverse-tagged-value? x-reverse)
	    (reverse-tagged-value-primal x-reverse))
	   ((and (not *church-pairs?*) (tagged-pair? x-reverse))
	    (unless (and (not (null? (tagged-pair-tags x-reverse)))
			 (eq? (first (tagged-pair-tags x-reverse)) 'reverse))
	     (run-time-error
	      "Attempt to take primal of a non-reverse value" x-reverse))
	    (create-tagged-pair (rest (tagged-pair-tags x-reverse))
				(*j-inverse (tagged-pair-car x-reverse))
				(*j-inverse (tagged-pair-cdr x-reverse))))
	   (else (internal-error)))
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
       ((real? v) #t)
       ((vlad-pair? v '())
	(and (quotable? (vlad-car v '())) (quotable? (vlad-cdr v '()))))
       ((primitive-procedure? v) #f)
       ((closure? v) #f)
       ((bundle? v) #f)
       ((reverse-tagged-value? v) #f)
       (else (internal-error))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *church-pairs?*) (tagged-pair? v)))
		(vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
		  `(bundle ,(loop (primal v) quote?)
			   ,(loop (tangent v) quote?)))
		 (else `(forward ,(loop (primal v) quote?)
				 ,(loop (tangent v) quote?)))))
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *church-pairs?*) (tagged-pair? v)))
		(vlad-reverse? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (internal-error))
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
	     (when quote? (internal-error))
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
 (unless (or (and *church-booleans?*
		  (or (vlad-pair? callee '())
		      (vlad-true? callee)
		      (vlad-false? callee)))
	     (and *church-pairs?* (vlad-pair? callee '()))
	     (vlad-procedure? callee))
  (run-time-error "Target is not a procedure" callee))
 (when *anal?*
  (unless (tag-check?
	   (cond ((primitive-procedure? callee) '())
		 ((closure? callee) (closure-tags callee))
		 (else (internal-error)))
	   argument)
   (run-time-error "Argument has wrong type for target" callee argument)))
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
			       i
			       (recursive-closure-index-expression callee)
			       (recursive-closure-index-environment callee))))
			 (vector-length (recursive-closure-bodies callee)))
			(recursive-closure-values callee))))
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
	 (make-nonrecursive-closure
	  (free-variables e)
	  vs
	  (lambda-expression-variable e)
	  (lambda-expression-body e)
	  e
	  vs)))
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
	      i
	      e
	      vs))
	    (vector-length es)))
	  (map-vector lookup
		      (letrec-expression-body-free-variable-indices e)))))
       ((cons-expression? e)
	;; This LET* is to specify the evaluation order.
	(let* ((car (evaluate (cons-expression-car e) v vs))
	       (cdr (evaluate (cons-expression-cdr e) v vs)))
	 (create-tagged-pair (cons-expression-tags e) car cdr)))
       (else (internal-error))))

;;; begin stuff that belongs to brownfis

;;; Flow Analysis

;;; b binding
;;; e expression
;;; p predicate or procedure
;;; u proto abstract value
;;; v abstract value
;;; x variable

;;; A novel issue with flow analysis for VLAD is that the AD functions create
;;; new expressions.

;;; General

(define (equalq? x y)
 ;; This is a version of equal? that checks for eq? (by way of eqv?). This is
 ;; used solely to allow application to circular structures, which arises only
 ;; in the case of primitive procedures.
 (or (eqv? x y)
     (and (pair? x)
	  (pair? y)
	  (equalq? (car x) (car y))
	  (equalq? (cdr x) (cdr y)))
     (and (vector? x)
	  (vector? y)
	  (= (vector-length x) (vector-length y))
	  (every-vector equalq? x y))
     (and (string? x) (string? y) (string=? x y))))

(define (make-list length fill) (map-n (lambda (i) fill) length))

(define (replaceq x x-prime l) (map (lambda (e) (if (eq? e x) x-prime e)) l))

(define (rest* l k) (if (zero? k) l (rest* (rest l) (- k 1))))

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
	  (equal? (cons-expression-tags e1) (cons-expression-tags e2))
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

;;; Abstract Reals

(define (abstract-real? u) (or (real? u) (eq? u 'real)))

;;; Abstract Closures

(define (nonrecursive-closure-extensional-match? u1 u2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (variable=? (nonrecursive-closure-variable u1)
		      (nonrecursive-closure-variable u2))
	  (expression=? (nonrecursive-closure-body u1)
			(nonrecursive-closure-body u2)))))

(define (nonrecursive-closure-match? bs)
 (lambda (u1 u2)
  (and (nonrecursive-closure-extensional-match? u1 u2)
       (let ((b1 (lookup-environment-binding
		  (nonrecursive-closure-index-expression u1)
		  (nonrecursive-closure-index-environment u1)
		  bs))
	     (b2 (lookup-environment-binding
		  (nonrecursive-closure-index-expression u2)
		  (nonrecursive-closure-index-environment u2)
		  bs)))
	(and b1 b2 (eq? b1 b2))))))

(define (make-abstract-nonrecursive-closure vs e index-environment)
 (if (some-vector empty-abstract-value? vs)
     (empty-abstract-value)
     (list (make-nonrecursive-closure
	    (free-variables e)
	    vs
	    (lambda-expression-variable e)
	    (lambda-expression-body e)
	    e
	    index-environment))))

(define (recursive-closure-extensional-match? u1 u2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (= (recursive-closure-index u1) (recursive-closure-index u2))
	  (= (vector-length (recursive-closure-procedure-variables u1))
	     (vector-length (recursive-closure-procedure-variables u2)))
	  (= (vector-length (recursive-closure-argument-variables u1))
	     (vector-length (recursive-closure-argument-variables u2)))
	  (every-vector variable=?
			(recursive-closure-procedure-variables u1)
			(recursive-closure-procedure-variables u2))
	  (every-vector variable=?
			(recursive-closure-argument-variables u1)
			(recursive-closure-argument-variables u2))
	  (every-vector expression=?
			(recursive-closure-bodies u1)
			(recursive-closure-bodies u2)))))

(define (recursive-closure-match? bs)
 (lambda (u1 u2)
  (and (recursive-closure-extensional-match? u1 u2)
       (let ((b1 (lookup-environment-binding
		  (recursive-closure-index-expression u1)
		  (recursive-closure-index-environment u1)
		  bs))
	     (b2 (lookup-environment-binding
		  (recursive-closure-index-expression u2)
		  (recursive-closure-index-environment u2)
		  bs)))
	(and b1 b2 (eq? b1 b2))))))

(define (make-abstract-recursive-closure variables
					 values
					 procedure-variables
					 argument-variables
					 bodies
					 index
					 index-expression
					 index-environment)
 (if (some-vector empty-abstract-value? values)
     (empty-abstract-value)
     (list (make-recursive-closure
	    variables
	    values
	    procedure-variables
	    argument-variables
	    bodies
	    index
	    index-expression
	    index-environment))))

(define (recursive-closure-procedure-lambda-expressions v)
 ;; This is only used in externalize-proto-abstract-value.
 (map-vector new-lambda-expression
	     (recursive-closure-argument-variables v)
	     (recursive-closure-bodies v)))

(define (closure-extensional-match? u1 u2)
 (unless (and (closure? u1) (closure? u2))
  (internal-error "u1 and u2 should both be closures"))
 (or (and (nonrecursive-closure? u1)
	  (nonrecursive-closure? u2)
	  (nonrecursive-closure-extensional-match? u1 u2))
     (and (recursive-closure? u1)
	  (recursive-closure? u2)
	  (recursive-closure-extensional-match? u1 u2))))

(define (closure-match? bs)
 (lambda (u1 u2)
  (unless (and (closure? u1) (closure? u2))
   (internal-error "u1 and u2 should both be closures"))
  (or (and (nonrecursive-closure? u1)
	   (nonrecursive-closure? u2)
	   ((nonrecursive-closure-match? bs) u1 u2))
      (and (recursive-closure? u1)
	   (recursive-closure? u2)
	   ((recursive-closure-match? bs) u1 u2)))))

(define (closure-values u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-values u))
       ((recursive-closure? u) (recursive-closure-values u))
       (else (internal-error "Not a closure"))))

;;; Abstract Bundles

(define (make-abstract-bundle v1 v2)
 (when (or (up? v1) (up? v2)) (unimplemented "Bundles with backlinks"))
 (if (or (empty-abstract-value? v1) (empty-abstract-value? v2))
     (empty-abstract-value)
     (list (make-bundle v1 v2))))

(define (bundle-extensional-match? u1 u2) #t)

(define (bundle-match? bs) (lambda (u1 u2) #t))

;;; Abstract Reverse Tagged Values

(define (make-abstract-reverse-tagged-value v)
 (when (up? v) (unimplemented "Reverse-tagged-values with backlinks"))
 (if (empty-abstract-value? v)
     (empty-abstract-value)
     (list (make-reverse-tagged-value v))))

(define (reverse-tagged-value-extensional-match? u1 u2) #t)

(define (reverse-tagged-value-match? bs) (lambda (u1 u2) #t))

;;; Abstract Tagged Pairs

(define (make-abstract-tagged-pair
	 tags v1 v2 index-expression index-environment)
 (if (or (empty-abstract-value? v1) (empty-abstract-value? v2))
     (empty-abstract-value)
     (list (make-tagged-pair tags v1 v2 index-expression index-environment))))

(define (tagged-pair-extensional-match? u1 u2)
 (equal? (tagged-pair-tags u1) (tagged-pair-tags u2)))

(define (tagged-pair-match? bs)
 (lambda (u1 u2)
  (and (tagged-pair-extensional-match? u1 u2)
       (let ((b1 (lookup-environment-binding (tagged-pair-index-expression u1)
					     (tagged-pair-index-environment u1)
					     bs))
	     (b2 (lookup-environment-binding (tagged-pair-index-expression u2)
					     (tagged-pair-index-environment u2)
					     bs)))
	(and b1 b2 (eq? b1 b2))))))

;;; Abstract Aggregate Values

(define (scalar-proto-abstract-value? u)
 (or (null? u) (boolean? u) (abstract-real? u) (primitive-procedure? u)))

(define (aggregate-value-extensional-match? u1 u2)
 (or (and (closure? u1) (closure? u2) (closure-extensional-match? u1 u2))
     (and (bundle? u1) (bundle? u2) (bundle-extensional-match? u1 u2))
     ;; needs work: reverse tagged values
     (and (tagged-pair? u1)
	  (tagged-pair? u2)
	  (tagged-pair-extensional-match? u1 u2))))

(define (aggregate-value-match? bs)
 (lambda (u1 u2)
  (or
   (and (closure? u1) (closure? u2) ((closure-match? bs) u1 u2))
   (and (bundle? u1) (bundle? u2) ((bundle-match? bs) u1 u2))
   ;; needs work: reverse tagged values
   (and (tagged-pair? u1) (tagged-pair? u2) ((tagged-pair-match? bs) u1 u2)))))

(define (aggregate-value-values u)
 (cond ((closure? u) (vector->list (closure-values u)))
       ((bundle? u) (list (bundle-primal u) (bundle-tangent u)))
       ;; needs work: reverse tagged values
       ((tagged-pair? u) (list (tagged-pair-car u) (tagged-pair-cdr u)))
       (else (internal-error))))

(define (make-aggregate-value-with-new-values u vs)
 ;; needs work: To check that no vs is empty-abstract-value.
 (cond ((nonrecursive-closure? u)
	(make-nonrecursive-closure (nonrecursive-closure-variables u)
				   (list->vector vs)
				   (nonrecursive-closure-variable u)
				   (nonrecursive-closure-body u)
				   (nonrecursive-closure-index-expression u)
				   (nonrecursive-closure-index-environment u)))
       ((recursive-closure? u)
	(make-recursive-closure (recursive-closure-variables u)
				(list->vector vs)
				(recursive-closure-procedure-variables u)
				(recursive-closure-argument-variables u)
				(recursive-closure-bodies u)
				(recursive-closure-index u)
				(recursive-closure-index-expression u)
				(recursive-closure-index-environment u)))
       ((bundle? u)
	(when (or (up? (first vs)) (up? (second vs)))
	 (unimplemented "Bundles with backlinks"))
	(make-bundle (first vs) (second vs)))
       ;; needs work: reverse tagged values
       ((tagged-pair? u)
	(make-tagged-pair (tagged-pair-tags u)
			  (first vs)
			  (second vs)
			  (tagged-pair-index-expression u)
			  (tagged-pair-index-environment u)))
       (else (internal-error))))

;;; Abstract Values

(define (empty-abstract-value) '())

;;; needs work: To check for recursive values that can't terminate.
(define (empty-abstract-value? v) (null? v))

(define (vlad-value->abstract-value v)
 (if (scalar-proto-abstract-value? v)
     (list v)
     ;; needs work: this doesn't fill in the index-expression and
     ;;             index-environment slots
     (list (make-aggregate-value-with-new-values
	    v (map vlad-value->abstract-value (aggregate-value-values v))))))

(define (remove-redundant-proto-abstract-values v)
 ;; This does not affect the extension of the abstract value but can yield
 ;; a smaller representation. Thus this is just an optimization. Since
 ;; (proto) abstract value subset and equality is undecidable, can only
 ;; conservatively approximate this. This selects among a hierarchy of more
 ;; precise conservative approximation alternatives.
 ;; Using a conservative approximation is sound since proto abstract values are
 ;; removed only when the predicate returns #t which is a precise result for
 ;; all of the approximations.
 (remove-duplicatesp
  (case *method-for-removing-redundant-proto-abstract-values*
   ((identity) eq?)
   ((structural) equalq?)
   ((equality) proto-abstract-value=?)
   ((subset) proto-abstract-value-subset?)
   (else (internal-error)))
  v))

;;; (Proto-)Abstract-Value Subset, Equality, Disjointness, and Union

;;; One (proto) abstract value is a subset of another if the extension of the
;;; former is a subset of the extension of the latter. Two (proto) abstract
;;; values are equal if their extensions are equal. (These notions are
;;; dependent on the notion of value equality.) I used to think that (proto)
;;; abstract value subset and equality is undecidable (by reduction from
;;; context-free-grammar equivalence and that it is semidecidable since a lone
;;; element in the extension of the left argument that is not in the extension
;;; of the right argument witnesses nonsubset and the extension of an abstract
;;; value is recursively enumerable.) But now I realize that we are asking
;;; about the trees generated by a grammar, not the strings, i.e. strong
;;; equivalence, not weak equivalence. And I don't know whether this is
;;; decidable. We conservatively approximate these. A #t result is precise.
;;; The lone cause of imprecision is illustrated by the following example.
;;; Let v1={box({0,1})} and v2={box({0}),box({1})}. v1 is a subset of v2. Yet
;;; the procedure checks whether for every u1 in v1 there is some u2 in v2
;;; such that u1 is a subset of v2. This does not hold in this example because
;;; there is no single u2 which box({0,1}) is a subset of. One can get more
;;; precision by multiplying out v1. In this case, multiplying out v1 to
;;; {box({0}),box({1})} whould allow every u1 to have a single u2 for which u1
;;; is a subset of u2. Thus in this case, multiplying out would yield a
;;; precise result. In principle, one only need multiply out v1. But if v1 has
;;; recursion, there is no bound on the amount of multiplying out that may be
;;; needed.
;;; Only used in remove-redundant-proto-abstract-values, widen-abstract-value
;;; (only as an error check), lookup-environment-binding, convergence check,
;;; abstract-primal-u, and abstract-tangent-u.

(define (proto-abstract-value-subset?-internal u1 u2 cs vs1-above vs2-above)
 (or (and (null? u1) (null? u2))
     (and (boolean? u1) (boolean? u2) (eq? u1 u2))
     (and (eq? u1 'real) (eq? u2 'real))
     (and (real? u1) (eq? u2 'real))
     (and (real? u1) (real? u2) (= u1 u2))
     (and (primitive-procedure? u1) (primitive-procedure? u2) (eq? u1 u2))
     (and (aggregate-value-extensional-match? u1 u2)
	  (every
	   (lambda (v1 v2)
	    (abstract-value-subset?-internal v1 v2 cs vs1-above vs2-above))
	   (aggregate-value-values u1)
	   (aggregate-value-values u2)))))

(define (abstract-value-subset?-internal v1 v2 cs vs1-above vs2-above)
 (cond
  ((up? v1)
   (abstract-value-subset?-internal (list-ref vs1-above (up-index v1))
				    v2
				    cs
				    (rest* vs1-above (+ (up-index v1) 1))
				    vs2-above))
  ((up? v2)
   (abstract-value-subset?-internal v1
				    (list-ref vs2-above (up-index v2))
				    cs
				    vs1-above
				    (rest* vs2-above (+ (up-index v2) 1))))
  ((some (lambda (c) (and (eq? v1 (car c)) (eq? v2 (cdr c)))) cs) #t)
  (else (every (lambda (u1)
		(some (lambda (u2)
		       (proto-abstract-value-subset?-internal
			u1
			u2
			(cons (cons v1 v2) cs)
			(cons v1 vs1-above)
			(cons v2 vs2-above)))
		      v2))
	       v1))))

(define (proto-abstract-value-subset? u1 u2)
 (proto-abstract-value-subset?-internal u1 u2 '() '() '()))

(define (abstract-value-subset? v1 v2)
 (abstract-value-subset?-internal v1 v2 '() '() '()))

(define (proto-abstract-value=? u1 u2)
 (and (proto-abstract-value-subset? u1 u2)
      (proto-abstract-value-subset? u2 u1)))

(define (abstract-value=? v1 v2)
 (and (abstract-value-subset? v1 v2) (abstract-value-subset? v2 v1)))

;;; Two (proto) abstract values are nondisjoint if their extensions are
;;; nondisjoint. (This notion depends on the notion of value equality.)
;;; I used to think that determining whether two (proto) abstract values are
;;; nondisjoint is undecidable (by reduction from nonempty interesection of
;;; two context-free grammars, which is semidecidable since a lone element in
;;; the extension of both arguments witnesses nondisjointness and the
;;; extension of an abstract value is enumerable.) But now I realize that we
;;; are asking about the trees generated by a grammar, not the strings, i.e.
;;; strong equivalence, not weak equivalence. And I believe that determining
;;; whether the set of trees generated by two context-free grammars is
;;; nondisjoint is decidable. And I believe that this algorithm is precise.
;;; Only used in widen-abstract-flow.

(define (proto-abstract-value-nondisjoint?-internal
	 u1 u2 cs vs1-above vs2-above)
 (or (and (null? u1) (null? u2))
     (and (boolean? u1) (boolean? u2) (eq? u1 u2))
     (and (eq? u1 'real) (eq? u2 'real))
     (and (eq? u1 'real) (real? u2))
     (and (real? u1) (eq? u2 'real))
     (and (real? u1) (real? u2) (= u1 u2))
     (and (primitive-procedure? u1) (primitive-procedure? u2) (eq? u1 u2))
     (and (aggregate-value-extensional-match? u1 u2)
	  (every (lambda (v1 v2)
		  (abstract-value-nondisjoint?-internal
		   v1 v2 cs vs1-above vs2-above))
		 (aggregate-value-values u1)
		 (aggregate-value-values u2)))))

(define (abstract-value-nondisjoint?-internal v1 v2 cs vs1-above vs2-above)
 (cond ((up? v1)
	(abstract-value-nondisjoint?-internal
	 (list-ref vs1-above (up-index v1))
	 v2
	 cs
	 (rest* vs1-above (+ (up-index v1) 1))
	 vs2-above))
       ((up? v2)
	(abstract-value-nondisjoint?-internal
	 v1
	 (list-ref vs2-above (up-index v2))
	 cs
	 vs1-above
	 (rest* vs2-above (+ (up-index v2) 1))))
       ((some (lambda (c) (and (eq? v1 (car c)) (eq? v2 (cdr c)))) cs) #f)
       (else (some (lambda (u1)
		    (some (lambda (u2)
			   (proto-abstract-value-nondisjoint?-internal
			    u1
			    u2
			    (cons (cons v1 v2) cs)
			    (cons v1 vs1-above)
			    (cons v2 vs2-above)))
			  v2))
		   v1))))

(define (proto-abstract-value-nondisjoint? u1 u2)
 (proto-abstract-value-nondisjoint?-internal u1 u2 '() '() '()))

(define (abstract-value-nondisjoint? v1 v2)
 (abstract-value-nondisjoint?-internal v1 v2 '() '() '()))

(define (closed-proto-abstract-values v)
 (let loop ((v v) (vs-above '()))
  (if (up? v)
      (if (= (up-index v) (- (length vs-above) 1))
	  (map (lambda (u)
		(if (scalar-proto-abstract-value? u)
		    u
		    (make-aggregate-value-with-new-values
		     u
		     (map (lambda (v)
			   (if (memq v vs-above)
			       (make-up (+ (positionq v vs-above) 1))
			       v))
			  (aggregate-value-values u)))))
	       (last vs-above))
	  v)
      (map (lambda (u)
	    (if (scalar-proto-abstract-value? u)
		u
		(make-aggregate-value-with-new-values
		 u
		 (map (lambda (v1) (loop v1 (cons v vs-above)))
		      (aggregate-value-values u)))))
	   v))))

(define (abstract-value-union v1 v2)
 ;; This cannot introduce imprecision.
 (cond ((and (up? v1) (up? v2) (= (up-index v1) (up-index v2))) v1)
       ((or (up? v1) (up? v2))
	(internal-error "Can't union a union type with a backlink"))
       (else (remove-redundant-proto-abstract-values
	      (append (closed-proto-abstract-values v1)
		      (closed-proto-abstract-values v2))))))

(define (abstract-value-union-without-unroll v1 v2)
 ;; needs work: Why does this procedure exist?
 ;; This can introduce imprecision, as illustrated by the following example:
 ;; {(),pair(0,^0)} U {(),pair(1,^0)} would yield
 ;; {(),pair(0,^0),pair(1,^0)} which includes pair(0,pair(1,())) in its
 ;; extension even though it is not in the extension of either argument.
 (cond ((and (up? v1) (up? v2) (= (up-index v1) (up-index v2))) v1)
       ((or (up? v1) (up? v2))
	(internal-error "Can't union a union type with a backlink"))
       (else (remove-redundant-proto-abstract-values (append v1 v2)))))

;;; Abstract Environments

(define (abstract-environment-subset? vs1 vs2)
 (every-vector abstract-value-subset? vs1 vs2))

(define (abstract-environment=? vs1 vs2)
 (and (abstract-environment-subset? vs1 vs2)
      (abstract-environment-subset? vs2 vs1)))

(define (abstract-environment-nondisjoint? vs1 vs2)
 (every-vector abstract-value-nondisjoint? vs1 vs2))

(define (abstract-environment-union vs1 vs2)
 ;; This can introduce imprecision by forming the environment of the unions
 ;; instead of the union of the environments.
 (map-vector abstract-value-union vs1 vs2))

;;; Abstract Flows

(define (abstract-flow=? bs1 bs2)
 ;; This is a conservative approximation. A #t result is precise.
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp? (lambda (b1 b2)
	       (and (abstract-environment=? (environment-binding-values b1)
					    (environment-binding-values b2))
		    (abstract-value=? (environment-binding-value b1)
				      (environment-binding-value b2))))
	      bs1
	      bs2))

(define (abstract-flow-union bs1 bs2) (append bs1 bs2))

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

;;; Widen

;;; General

(define (some-proto-abstract-value?-internal p u vs-above)
 (and (not (scalar-proto-abstract-value? u))
      (some (lambda (v) (some-abstract-value?-internal p v vs-above))
	    (aggregate-value-values u))))

(define (some-abstract-value?-internal p v vs-above)
 (or (p v vs-above)
     (and (not (up? v))
	  (some (lambda (u)
		 (some-proto-abstract-value?-internal p u (cons v vs-above)))
		v))))

(define (some-proto-abstract-value? p u)
 (some-proto-abstract-value?-internal p u '()))

(define (some-abstract-value? p v) (some-abstract-value?-internal p v '()))

(define (map-abstract-value f v)
 (let loop ((v v) (vs-above '()))
  (if (up? v)
      v
      (map (lambda (u)
	    (if (scalar-proto-abstract-value? u)
		u
		(make-aggregate-value-with-new-values
		 u
		 (map (lambda (v1) (loop v1 (cons v vs-above)))
		      (aggregate-value-values u)))))
	   (f v vs-above)))))

(define (remove-redundant-proto-abstract-values* v)
 (map-abstract-value
  (lambda (v vs-above) (remove-redundant-proto-abstract-values v)) v))

(define (free-up? v vs-above)
 (and (up? v) (>= (up-index v) (length vs-above))))

(define (free-up-index up vs-above)
 (unless (free-up? up vs-above) (internal-error))
 (- (up-index up) (length vs-above)))

(define (make-free-up index vs-above)
 (make-up (+ index (length vs-above))))

(define (proto-abstract-value-process-free-ups-internal f u vs-above)
 (if (scalar-proto-abstract-value? u)
     u
     (make-aggregate-value-with-new-values
      u
      (map (lambda (v) (abstract-value-process-free-ups-internal f v vs-above))
	   (aggregate-value-values u)))))

(define (abstract-value-process-free-ups-internal f v vs-above)
 (cond ((free-up? v vs-above) (f v vs-above))
       ((up? v) v)
       (else (map (lambda (u)
		   (proto-abstract-value-process-free-ups-internal
		    f u (cons v vs-above)))
		  v))))

(define (proto-abstract-value-process-free-ups f u)
 (proto-abstract-value-process-free-ups-internal f u '()))

(define (abstract-value-process-free-ups f v)
 (abstract-value-process-free-ups-internal f v '()))

(define (decrement-free-ups v)
 (abstract-value-process-free-ups
  (lambda (up vs-above) (make-up (- (up-index up) 1))) v))

;;; Many procedures below return (list v additions), a list of an abstract
;;; value v and a list of additions. An addition is a set of abstract values.
;;; The first set is to added to the parent abstract value of v, the second
;;; set to the grandparent abstract value, and so on.
;;; Each abstract value in the addition is treated as if it were a child
;;; abstract value of the current abstract value.  This means that free
;;; references (FREE-UP 0) refer to the current abstract value, (FREE-UP 1)
;;; refer to the current abstract value's parent, and so on.

(define (create-v-additions up v)
 ;; returns: (list v additions)
 (list up (append (make-list (up-index up) '()) (list (list v)))))

(define (move-values-up-value v additions)
 ;; returns: (list v additions)
 (when (null? additions)
  (internal-error "Shouldn't we NOT do this if (null? additions)?"))
 (when (some up? (first additions))
  (internal-error "No additions should be UPs...should they?"))
 (let ((v-new (abstract-value-union-without-unroll
	       v
	       (reduce abstract-value-union-without-unroll
		       (map decrement-free-ups (first additions))
		       (empty-abstract-value)))))
  (list v-new
	(map-indexed
	 (lambda (vs i)
	  (append (map (lambda (v)
			(if (and (up? v) (zero? (up-index v)))
			    v-new
			    (abstract-value-process-free-ups
			     (lambda (v vs-above)
			      (if (zero? (free-up-index v vs-above))
				  (make-free-up i vs-above)
				  (make-up (- (up-index v) 1))))
			     v)))
		       vs)
		  (if (some (lambda (v)
			     (and (or (not (up? v)) (not (zero? (up-index v))))
				  (some-abstract-value?
				   (lambda (v vs-above)
				    (and (free-up? v vs-above)
					 (zero? (free-up-index v vs-above))))
				   v)))
			    vs)
		      (list v-new)
		      '())))
	 (rest additions)))))

;;; Matching Values

;;; needs work: To prefer widening to real instead of creating unions.
(define (pick-closures-to-coalesce us) (sublist us 0 2))

(define (pick-bundles-to-coalesce us) (sublist us 0 2))

(define (pick-tagged-pairs-to-coalesce us) (sublist us 0 2))

(define (merge-additions additions1 additions2)
 (cond ((null? additions1) additions2)
       ((null? additions2) additions1)
       (else (cons (append (first additions1) (first additions2))
		   (merge-additions (rest additions1) (rest additions2))))))

(define (union-for-widening v1 v2)
 ;; This assumes that v1 and v2 share the same context. In other words, all
 ;; free ups which are the same refer to the same abstract values.
 ;; returns: (list v additions)
 (cond ((and (up? v1) (up? v2))
	(cond ((> (up-index v1) (up-index v2)) (create-v-additions v1 v2))
	      ((< (up-index v1) (up-index v2)) (create-v-additions v2 v1))
	      (else (list v1 '()))))
       ((up? v1) (create-v-additions v1 v2))
       ((up? v2) (create-v-additions v2 v1))
       (else (list (abstract-value-union-without-unroll v1 v2) '()))))

(define (limit-aggregate-values v
				k
				target-aggregate-value?
				match?
				pick-us-to-coalesce)
 ;; If there were no redundant proto abstract values upon entry, there will be
 ;; none upon exit.
 ;; returns: (list v additions)
 (let ((v-additions-list
	(map
	 (lambda (us)
	  (let loop ((us us) (additions '()))
	   ;; This assumes that we have first called
	   ;; remove-redundant-proto-abstract-values.
	   (if (<= (length us) k)
	       (list us additions)
	       (let* ((u1-u2 (pick-us-to-coalesce us))
		      (v-additions-list
		       (map union-for-widening
			    (aggregate-value-values (first u1-u2))
			    (aggregate-value-values (second u1-u2)))))
		(loop
		 (cons (make-aggregate-value-with-new-values
			(first u1-u2) (map first v-additions-list))
		       (removeq (second u1-u2) (removeq (first u1-u2) us)))
		 (merge-additions
		  additions
		  (reduce
		   merge-additions (map second v-additions-list) '())))))))
	 (transitive-equivalence-classesp
	  match? (remove-if-not target-aggregate-value? v)))))
  (list (append (remove-if target-aggregate-value? v)
		(reduce append (map first v-additions-list) '()))
	(reduce merge-additions (map second v-additions-list) '()))))

(define (limit-aggregate-values* limit v)
 (let ((v-additions
	;; returns: (list v additions)
	(let loop ((v v))
	 (if (up? v)
	     (list v '())
	     (let ((v-additions (limit v)))
	      (if (null? (second v-additions))
		  (if (up? (first v-additions))
		      (list (first v-additions) '())
		      (let ((u-additions-list
			     (map
			      (lambda (u)
			       (if (scalar-proto-abstract-value? u)
				   (list u '())
				   (let ((v-additions-list
					  (map loop
					       (aggregate-value-values u))))
				    (list (make-aggregate-value-with-new-values
					   u (map first v-additions-list))
					  (reduce merge-additions
						  (map second v-additions-list)
						  '())))))
			      (first v-additions))))
		       (if (null? (reduce merge-additions
					  (map second u-additions-list)
					  '()))
			   (list (map first u-additions-list) '())
			   (let ((v-additions
				  (move-values-up-value
				   (map first u-additions-list)
				   (reduce merge-additions
					   (map second u-additions-list)
					   '()))))
			    (if (null? (second v-additions))
				(loop (first v-additions))
				v-additions)))))
		  (let ((v-additions
			 (move-values-up-value
			  (first v-additions) (second v-additions))))
		   (if (null? (second v-additions))
		       (loop (first v-additions))
		       v-additions))))))))
  (unless (null? (second v-additions))
   (internal-error "Some addition wasn't applied"))
  (first v-additions)))

(define (limit-reals v)
 (if (eq? *real-limit* #f)
     v
     (map-abstract-value (lambda (v vs-above)
			  ;; This assumes that we have first called
			  ;; remove-redundant-proto-abstract-values.
			  (if (> (count-if abstract-real? v) *real-limit*)
			      (cons 'real (remove-if abstract-real? v))
			      v))
			 v)))

(define (limit-closures v bs)
 (if (eq? *closure-limit* #f)
     v
     (limit-aggregate-values*
      (lambda (v)
       (limit-aggregate-values v
			       *closure-limit*
			       closure?
			       closure-extensional-match?
			       pick-closures-to-coalesce))
      v)))

(define (limit-bundles v bs)
 (if (eq? *bundle-limit* #f)
     v
     (limit-aggregate-values*
      (lambda (v)
       (limit-aggregate-values v
			       *bundle-limit*
			       bundle?
			       bundle-extensional-match?
			       pick-bundles-to-coalesce))
      v)))

(define (limit-tagged-pairs v bs)
 (if (eq? *tagged-pair-limit* #f)
     v
     (limit-aggregate-values*
      (lambda (v)
       (limit-aggregate-values v
			       *tagged-pair-limit*
			       tagged-pair?
			       tagged-pair-extensional-match?
			       pick-tagged-pairs-to-coalesce))
      v)))

;;; Depth

;;; A path is an alternating list of abstract values and proto abstract values.
;;; The first element of the list is the root and the last element is a leaf.
;;; The first element is an abstract value and the last element is either a
;;; scalar proto abstract value, an aggregate proto abstract value that has no
;;; children, an empty abstract value, or an up. Each proto abstract value is
;;; a member of the preceeding abstract value and each abstract value is a
;;; member of the aggregate values of the preceeding proto abstract value.

(define (depth match? type? path)
 (reduce max
	 (map length
	      (transitive-equivalence-classesp
	       match? (remove-if-not type? (every-other (rest path)))))
	 0))

(define (path-of-depth-greater-than-k k match? type? v)
 (let outer ((v v) (path '()))
  (if (or (up? v) (empty-abstract-value? v))
      (if (> (depth match? type? (reverse (cons v path))) k)
	  (reverse (cons v path))
	  #f)
      (let middle ((us v))
       (if (null? us)
	   #f
	   (if (scalar-proto-abstract-value? (first us))
	       (if (> (depth
		       match? type? (reverse (cons (first us) (cons v path))))
		      k)
		   (reverse (cons (first us) (cons v path)))
		   (middle (rest us)))
	       (let inner ((vs (aggregate-value-values (first us))))
		(if (null? vs)
		    (middle (rest us))
		    (let ((path
			   (outer (first vs) (cons (first us) (cons v path)))))
		     (if (eq? path #f) (inner (rest vs)) path))))))))))

(define (pick-values-to-coalesce match? type? path)
 (let* ((classes (transitive-equivalence-classesp
		  match? (remove-if-not type? (every-other (rest path)))))
	(k (reduce max (map length classes) 0))
	(positions
	 (sort (map (lambda (u) (positionq u path))
		    (find-if (lambda (us) (= (length us) k)) classes))
	       >
	       identity)))
  ;; v1 must be closer to the root than v2
  (list (list-ref path (- (second positions) 1))
	(list-ref path (- (first positions) 1)))))

(define (reduce-depth path v1 v2)
 ;; v1 must be closer to the root than v2
 (let ((v-additions
	(let loop ((path path) (vs-above '()))
	 (when (null? path) (internal-error))
	 (if (eq? (first path) v2)
	     (create-v-additions
	      (make-up (positionq v1 vs-above)) (first path))
	     (let* ((v-additions
		     (loop (rest (rest path)) (cons (first path) vs-above)))
		    (v (replaceq
			(second path)
			(make-aggregate-value-with-new-values
			 (second path)
			 (replaceq (third path)
				   (first v-additions)
				   (aggregate-value-values (second path))))
			(first path))))
	      (if (null? (second v-additions))
		  (list v '())
		  (move-values-up-value v (second v-additions))))))))
  (unless (null? (second v-additions))
   (internal-error "Some addition wasn't applied"))
  (first v-additions)))

(define (limit-closure-depth v bs)
 (if (eq? *closure-depth-limit* #f)
     v
     (let loop ((v v))
      (let ((path (path-of-depth-greater-than-k
		   *closure-depth-limit* (closure-match? bs) closure? v)))
       (if (eq? path #f)
	   v
	   (let ((v1-v2
		  (pick-values-to-coalesce (closure-match? bs) closure? path)))
	    (loop (reduce-depth path (first v1-v2) (second v1-v2)))))))))

(define (limit-tagged-pair-depth v bs)
 (if (eq? *tagged-pair-depth-limit* #f)
     v
     (let loop ((v v))
      (let ((path (path-of-depth-greater-than-k *tagged-pair-depth-limit*
						(tagged-pair-match? bs)
						tagged-pair?
						v)))
       (if (eq? path #f)
	   v
	   (let ((v1-v2 (pick-values-to-coalesce
			 (tagged-pair-match? bs) tagged-pair? path)))
	    (loop (reduce-depth path (first v1-v2) (second v1-v2)))))))))

;;; Syntactic Constraints

(define (flow-size-limit-met? bs)
 (or (not *flow-size-limit*) (<= (length bs) *flow-size-limit*)))

(define (real-limit-met? v)
 (or (not *real-limit*)
     (not (some-abstract-value?
	   (lambda (v vs-above)
	    (and (not (up? v)) (> (count-if abstract-real? v) *real-limit*)))
	   v))))

(define (closure-limit-met? v bs)
 (or (not *closure-limit*)
     (not (some-abstract-value?
	   (lambda (v vs-above)
	    (and (not (up? v))
		 (some (lambda (us) (> (length us) *closure-limit*))
		       (transitive-equivalence-classesp
			closure-extensional-match?
			(remove-if-not closure? v)))))
	   v))))

(define (closure-depth-limit-met? v bs)
 (or (not *closure-depth-limit*)
     (eq? (path-of-depth-greater-than-k
	   *closure-depth-limit* (closure-match? bs) closure? v)
	  #f)))

(define (bundle-limit-met? v bs)
 (or (not *bundle-limit*)
     (not (some-abstract-value?
	   (lambda (v vs-above)
	    (and (not (up? v))
		 (some (lambda (us) (> (length us) *bundle-limit*))
		       (transitive-equivalence-classesp
			bundle-extensional-match? (remove-if-not bundle? v)))))
	   v))))

(define (bundle-depth-limit-met? v bs)
 (or (not *bundle-depth-limit*)
     (eq? (path-of-depth-greater-than-k
	   *bundle-depth-limit* (bundle-match? bs) bundle? v)
	  #f)))

(define (tagged-pair-limit-met? v bs)
 (or (not *tagged-pair-limit*)
     (not (some-abstract-value?
	   (lambda (v vs-above)
	    (and (not (up? v))
		 (some (lambda (us) (> (length us) *tagged-pair-limit*))
		       (transitive-equivalence-classesp
			tagged-pair-extensional-match?
			(remove-if-not tagged-pair? v)))))
	   v))))

(define (tagged-pair-depth-limit-met? v bs)
 (or (not *tagged-pair-depth-limit*)
     (eq? (path-of-depth-greater-than-k
	   *tagged-pair-depth-limit* (tagged-pair-match? bs) tagged-pair? v)
	  #f)))

(define (syntactic-constraints-met? v bs)
 (and (real-limit-met? v)
      (closure-limit-met? v bs)
      (closure-depth-limit-met? v bs)
      (bundle-limit-met? v bs)
      (tagged-pair-limit-met? v bs)
      (tagged-pair-depth-limit-met? v bs)))

(define (widen-abstract-value v-debugging bs)
 ;; This can introduce imprecision.
 (let loop ((v (remove-redundant-proto-abstract-values* v-debugging)))
  (if (syntactic-constraints-met? v bs)
      (begin
       (when #t				;debugging
	(unless (abstract-value-subset? v-debugging v)
	 (internal-error
	  "widen: ~s" (externalize-abstract-value v-debugging))))
       (unless (bundle-depth-limit-met? v bs)
	(compile-time-error "Bundle depth limit exceeded"))
       v)
      (loop
       (remove-redundant-proto-abstract-values*
	(limit-reals
	 (remove-redundant-proto-abstract-values*
	  (limit-tagged-pair-depth
	   (limit-closure-depth
	    (limit-tagged-pairs
	     (limit-bundles (limit-closures v bs) bs) bs)
	    bs)
	   bs))))))))

(define (pick-environment-bindings-to-coalesce bs) (sublist bs 0 2))

(define (widen-abstract-flow bs bs1)
 (let loop ((bs (map (lambda (b)
		      (make-environment-binding
		       ;; needs work: This should be removed if not necessary
		       ;;             and moved to abstract-value-union if
		       ;;             necessary.
		       (map-vector remove-redundant-proto-abstract-values*
				   (environment-binding-values b))
		       (environment-binding-value b)))
		     bs)))
  ;; This enforces three constraints. We could change the order in which they
  ;; are enforced.
  (cond
   ;; First, that the domains be disjoint. This can introduce imprecision
   ;; because of abstract-environment-union.
   ((some (lambda (b1)
	   (some (lambda (b2)
		  (and (not (eq? b1 b2))
		       (abstract-environment-nondisjoint?
			(environment-binding-values b1)
			(environment-binding-values b2))))
		 bs))
	  bs)
    ;; needs work: Should abstract the choice of which environments to
    ;;             coalesce as a pick procedure.
    (let* ((b1 (find-if
		(lambda (b1)
		 (some (lambda (b2)
			(and (not (eq? b1 b2))
			     (abstract-environment-nondisjoint?
			      (environment-binding-values b1)
			      (environment-binding-values b2))))
		       bs))
		bs))
	   (b2 (find-if (lambda (b2)
			 (and (not (eq? b1 b2))
			      (abstract-environment-nondisjoint?
			       (environment-binding-values b1)
			       (environment-binding-values b2))))
			bs)))
     (loop (cons (make-environment-binding
		  ;; needs work: This should be removed if not necessary and
		  ;;             moved to abstract-value-union if necessary.
		  (map-vector remove-redundant-proto-abstract-values*
			      (abstract-environment-union
			       (environment-binding-values b1)
			       (environment-binding-values b2)))
		  ;; We pick one range arbitrarily. We don't union the ranges
		  ;; and leave it up to update-analysis-ranges to do that.
		  (environment-binding-value b1))
		 (removeq b2 (removeq b1 bs))))))
   ;; Second, that the abstract values in the domains meet the syntactic
   ;; constraints. This can introduct imprecision.
   ((some (lambda (b)
	   (some-vector (lambda (v) (not (syntactic-constraints-met? v bs1)))
			(environment-binding-values b)))
	  bs)
    (loop (map (lambda (b)
		(make-environment-binding
		 (map-vector (lambda (v) (widen-abstract-value v bs1))
			     (environment-binding-values b))
		 (environment-binding-value b)))
	       bs)))
   ;; Third, that the flow size limit be met. This can introduce imprecision
   ;; because of abstract-environment-union.
   ((not (flow-size-limit-met? bs))
    (let ((b1-b2 (pick-environment-bindings-to-coalesce bs)))
     (loop (cons (make-environment-binding
		  ;; needs work: This should be removed if not necessary and
		  ;;             moved to abstract-value-union if necessary.
		  (map-vector remove-redundant-proto-abstract-values*
			      (abstract-environment-union
			       (environment-binding-values (first b1-b2))
			       (environment-binding-values (second b1-b2))))
		  ;; We pick one range arbitrarily. We don't union the ranges
		  ;; and leave it up to update-analysis-ranges to do that.
		  (environment-binding-value (first b1-b2)))
		 (removeq (second b1-b2) (removeq (first b1-b2) bs))))))
   (else bs))))

(define (widen-analysis-domains bs bs1)
 ;; This can introduce imprecision.
 (map (lambda (b)
       (make-expression-binding
	(expression-binding-expression b)
	(widen-abstract-flow (expression-binding-flow b) bs1)))
      bs))

;;; Abstract Interpretation

(define (free-variable-indices e)
 (cond
  ((variable-access-expression? e)
   (vector (variable-access-expression-index e)))
  ((lambda-expression? e) (lambda-expression-free-variable-indices e))
  ((application? e) (application-free-variable-indices e))
  ((letrec-expression? e) (letrec-expression-body-free-variable-indices e))
  ((cons-expression? e) (cons-expression-free-variable-indices e))
  (else (internal-error))))

(define (abstract-index lookup e)
 (let ((xs (free-variables e)))
  (cond
   ((variable-access-expression? e)
    (make-variable-access-expression
     (variable-access-expression-variable e)
     (lookup (variable-access-expression-variable e))))
   ((lambda-expression? e)
    (make-lambda-expression
     xs
     (list->vector (map lookup xs))
     (lambda-expression-variable e)
     (abstract-index (lambda (x)
		      (unless (or (variable=? x (lambda-expression-variable e))
				  (memp variable=? x xs))
		       (internal-error))
		      (if (variable=? x (lambda-expression-variable e))
			  (length xs)
			  (positionp variable=? x xs)))
		     (lambda-expression-body e))))
   ((application? e)
    (make-application
     (abstract-index (lambda (x)
		      (unless (memp variable=? x xs) (internal-error))
		      (positionp variable=? x xs))
		     (application-callee e))
     (abstract-index (lambda (x)
		      (unless (memp variable=? x xs) (internal-error))
		      (positionp variable=? x xs))
		     (application-argument e))
     (list->vector (map lookup xs))))
   ((letrec-expression? e)
    (make-letrec-expression
     (letrec-expression-bodies-free-variables e)
     (list->vector (map (lambda (x)
			 (unless (memp variable=? x xs) (internal-error))
			 (positionp variable=? x xs))
			(letrec-expression-bodies-free-variables e)))
     xs
     (list->vector (map lookup xs))
     (letrec-expression-procedure-variables e)
     (letrec-expression-argument-variables e)
     (map (lambda (x1 e1)
	   (abstract-index
	    (lambda (x)
	     (unless (or (variable=? x x1)
			 (memp variable=?
			       x
			       (letrec-expression-procedure-variables e))
			 (memp variable=?
			       x
			       (letrec-expression-bodies-free-variables e)))
	      (internal-error))
	     (cond
	      ((variable=? x x1)
	       (+ (length (letrec-expression-bodies-free-variables e))
		  (length (letrec-expression-procedure-variables e))))
	      ((memp variable=?
		     x
		     (letrec-expression-procedure-variables e))
	       (+ (length (letrec-expression-bodies-free-variables e))
		  (positionp
		   variable=? x (letrec-expression-procedure-variables e))))
	      (else
	       (positionp
		variable=? x (letrec-expression-bodies-free-variables e)))))
	    e1))
	  (letrec-expression-argument-variables e)
	  (letrec-expression-bodies e))
     (abstract-index
      (lambda (x)
       (unless (or
		(memp variable=? x (letrec-expression-procedure-variables e))
		(memp variable=? x xs))
	(internal-error))
       (if (memp variable=? x (letrec-expression-procedure-variables e))
	   (+ (length xs)
	      (positionp
	       variable=? x (letrec-expression-procedure-variables e)))
	   (positionp variable=? x xs)))
      (letrec-expression-body e))))
   ((cons-expression? e)
    (make-cons-expression
     (cons-expression-tags e)
     (abstract-index (lambda (x)
		      (unless (memp variable=? x xs) (internal-error))
		      (positionp variable=? x xs))
		     (cons-expression-car e))
     (abstract-index (lambda (x)
		      (unless (memp variable=? x xs) (internal-error))
		      (positionp variable=? x xs))
		     (cons-expression-cdr e))
     (list->vector (map lookup xs))))
   (else (internal-error)))))

(define (make-abstract-analysis e vs bs)
 (unless (= (vector-length vs) (length (free-variables e)))
  (internal-error
   "vs and (length (free-variables e)) should be of same length"))
 (if (some-vector empty-abstract-value? vs)
     (empty-abstract-analysis)
     (list (make-expression-binding
	    e (list (make-environment-binding
		     vs
		     (widen-abstract-value (abstract-eval1 e vs bs) bs)))))))

(define (initial-abstract-analysis e bs)
 ;; This (like update-analysis-domains) only makes domains.
 (make-abstract-analysis
  e
  (list->vector
   (map
    (lambda (x)
     (vlad-value->abstract-value
      (value-binding-value
       (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs))))
    (free-variables e)))
  '()))

(define (lookup-environment-binding e vs bs)
 (let ((b (lookup-expression-binding e bs)))
  (cond (b
	 (when #t			;debugging
	  ;; Because the domains of a flow are disjoint there can be only one.
	  (when (> (count-if (lambda (b)
			      (abstract-environment-subset?
			       vs (environment-binding-values b)))
			     (expression-binding-flow b))
		   1)
	   (internal-error)))
	 (find-if (lambda (b)
		   (abstract-environment-subset?
		    vs (environment-binding-values b)))
		  (expression-binding-flow b)))
	(else #f))))

(define (abstract-eval1 e vs bs)
 (let ((b (lookup-environment-binding e vs bs)))
  (if b (environment-binding-value b) (empty-abstract-value))))

(define (abstract-apply-closure p u1 v2)
 (cond
  ((nonrecursive-closure? u1)
   (p (nonrecursive-closure-body u1)
      (let ((vs (list->vector
		 (append (vector->list (nonrecursive-closure-values u1))
			 (list v2)))))
       (map-vector (lambda (i) (vector-ref vs i))
		   (free-variable-indices (nonrecursive-closure-body u1))))))
  ((recursive-closure? u1)
   (p (vector-ref (recursive-closure-bodies u1) (recursive-closure-index u1))
      (let ((vs (list->vector
		 (append
		  (vector->list (recursive-closure-values u1))
		  (map-n
		   (lambda (i)
		    (make-abstract-recursive-closure
		     (recursive-closure-variables u1)
		     (recursive-closure-values u1)
		     (recursive-closure-procedure-variables u1)
		     (recursive-closure-argument-variables u1)
		     (recursive-closure-bodies u1)
		     i
		     (recursive-closure-index-expression u1)
		     (recursive-closure-index-environment u1)))
		   (vector-length (recursive-closure-procedure-variables u1)))
		  (list v2)))))
       (map-vector (lambda (i) (vector-ref vs i))
		   (free-variable-indices
		    (vector-ref (recursive-closure-bodies u1)
				(recursive-closure-index u1)))))))
  (else (internal-error))))

(define (abstract-apply v1 v2 bs)
 (if (empty-abstract-value? v2)
     (empty-abstract-value)
     (reduce
      abstract-value-union
      (map
       (lambda (u1)
	(cond
	 ((primitive-procedure? u1)
	  (reduce abstract-value-union
		  (map (lambda (u2)
			((primitive-procedure-abstract-procedure u1) u2))
		       (closed-proto-abstract-values v2))
		  (empty-abstract-value)))
	 ((closure? u1)
	  (abstract-apply-closure
	   (lambda (e vs) (abstract-eval1 e vs bs)) u1 v2))
	 (else (compile-time-warning "Target might not be a procedure" u1))))
       (closed-proto-abstract-values v1))
      (empty-abstract-value))))

(define (abstract-eval e vs bs)
 (cond
  ((variable-access-expression? e) (vector-ref vs 0))
  ((lambda-expression? e) (make-abstract-nonrecursive-closure vs e vs))
  ((application? e)
   (abstract-apply
    (abstract-eval1
     (application-callee e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (application-callee e)))
     bs)
    (abstract-eval1
     (application-argument e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (application-argument e)))
     bs)
    bs))
  ((letrec-expression? e)
   (abstract-eval1
    (letrec-expression-body e)
    (let ((vs (list->vector
	       (append
		(vector->list vs)
		(let ((xs0 (letrec-expression-bodies-free-variables e))
		      (vs (map-vector
			   (lambda (i) (vector-ref vs i))
			   (letrec-expression-bodies-free-variable-indices e)))
		      (xs1 (list->vector
			    (letrec-expression-procedure-variables e)))
		      (xs2 (list->vector
			    (letrec-expression-argument-variables e)))
		      (es (list->vector (letrec-expression-bodies e))))
		 (map-n
		  (lambda (i)
		   (make-abstract-recursive-closure xs0 vs xs1 xs2 es i e vs))
		  (length (letrec-expression-procedure-variables e))))))))
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (letrec-expression-body e))))
    bs))
  ((cons-expression? e)
   (make-abstract-tagged-pair
    (cons-expression-tags e)
    (abstract-eval1
     (cons-expression-car e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (cons-expression-car e)))
     bs)
    (abstract-eval1
     (cons-expression-cdr e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (cons-expression-cdr e)))
     bs)
    e
    vs))
  (else (internal-error))))

(define (abstract-eval1-prime e vs bs)
 (let ((b (lookup-environment-binding e vs bs)))
  (if b (empty-abstract-analysis) (make-abstract-analysis e vs bs))))

(define (abstract-apply-prime v1 v2 bs)
 (if (empty-abstract-value? v2)
     (empty-abstract-analysis)
     (reduce
      abstract-analysis-union
      (map
       (lambda (u1)
	(cond
	 ((primitive-procedure? u1) (empty-abstract-analysis))
	 ((closure? u1)
	  (abstract-apply-closure
	   (lambda (e vs) (abstract-eval1-prime e vs bs)) u1 v2))
	 (else (compile-time-warning "Target might not be a procedure" u1))))
       (closed-proto-abstract-values v1))
      (empty-abstract-analysis))))

(define (abstract-eval-prime e vs bs)
 (cond
  ((variable-access-expression? e) (empty-abstract-analysis))
  ((lambda-expression? e) (empty-abstract-analysis))
  ((application? e)
   (abstract-analysis-union
    (abstract-analysis-union
     (abstract-eval1-prime
      (application-callee e)
      (map-vector (lambda (i) (vector-ref vs i))
		  (free-variable-indices (application-callee e)))
      bs)
     (abstract-eval1-prime
      (application-argument e)
      (map-vector (lambda (i) (vector-ref vs i))
		  (free-variable-indices (application-argument e)))
      bs))
    (abstract-apply-prime
     (abstract-eval1
      (application-callee e)
      (map-vector (lambda (i) (vector-ref vs i))
		  (free-variable-indices (application-callee e)))
      bs)
     (abstract-eval1
      (application-argument e)
      (map-vector (lambda (i) (vector-ref vs i))
		  (free-variable-indices (application-argument e)))
      bs)
     bs)))
  ((letrec-expression? e)
   (abstract-eval1-prime
    (letrec-expression-body e)
    (let ((vs (list->vector
	       (append
		(vector->list vs)
		(let ((xs0 (letrec-expression-bodies-free-variables e))
		      (vs (map-vector
			   (lambda (i) (vector-ref vs i))
			   (letrec-expression-bodies-free-variable-indices e)))
		      (xs1 (list->vector
			    (letrec-expression-procedure-variables e)))
		      (xs2 (list->vector
			    (letrec-expression-argument-variables e)))
		      (es (list->vector (letrec-expression-bodies e))))
		 (map-n
		  (lambda (i)
		   (make-abstract-recursive-closure xs0 vs xs1 xs2 es i e vs))
		  (length (letrec-expression-procedure-variables e))))))))
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (letrec-expression-body e))))
    bs))
  ((cons-expression? e)
   (abstract-analysis-union
    (abstract-eval1-prime
     (cons-expression-car e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (cons-expression-car e)))
     bs)
    (abstract-eval1-prime
     (cons-expression-cdr e)
     (map-vector (lambda (i) (vector-ref vs i))
		 (free-variable-indices (cons-expression-cdr e)))
     bs)))
  (else (internal-error))))

(define (update-analysis-ranges bs)
 (map (lambda (b1)
       (make-expression-binding
	(expression-binding-expression b1)
	(map (lambda (b2)
	      (make-environment-binding
	       (environment-binding-values b2)
	       (widen-abstract-value
		(abstract-eval (expression-binding-expression b1)
			       (environment-binding-values b2)
			       bs)
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

(define (flow-analysis e bs)
 (let loop ((bs (widen-analysis-domains (initial-abstract-analysis e bs) '())))
  (let ((bs1 (widen-analysis-domains
	      (abstract-analysis-union (update-analysis-ranges bs)
				       (update-analysis-domains bs))
	      bs)))
   (if (abstract-analysis=? bs1 bs) bs (loop bs1)))))

;;; Abstract Basis

;;; \AB{U} -> \AB{V}
(define (abstract-vlad-car-u u tags)
 (if (vlad-pair? u tags)
     (if *church-pairs?*
	 (unimplemented "abstract-vlad-car-u for Church pairs")
	 (tagged-pair-car u))
     (compile-time-warning "Might attempt to take car of a non-pair" u)))

;;; \AB{U} -> \AB{V}
(define (abstract-vlad-cdr-u u tags)
 (if (vlad-pair? u tags)
     (if *church-pairs?*
	 (unimplemented "abstract-vlad-cdr-u for Church pairs")
	 (tagged-pair-cdr u))
     (compile-time-warning "Might attempt to take cdr of a non-pair" u)))

;;; [\AB{V}]* x [tag]* -> \AB{V}
(define (abstract-listify vs tags)
 (if *church-pairs?*
     (unimplemented "abstract-listify for Church pairs")
     (let loop ((vs vs))
      (if (null? vs)
	  (let loop ((tags tags))
	   (if (null? tags)
	       '(())
	       ((case (first tags)
		 ((forward) abstract-j*-v)
		 ((reverse) abstract-*j-v)
		 (else (internal-error)))
		(loop (rest tags)))))
	  ;; needs work: to give the index-expression and index-environment
	  (make-abstract-tagged-pair
	   tags (first vs) (loop (rest vs)) #f #f)))))

(define (abstract-base-variables-v v)
 (when (and (list? v) (not (= (length v) 1)))
  (internal-error "How to handle abstract-base-variables-v for v?: ~s" v))
 (unless (list? v) (internal-error "Why isn't v a list?: ~s" v))
 (abstract-base-variables-u (first v)))

;;; \AB{U} -> [variable]*
(define (abstract-base-variables-u u)
 (cond ((primitive-procedure? u) '())
       ((closure? u)
	(let ((xs (closure-variables u)))
	 (if (null? (closure-tags u))
	     xs
	     (case (first (closure-tags u))
	      ((forward)
	       (forward-uptag-variables
		(abstract-base-variables-v (abstract-primal-u u)) xs))
	      ((reverse)
	       (reverse-uptag-variables
		(abstract-base-variables-v (abstract-*j-inverse-u u)) xs))
	      (else (internal-error))))))
       (else (internal-error))))

;;; \AB{U} -> [\AB{V}]*
(define (abstract-base-values-u u)
 (let ((xs (closure-variables u)) (vs (closure-values u)))
  (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
       (abstract-base-variables-u u))))

;;; \AB{V} -> \AB{V}
(define (abstract-zero-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-zero-u v)
	     (empty-abstract-value))))

;;; \AB{U} -> \AB{V}
(define (abstract-zero-u u)
 (cond ((null? u) '(()))
       ((and (not *church-booleans?*) (vlad-boolean? u)) '(()))
       ((abstract-real? u) '(0))
       ((primitive-procedure? u) '(()))
       ((closure? u)
	(abstract-listify (map abstract-zero-v (abstract-base-values-u u))
			  (closure-tags u)))
       ((bundle? u)
	(make-abstract-bundle (abstract-zero-v (bundle-primal u))
			      (abstract-zero-v (bundle-tangent u))))
       ((reverse-tagged-value? u)
	(make-abstract-reverse-tagged-value
	 (abstract-zero-v (reverse-tagged-value-primal u))))
       ((and (not *church-pairs?*) (tagged-pair? u))
	(make-abstract-tagged-pair
	 (tagged-pair-tags u)
	 (abstract-zero-v (abstract-vlad-car-u u (tagged-pair-tags u)))
	 (abstract-zero-v (abstract-vlad-cdr-u u (tagged-pair-tags u)))
	 (tagged-pair-index-expression u)
	 (tagged-pair-index-environment u)))
       (else (internal-error))))

;;; Forward Mode

(define (abstract-primal-v v-forward)
 (if (up? v-forward)
     v-forward
     (reduce abstract-value-union-without-unroll
	     (map abstract-primal-u v-forward)
	     (empty-abstract-value))))

(define (abstract-primal-u u-forward)
 (cond ((null? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((and (not *church-booleans?*) (vlad-boolean? u-forward))
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((abstract-real? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((primitive-procedure? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((nonrecursive-closure? u-forward)
	(if (or (null? (nonrecursive-closure-tags u-forward))
		(not (eq? (first (nonrecursive-closure-tags u-forward))
			  'forward)))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)
	    (let ((b (find-if
		      (lambda (b)
		       ;; needs work: imprecision
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)))
	     (if b
		 (vlad-value->abstract-value (value-binding-value b))
		 (make-abstract-nonrecursive-closure
		  ;; We don't do add/remove-slots here.
		  (map-vector abstract-primal-v
			      (nonrecursive-closure-values u-forward))
		  (forward-transform-inverse
		   (new-lambda-expression
		    (nonrecursive-closure-variable u-forward)
		    (nonrecursive-closure-body u-forward)))
		  ;; needs work: tangent of bundle gives the index-expression
		  ;;             and index-environment of the primal
		  (nonrecursive-closure-index-environment u-forward))))))
       ((recursive-closure? u-forward)
	(if (or (null? (recursive-closure-tags u-forward))
		(not (eq? (first (recursive-closure-tags u-forward))
			  'forward)))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)
	    (let ((b (find-if
		      (lambda (b)
		       ;; needs work: imprecision
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)))
	     (if b
		 (vlad-value->abstract-value (value-binding-value b))
		 (let* ((es (vector->list
			     (map-vector
			      (lambda (x e)
			       (forward-transform-inverse
				(new-lambda-expression x e)))
			      (recursive-closure-argument-variables u-forward)
			      (recursive-closure-bodies u-forward))))
			(xs1 (map-vector unforwardify
					 (recursive-closure-procedure-variables
					  u-forward)))
			(xs (letrec-recursive-closure-variables
			     (vector->list xs1)
			     (map lambda-expression-variable es)
			     (map lambda-expression-body es))))
		  (make-abstract-recursive-closure
		   xs
		   ;; We don't do add/remove-slots here.
		   (map-vector abstract-primal-v
			       (recursive-closure-values u-forward))
		   xs1
		   (list->vector (map lambda-expression-variable es))
		   (list->vector (map lambda-expression-body es))
		   (recursive-closure-index u-forward)
		   ;; needs work: tangent of bundle gives the index-expression
		   ;;             and index-environment of the primal
		   (recursive-closure-index-expression u-forward)
		   (recursive-closure-index-environment u-forward)))))))
       ((bundle? u-forward) (bundle-primal u-forward))
       ((reverse-tagged-value? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((and (not *church-pairs?*) (tagged-pair? u-forward))
	(if (or (null? (tagged-pair-tags u-forward))
		(not (eq? (first (tagged-pair-tags u-forward)) 'forward)))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)
	    (make-abstract-tagged-pair
	     (rest (tagged-pair-tags u-forward))
	     (abstract-primal-v (tagged-pair-car u-forward))
	     (abstract-primal-v (tagged-pair-cdr u-forward))
	     ;; needs work: tangent of bundle gives the index-expression and
	     ;;             index-environment of the primal
	     (tagged-pair-index-expression u-forward)
	     (tagged-pair-index-environment u-forward))))
       (else (internal-error))))

(define (abstract-tangent-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-tangent-u v)
	     (empty-abstract-value))))

(define (abstract-tangent-u u-forward)
 (cond ((null? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((and (not *church-booleans?*) (vlad-boolean? u-forward))
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((abstract-real? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((primitive-procedure? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((closure? u-forward)
	(if (or (null? (closure-tags u-forward))
		(not (eq? (first (closure-tags u-forward)) 'forward)))
	    (compile-time-warning
	     "Might attempt to take tangent of a non-forward value" u-forward)
	    (if (some (lambda (b)
		       ;; needs work: imprecision
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)
		'(())
		(abstract-listify
		 (map abstract-tangent-v (abstract-base-values-u u-forward))
		 (rest (closure-tags u-forward))))))
       ((bundle? u-forward) (bundle-tangent u-forward))
       ((reverse-tagged-value? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((and (not *church-pairs?*) (tagged-pair? u-forward))
	(if (or (null? (tagged-pair-tags u-forward))
		(not (eq? (first (tagged-pair-tags u-forward)) 'forward)))
	    (compile-time-warning
	     "Might attempt to take tangent of a non-forward value" u-forward)
	    (make-abstract-tagged-pair
	     (rest (tagged-pair-tags u-forward))
	     (abstract-tangent-v (tagged-pair-car u-forward))
	     (abstract-tangent-v (tagged-pair-cdr u-forward))
	     ;; needs work: tangent of bundle gives the index-expression and
	     ;;             index-environment of the primal
	     (tagged-pair-index-expression u-forward)
	     (tagged-pair-index-environment u-forward))))
       (else (internal-error))))

(define (abstract-tagged-null? tags u vs-above)
 ;; vs-above is the context for u
 (if (null? tags)
     (null? u)
     (case (first tags)
      ((forward)
       (and
	(bundle? u)
	(let ((v (bundle-primal u)))
	 (some (lambda (u)
		(abstract-tagged-null?
		 (rest tags)
		 u
		 (if (up? v) (rest* vs-above (up-index v)) (cons v vs-above))))
	       (if (up? v) (list-ref vs-above (up-index v)) v)))
	(let ((v (bundle-tangent u)))
	 (some (lambda (u)
		(abstract-tagged-null?
		 (rest tags)
		 u
		 (if (up? v) (rest* vs-above (up-index v)) (cons v vs-above))))
	       (if (up? v) (list-ref vs-above (up-index v)) v)))))
      ((reverse)
       (and
	(reverse-tagged-value? u)
	(let ((v (reverse-tagged-value-primal u)))
	 (some (lambda (u)
		(abstract-tagged-null?
		 (rest tags)
		 u
		 (if (up? v) (rest* vs-above (up-index v)) (cons v vs-above))))
	       (if (up? v) (list-ref vs-above (up-index v)) v)))))
      (else (internal-error)))))

(define (abstract-legitimate-list? vs u-perturbation tags vs-above cs)
 ;; vs-above is the context for u-perturbation
 (or (and (null? vs) (abstract-tagged-null? tags u-perturbation vs-above))
     (and (not (null? vs))
	  (vlad-pair? u-perturbation tags)
	  (abstract-legitimate?
	   (first vs) (abstract-vlad-car-u u-perturbation tags) vs-above cs)
	  (let ((v-perturbation (abstract-vlad-cdr-u u-perturbation tags)))
	   (some (lambda (u-perturbation)
		  (abstract-legitimate-list?
		   (rest vs)
		   u-perturbation
		   tags
		   (if (up? v-perturbation)
		       (rest* vs-above (up-index v-perturbation))
		       (cons v-perturbation vs-above))
		   cs))
		 (if (up? v-perturbation)
		     (list-ref vs-above (up-index v-perturbation))
		     v-perturbation))))))

(define (abstract-legitimate? v v-perturbation vs-above cs)
 ;; vs-above is the context for v-perturbation
 (cond
  ((up? v)
   (abstract-legitimate?
    (car (list-ref cs (up-index v))) v-perturbation vs-above cs))
  ((up? v-perturbation)
   (abstract-legitimate? v
			 (list-ref vs-above (up-index v-perturbation))
			 (rest* vs-above (+ (up-index v-perturbation) 1))
			 cs))
  (else
   (let ((i (position-if
	     (lambda (c) (and (eq? (car c) v) (eq? (cdr c) v-perturbation)))
	     cs)))
    (or
     (not (eq? i #f))
     (some
      (lambda (u)
       (some
	(lambda (u-perturbation)
	 (or
	  (and (null? u) (null? u-perturbation))
	  (and (not *church-booleans?*)
	       (vlad-boolean? u)
	       (null? u-perturbation))
	  (and (abstract-real? u) (abstract-real? u-perturbation))
	  (and (primitive-procedure? u) (null? u-perturbation))
	  (and (closure? u)
	       (abstract-legitimate-list? (abstract-base-values-u u)
					  u-perturbation
					  (closure-tags u)
					  (cons v-perturbation vs-above)
					  (cons (cons v v-perturbation) cs)))
	  (and (bundle? u)
	       (bundle? u-perturbation)
	       (abstract-legitimate? (bundle-primal u)
				     (bundle-primal u-perturbation)
				     (cons v-perturbation vs-above)
				     (cons (cons v v-perturbation) cs))
	       (abstract-legitimate? (bundle-tangent u)
				     (bundle-tangent u-perturbation)
				     (cons v-perturbation vs-above)
				     (cons (cons v v-perturbation) cs)))
	  (and (reverse-tagged-value? u)
	       (reverse-tagged-value? u-perturbation)
	       (abstract-legitimate?
		(reverse-tagged-value-primal u)
		(reverse-tagged-value-primal u-perturbation)
		(cons v-perturbation vs-above)
		(cons (cons v v-perturbation) cs)))
	  (and (not *church-pairs?*)
	       (tagged-pair? u)
	       (tagged-pair? u-perturbation)
	       (equal? (tagged-pair-tags u)
		       (tagged-pair-tags u-perturbation))
	       (abstract-legitimate? (tagged-pair-car u)
				     (tagged-pair-car u-perturbation)
				     (cons v-perturbation vs-above)
				     (cons (cons v v-perturbation) cs))
	       (abstract-legitimate? (tagged-pair-cdr u)
				     (tagged-pair-cdr u-perturbation)
				     (cons v-perturbation vs-above)
				     (cons (cons v v-perturbation) cs)))))
	v-perturbation))
      v))))))

(define (abstract-bundle-list vs u-perturbation tags vs-above cs)
 ;; vs-above is the context for u-perturbation
 (if (null? vs)
     (cond ((abstract-tagged-null? tags u-perturbation vs-above) '(()))
	   (else
	    (compile-time-warning
	     "The arguments to bundle might be illegitimate" u-perturbation)
	    '()))
     (cond ((vlad-pair? u-perturbation tags)
	    (let ((v (abstract-bundle-internal
		      (first vs)
		      (abstract-vlad-car-u u-perturbation tags)
		      vs-above
		      cs))
		  (v-perturbation (abstract-vlad-cdr-u u-perturbation tags)))
	     (reduce
	      append
	      (map (lambda (u-perturbation)
		    (map (lambda (vs) (cons v vs))
			 (abstract-bundle-list
			  (rest vs)
			  u-perturbation
			  tags
			  (if (up? v-perturbation)
			      (rest* vs-above (up-index v-perturbation))
			      (cons v-perturbation vs-above))
			  cs)))
		   (if (up? v-perturbation)
		       (list-ref vs-above (up-index v-perturbation))
		       v-perturbation))
	      '())))
	   (else
	    (compile-time-warning
	     "The arguments to bundle might be illegitimate" u-perturbation)
	    '()))))

(define (abstract-bundle-internal v v-perturbation vs-above cs)
 ;; vs-above is the context for v-perturbation
 (cond
  ((up? v)
   (abstract-bundle-internal
    (car (list-ref cs (up-index v))) v-perturbation vs-above cs))
  ((up? v-perturbation)
   (abstract-bundle-internal v
			     (list-ref vs-above (up-index v-perturbation))
			     (rest* vs-above (+ (up-index v-perturbation) 1))
			     cs))
  (else
   (let ((i (position-if
	     (lambda (c) (and (eq? (car c) v) (eq? (cdr c) v-perturbation)))
	     cs)))
    (if (eq? i #f)
	(reduce
	 abstract-value-union-without-unroll
	 (map
	  (lambda (u)
	   (reduce
	    abstract-value-union-without-unroll
	    (map
	     (lambda (u-perturbation)
	      (cond
	       ((and (null? u) (null? u-perturbation))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (not *church-booleans?*)
		     (vlad-boolean? u)
		     (null? u-perturbation))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (abstract-real? u) (abstract-real? u-perturbation))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (primitive-procedure? u) (null? u-perturbation))
		(vlad-value->abstract-value (primitive-procedure-forward u)))
	       ((and
		 (nonrecursive-closure? u)
		 (abstract-legitimate-list? (abstract-base-values-u u)
					    u-perturbation
					    (closure-tags u)
					    (cons v-perturbation vs-above)
					    (cons (cons v v-perturbation) cs)))
		(let* ((e (forward-transform
			   (new-lambda-expression
			    (nonrecursive-closure-variable u)
			    (nonrecursive-closure-body u))))
		       (x (lambda-expression-variable e))
		       (xs (free-variables e))
		       (xs1 (abstract-base-variables-u u))
		       (is (map (lambda (x) (positionp variable=? x xs1))
				(nonrecursive-closure-variables u))))
		 (map (lambda (vs)
		       ;; needs work: should use
		       ;;             make-abstract-nonrecursive-closure
		       (make-nonrecursive-closure
			xs
			;; This should use a generalized add/remove-slots here.
			(list->vector
			 (map (lambda (i v)
			       (if i (list-ref vs i) (abstract-j*-v v)))
			      is
			      (vector->list (nonrecursive-closure-values u))))
			x
			(lambda-expression-body e)
			;; needs work: tangent of bundle gives the
			;;             index-expression and index-environment
			;;             of the primal
			(nonrecursive-closure-index-expression u)
			(nonrecursive-closure-index-environment u)))
		      (abstract-bundle-list
		       (abstract-base-values-u u)
		       u-perturbation
		       (nonrecursive-closure-tags u)
		       (cons v-perturbation vs-above)
		       (cons (cons v v-perturbation) cs)))))
	       ((and
		 (recursive-closure? u)
		 (abstract-legitimate-list? (abstract-base-values-u u)
					    u-perturbation
					    (closure-tags u)
					    (cons v-perturbation vs-above)
					    (cons (cons v v-perturbation) cs)))
		(let* ((es (vector->list
			    (map-vector
			     (lambda (x e)
			      (forward-transform (new-lambda-expression x e)))
			     (recursive-closure-argument-variables u)
			     (recursive-closure-bodies u))))
		       (xs1 (map-vector
			     forwardify
			     (recursive-closure-procedure-variables u)))
		       (xs (letrec-recursive-closure-variables
			    (vector->list xs1)
			    (map lambda-expression-variable es)
			    (map lambda-expression-body es)))
		       (xs2 (abstract-base-variables-u u))
		       (is (map (lambda (x) (positionp variable=? x xs2))
				(recursive-closure-variables u))))
		 (map (lambda (vs)
		       ;; needs work: should use
		       ;;             make-abstract-recursive-closure
		       (make-recursive-closure
			xs
			;; This should use a generalized add/remove-slots here.
			(list->vector
			 (map (lambda (i v)
			       (if i (list-ref vs i) (abstract-j*-v v)))
			      is
			      (vector->list (recursive-closure-values u))))
			xs1
			(list->vector (map lambda-expression-variable es))
			(list->vector (map lambda-expression-body es))
			(recursive-closure-index u)
			;; needs work: tangent of bundle gives the
			;;             index-expression and index-environment
			;;             of the primal
			(recursive-closure-index-expression u)
			(recursive-closure-index-environment u)))
		      (abstract-bundle-list
		       (abstract-base-values-u u)
		       u-perturbation
		       (recursive-closure-tags u)
		       (cons v-perturbation vs-above)
		       (cons (cons v v-perturbation) cs)))))
	       ((and (bundle? u)
		     (bundle? u-perturbation)
		     (abstract-legitimate? (bundle-primal u)
					   (bundle-primal u-perturbation)
					   (cons v-perturbation vs-above)
					   (cons (cons v v-perturbation) cs))
		     (abstract-legitimate? (bundle-tangent u)
					   (bundle-tangent u-perturbation)
					   (cons v-perturbation vs-above)
					   (cons (cons v v-perturbation) cs)))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (reverse-tagged-value? u)
		     (reverse-tagged-value? u-perturbation)
		     (abstract-legitimate?
		      (reverse-tagged-value-primal u)
		      (reverse-tagged-value-primal u-perturbation)
		      (cons v-perturbation vs-above)
		      (cons (cons v v-perturbation) cs)))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (not *church-pairs?*)
		     (tagged-pair? u)
		     (tagged-pair? u-perturbation)
		     (equal? (tagged-pair-tags u)
			     (tagged-pair-tags u-perturbation))
		     (abstract-legitimate? (tagged-pair-car u)
					   (tagged-pair-car u-perturbation)
					   (cons v-perturbation vs-above)
					   (cons (cons v v-perturbation) cs))
		     (abstract-legitimate? (tagged-pair-cdr u)
					   (tagged-pair-cdr u-perturbation)
					   (cons v-perturbation vs-above)
					   (cons (cons v v-perturbation) cs)))
		(make-abstract-tagged-pair
		 (cons 'forward (tagged-pair-tags u))
		 (abstract-bundle-internal
		  (tagged-pair-car u)
		  (tagged-pair-car u-perturbation)
		  (cons v-perturbation vs-above)
		  (cons (cons v v-perturbation) cs))
		 (abstract-bundle-internal
		  (tagged-pair-cdr u)
		  (tagged-pair-cdr u-perturbation)
		  (cons v-perturbation vs-above)
		  (cons (cons v v-perturbation) cs))
		 ;; needs work: tangent of bundle gives the index-expression
		 ;;             and index-environment of the primal
		 (tagged-pair-index-expression u)
		 (tagged-pair-index-environment u)))
	       (else (compile-time-warning
		      "The arguments to bundle might be illegitimate"
		      u
		      u-perturbation))))
	     v-perturbation)
	    (empty-abstract-value)))
	  v)
	 (empty-abstract-value))
	(make-up i))))))

(define (abstract-bundle v v-perturbation)
 (abstract-bundle-internal v v-perturbation '() '()))

;;; \AB{V} -> \AB{V}
(define (abstract-j*-v v) (abstract-bundle v (abstract-zero-v v)))

;;; \AB{U} -> \AB{V}
(define (abstract-j*-u u) (abstract-bundle (list u) (abstract-zero-u u)))

;;; Reverse Mode

(define (abstract-plus u) (unimplemented "abstract-plus"))

(define (abstract-*j-v v) (unimplemented "abstract-*j-v"))

(define (abstract-*j-u u) (unimplemented "abstract-*j-u"))

(define (abstract-*j-inverse-v v) (unimplemented "abstract-*j-inverse-v"))

(define (abstract-*j-inverse-u u) (unimplemented "abstract-*j-inverse-u"))

;;; Abstract Basis Generators

;;; All these procedures take a function f: \AB{U} -> \AB{U} with the exception
;;;   of abstract-binary-u->v, which takes f: \AB{U} -> \AB{V}
(define (abstract-unary f s) (lambda (u) (list (f u))))

(define (abstract-unary-real f s)
 (lambda (u)
  (cond ((real? u) (list (f u)))
	((abstract-real? u) '(real))
	(else (compile-time-warning
	       (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-unary-predicate f s)
 (lambda (u) (list (if (f u) vlad-true vlad-false))))

(define (abstract-unary-real-predicate f s)
 (lambda (u)
  (cond ((real? u) (list (if (f u) vlad-true vlad-false)))
	((abstract-real? u) (list vlad-true vlad-false))
	(else (compile-time-warning
	       (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-binary f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
     (reduce abstract-value-union
	     (map (lambda (u1)
		   (reduce abstract-value-union
			   (map (lambda (u2) (list (f u1 u2))) v2)
			   (empty-abstract-value)))
		  (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	     (empty-abstract-value))))
   (else (compile-time-warning
	  (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-binary-u->v f s)
 ;; This is different in that f is of type: \AB{U} -> \AB{V}
 (lambda (u)
  (if (vlad-pair? u '())
      (f (closed-proto-abstract-values (abstract-vlad-car-u u '()))
	 (closed-proto-abstract-values (abstract-vlad-cdr-u u '())))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u))))

(define (abstract-binary-real f s)
 (lambda (u)
  (if (vlad-pair? u '())
      (let ((v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
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
			  (format #f "Argument to ~a might be invalid" s) u))))
	    v2)
	   (empty-abstract-value)))
	 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	(empty-abstract-value)))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u))))

(define (abstract-binary-real-predicate f s)
 (lambda (u)
  (if (vlad-pair? u '())
      (let ((v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
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
			  (format #f "Argument to ~a might be invalid" s) u))))
	    v2)
	   (empty-abstract-value)))
	 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	(empty-abstract-value)))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u))))

(define (abstract-ternary f s)
 (lambda (u123)
  (if (vlad-pair? u123 '())
      (let ((v23
	     (closed-proto-abstract-values (abstract-vlad-cdr-u u123 '()))))
       (reduce
	abstract-value-union
	(map
	 (lambda (u1)
	  (reduce
	   abstract-value-union
	   (map (lambda (u23)
		 (if (vlad-pair? u23 '())
		     (let ((v3 (closed-proto-abstract-values
				(abstract-vlad-cdr-u u23 '()))))
		      (reduce
		       abstract-value-union
		       (map (lambda (u2)
			     (reduce abstract-value-union
				     (map (lambda (u3) (list (f u1 u2 u3))) v3)
				     (empty-abstract-value)))
			    (closed-proto-abstract-values
			     (abstract-vlad-car-u u23 '())))
		       (empty-abstract-value)))
		     (compile-time-warning
		      (format #f "Argument to ~a might be invalid" s) u123)))
		v23)
	   (empty-abstract-value)))
	 (closed-proto-abstract-values (abstract-vlad-car-u u123 '())))
	(empty-abstract-value)))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u123))))

;;; Pretty printer for abstract

(define (externalize-proto-abstract-value u)
 (cond ((and (or (not *unabbreviate-transformed?*)
		 (and (not *church-pairs?*) (tagged-pair? u)))
	     (vlad-forward? u))
	`(forward ,(externalize-abstract-value (abstract-primal-u u))
		  ,(externalize-abstract-value (abstract-tangent-u u))))
       ((null? u) '())
       ((vlad-true? u) #t)
       ((vlad-false? u) #f)
       ((abstract-real? u) u)
       ;; Whenever u is a pair and the cdr of u is a singleton abstract value
       ;; which is a closure, the pretty-printing of the closure is affected
       ;; because the closure is outputted as a list.
       ((vlad-pair? u '())
	(cons (externalize-abstract-value (abstract-vlad-car-u u '()))
	      (externalize-abstract-value (abstract-vlad-cdr-u u '()))))
       ((primitive-procedure? u) (primitive-procedure-name u))
       ((nonrecursive-closure? u)
	`(nonrecursive-closure
	  ,(externalize-abstract-environment
	    (nonrecursive-closure-variables u)
	    (nonrecursive-closure-values u))
	  ,(abstract->concrete
	    (new-lambda-expression (nonrecursive-closure-variable u)
				   (nonrecursive-closure-body u)))))
       ((recursive-closure? u)
	`(recursive-closure
	  ,(externalize-abstract-environment
	    (recursive-closure-variables u) (recursive-closure-values u))
	  ,(vector->list
	    (map-vector (lambda (x e) (list x (abstract->concrete e)))
			(recursive-closure-procedure-variables u)
			(recursive-closure-procedure-lambda-expressions u)))
	  ,(vector-ref (recursive-closure-procedure-variables u)
		       (recursive-closure-index u))))
       ((bundle? u)
	;; Only needed for *unabbreviate-transformed?*.
	`(forward ,(externalize-abstract-value (bundle-primal u))
		  ,(externalize-abstract-value (bundle-tangent u))))
       ((reverse-tagged-value? u)
	;; Only needed for *unabbreviate-transformed?*.
	`(reverse
	  ,(externalize-abstract-value (reverse-tagged-value-primal u))))
       (else (internal-error "Not a proto-abstract-value: ~s" u))))

(define (externalize-abstract-value v)
 (cond ((up? v) `(up ,(up-index v)))
       ((list? v)
	(cond ((empty-abstract-value? v) 'bottom)
	      ((empty-abstract-value? (rest v))
	       (externalize-proto-abstract-value (first v)))
	      (else `(union ,@(map externalize-proto-abstract-value v)))))
       (else (internal-error "Not an abstract value: ~s" v))))

(define (externalize-abstract-environment xs vs)
 (unless (and (vector? vs)
	      (every-vector (lambda (v) (or (list? v) (up? v))) vs)
	      (= (length xs) (vector-length vs)))
  (internal-error "Not an abstract environment"))
 (map (lambda (x v) (list x (externalize-abstract-value v)))
      xs (vector->list vs)))

(define (externalize-abstract-environment-binding xs b)
 (unless (environment-binding? b)
  (internal-error "Not an abstract environment binding"))
 (list (externalize-abstract-environment xs (environment-binding-values b))
       (externalize-abstract-value (environment-binding-value b))))

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

(define (read-real) (unimplemented "read-real"))

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
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f (vlad-car x '()) (vlad-cdr x '()))))

(define (binary-real f s)
 (lambda (x)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x '())) (x2 (vlad-cdr x '())))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 x2))))

(define (binary-real-predicate f s)
 (lambda (x)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x '())) (x2 (vlad-cdr x '())))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (f x1 x2) vlad-true vlad-false))))

(define (ternary f s)
 (lambda (x)
  (unless (vlad-pair? x '())
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x23 (vlad-cdr x '())))
   (unless (vlad-pair? x23 '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f (vlad-car x '()) (vlad-car x23 '()) (vlad-cdr x23 '())))))

(define (define-primitive-procedure
	 x procedure abstract-procedure forward reverse)
 (set! *value-bindings*
       (cons (make-value-binding
	      x
	      (make-primitive-procedure
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
       (if *church-booleans?*
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
	      (new-variable-access-expression 'x2)))
	    ;; needs work: to fill in index-expression
	    #f
	    '#())
	   #t))
 (set! vlad-false
       (if *church-booleans?*
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
	      (new-variable-access-expression 'x2)))
	    ;; needs work: to fill in index-expression
	    #f
	    '#())
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
 (unless *church-booleans?*
  (define-primitive-procedure 'if-procedure
   (ternary (lambda (x1 x2 x3) (if x1 x2 x3)) "if-procedure")
   (abstract-ternary (lambda (x1 x2 x3) (if x1 x2 x3)) "if-procedure")
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
 (unless *church-pairs?*
  (define-primitive-procedure 'car
   (unary (lambda (x) (vlad-car x '())) "car")
   (unary (lambda (u) (abstract-vlad-car-u u '())) "car")
   '(lambda ((forward x))
     (let (((cons x1 x2) (primal (forward x)))
	   ((cons x1-tangent x2-tangent) (tangent (forward x))))
      (bundle x1 x1-tangent)))
   '(lambda ((reverse x))
     (let (((cons x1 x2) (*j-inverse (reverse x))))
      (cons (*j x1)
	    (lambda ((sensitivity y))
	     (cons '() (cons (sensitivity y) (zero x2))))))))
  (define-primitive-procedure 'cdr
   (unary (lambda (x) (vlad-cdr x '())) "cdr")
   (unary (lambda (u) (abstract-vlad-cdr-u u '())) "cdr")
   '(lambda ((forward x))
     (let (((cons x1 x2) (primal (forward x)))
	   ((cons x1-tangent x2-tangent) (tangent (forward x))))
      (bundle x2 x2-tangent)))
   '(lambda ((reverse x))
     (let (((cons x1 x2) (*j-inverse (reverse x))))
      (cons (*j x2)
	    (lambda ((sensitivity y))
	     (cons '() (cons (zero x1) (sensitivity y)))))))))
 (define-primitive-procedure 'read-real
  (lambda (x) (read-real))
  (lambda (u) '(real))
  ;; needs work: is this right?
  '(lambda ((forward (ignore))) (bundle (read-real) (read-real)))
  ;; needs work: is this right?
  '(lambda ((reverse (ignore)))
    (cons (*j (read-real))
	  (lambda ((sensitivity y)) (cons '() (sensitivity y))))))
 (define-primitive-procedure 'real
  (unary-real identity "real")
  (abstract-unary-real (lambda (u) 'real) "real")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle x (perturbation x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j x) (lambda ((sensitivity y)) (cons '() (sensitivity y)))))))
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write")
  (abstract-unary identity "write")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (write x) (perturbation x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write x))
	   (lambda ((sensitivity y)) (cons '() (sensitivity y)))))))
 (define-primitive-procedure 'zero
  (unary zero "zero")
  (unary abstract-zero-u "zero")
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
  (unary abstract-primal-u "primal")
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
  (unary abstract-tangent-u "tangent")
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
  (abstract-binary-u->v abstract-bundle "bundle")
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
  (unary abstract-j*-u "j*")
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
  (unary abstract-*j-u "*j")
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
  (unary abstract-*j-inverse-u "*j-inverse")
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
