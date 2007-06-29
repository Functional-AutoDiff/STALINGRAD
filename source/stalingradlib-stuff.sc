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
 name procedure abstract-procedure generator forward reverse meter)

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

;;; A proto abstract value is
;;; - (),
;;; - #t,
;;; - #f,
;;; - a real,
;;; - real,
;;; - a primitive procedure,
;;; - a nonrecursive closure,
;;; - a recursive closure,
;;; - a bundle,
;;; - a reverse tagged value, or
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

(define *imprecise-zero?* #f)

(define *imprecise-inexacts?* #f)

(define *union-free?* #f)

(define *verbose?* #f)

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
 (or (null? v) (boolean? v) (real? v) (primitive-procedure? v)))

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

(define (vlad-boolean? v) (or (vlad-true? v) (vlad-false? v)))

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

(define (create-tagged-pair tags v1 v2)
 ;; We intentionally don't give the index-expression and index-environment
 ;; since these are only used during flow analysis.
 (make-tagged-pair tags v1 v2 #f #f))

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
		  (new-variable-access-expression 'x2)))
       ;; needs work: to fill in index-expression
       #f
       vs))
     (create-tagged-pair '() v1 v2)))

(define (vlad-equal? v1 v2)
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (and (not *encoded-booleans?*)
	  (or (and (vlad-true? v1) (vlad-true? v2))
	      (and (vlad-false? v1) (vlad-false? v2))))
     ;; This was = but then it equates exact values with inexact values and
     ;; this breaks -imprecise-inexacts.
     (and (real? v1) (real? v2) (equal? v1 v2))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (= (vector-length (closure-values v1))
	     (vector-length (closure-values v2)))
	  (alpha-equivalent?
	   (closure-body v1)
	   (closure-body v2)
	   (cons (closure-variable v1) (closure-variables v1))
	   (cons (closure-variable v2) (closure-variables v2)))
	  ;; This assumes that the free variables in two alpha-equivalent
	  ;; expressions are in the same order. Note that this is a weak notion
	  ;; of equivalence. A stronger notion would attempt to find a
	  ;; correspondence between the free variables that would allow them
	  ;; to be contextually alpha equivalent.
	  (every-vector vlad-equal? (closure-values v1) (closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (= (vector-length (recursive-closure-bodies v1))
	     (vector-length (recursive-closure-bodies v2)))
	  (= (recursive-closure-index v1) (recursive-closure-index v2))
	  (= (vector-length (closure-values v1))
	     (vector-length (closure-values v2)))
	  (every-vector
	   (lambda (x1 x2 e1 e2)
	    (alpha-equivalent?
	     e1
	     e2
	     (cons x1
		   (append
		    (vector->list (recursive-closure-procedure-variables v1))
		    (closure-variables v1)))
	     (cons x2
		   (append
		    (vector->list (recursive-closure-procedure-variables v2))
		    (closure-variables v2)))))
	   (recursive-closure-argument-variables v1)
	   (recursive-closure-argument-variables v2)
	   (recursive-closure-bodies v1)
	   (recursive-closure-bodies v2))
	  ;; See the note above.
	  (every-vector vlad-equal? (closure-values v1) (closure-values v2)))
     (and (bundle? v1)
	  (bundle? v2)
	  (vlad-equal? (bundle-primal v1) (bundle-primal v2))
	  (vlad-equal? (bundle-tangent v1) (bundle-tangent v2)))
     (and (reverse-tagged-value? v1)
	  (reverse-tagged-value? v2)
	  (vlad-equal? (reverse-tagged-value-primal v1)
		       (reverse-tagged-value-primal v2)))
     (and (not *scott-pairs?*)
	  (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))
	  (vlad-equal? (tagged-pair-car v1) (tagged-pair-car v2))
	  (vlad-equal? (tagged-pair-cdr v1) (tagged-pair-cdr v2)))))

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
       ;; needs work: flow analysis requires tagged pairs to have
       ;;             index-expression and index-environment slots
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
  ((and (not *encoded-booleans?*) (boolean? v)) v)
  ((real? v) 0)
  ((primitive-procedure? v) v)
  ((nonrecursive-closure? v)
   (let ((e (new-lambda-expression (closure-variable v) (closure-body v))))
    (make-nonrecursive-closure
     (free-variables e)
     ;; This assumes that the closure variables are in the same order.
     (map-vector zero (closure-values v))
     (lambda-expression-variable e)
     (lambda-expression-body e)
     (nonrecursive-closure-index-expression v)
     (nonrecursive-closure-index-environment v))))
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
     (recursive-closure-index v)
     (recursive-closure-index-expression v)
     (recursive-closure-index-environment v))))
  ((bundle? v)
   (make-bundle (zero (bundle-primal v)) (zero (bundle-tangent v))))
  ((reverse-tagged-value? v)
   (make-reverse-tagged-value (zero (reverse-tagged-value-primal v))))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   (create-tagged-pair (tagged-pair-tags v)
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
  ((and (not *encoded-booleans?*) (boolean? v-forward))
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((real? v-forward)
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((primitive-procedure? v-forward)
   (run-time-error "Attempt to take primal of a non-forward value" v-forward))
  ((nonrecursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error "Attempt to take primal of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (vlad-equal? v-forward
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
		 (lambda-expression-body e))
	  ;; needs work: tangent of bundle gives the index-expression and
	  ;;             index-environment of the primal
	  (nonrecursive-closure-index-expression v-forward)
	  (nonrecursive-closure-index-environment v-forward))))))
  ((recursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error "Attempt to take primal of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (vlad-equal? v-forward
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
	  (recursive-closure-index v-forward)
	  ;; needs work: tangent of bundle gives the index-expression and
	  ;;             index-environment of the primal
	  (recursive-closure-index-expression v-forward)
	  (recursive-closure-index-environment v-forward))))))
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
   ;; needs work: tangent of bundle gives the index-expression and
   ;;             index-environment of the primal
   (create-tagged-pair (remove-oneq 'forward (tagged-pair-tags v-forward))
		       (primal (tagged-pair-car v-forward))
		       (primal (tagged-pair-cdr v-forward))))
  (else (internal-error))))

(define (tangent v-forward)
 (cond
  ((null? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((and (not *encoded-booleans?*) (boolean? v-forward))
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((real? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((primitive-procedure? v-forward)
   (run-time-error "Attempt to take tangent of a non-forward value" v-forward))
  ((nonrecursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error
     "Attempt to take tangent of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (vlad-equal? v-forward
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
		 (lambda-expression-body e))
	  ;; needs work: tangent of bundle gives the index-expression and
	  ;;             index-environment of the primal
	  (nonrecursive-closure-index-expression v-forward)
	  (nonrecursive-closure-index-environment v-forward))))))
  ((recursive-closure? v-forward)
   (unless (forward-variable? (closure-variable v-forward))
    (run-time-error
     "Attempt to take tangent of a non-forward value" v-forward))
   (let ((b (find-if (lambda (b)
		      (vlad-equal? v-forward
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
	  (recursive-closure-index v-forward)
	  ;; needs work: tangent of bundle gives the index-expression and
	  ;;             index-environment of the primal
	  (recursive-closure-index-expression v-forward)
	  (recursive-closure-index-environment v-forward))))))
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
   ;; needs work: tangent of bundle gives the index-expression and
   ;;             index-environment of the primal
   (create-tagged-pair (remove-oneq 'forward (tagged-pair-tags v-forward))
		       (tangent (tagged-pair-car v-forward))
		       (tangent (tagged-pair-cdr v-forward))))
  (else (internal-error))))

(define (legitimate? v v-perturbation)
 (or (and (null? v) (null? v-perturbation))
     (and (not *encoded-booleans?*)
	  (boolean? v)
	  (boolean? v-perturbation)
	  (eq? v v-perturbation))
     (and (real? v) (real? v-perturbation))
     (and (primitive-procedure? v)
	  (primitive-procedure? v-perturbation)
	  (eq? v v-perturbation))
     (and (nonrecursive-closure? v)
	  (nonrecursive-closure? v-perturbation)
	  (= (vector-length (closure-values v))
	     (vector-length (closure-values v-perturbation)))
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in vlad-equal?.
	  (let ((e (new-lambda-expression
		    (closure-variable v) (closure-body v)))
		(e-perturbation
		 (new-lambda-expression (closure-variable v-perturbation)
					(closure-body v-perturbation))))
	   (alpha-equivalent?
	    (lambda-expression-body e)
	    (lambda-expression-body e-perturbation)
	    (cons (lambda-expression-variable e) (free-variables e))
	    (cons (lambda-expression-variable e-perturbation)
		  (free-variables e-perturbation))))
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in vlad-equal?.
	  (every-vector
	   legitimate? (closure-values v) (closure-values v-perturbation)))
     (and (recursive-closure? v)
	  (recursive-closure? v-perturbation)
	  (= (vector-length (recursive-closure-bodies v))
	     (vector-length (recursive-closure-bodies v-perturbation)))
	  (= (recursive-closure-index v)
	     (recursive-closure-index v-perturbation))
	  (= (vector-length (closure-values v))
	     (vector-length (closure-values v-perturbation)))
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in vlad-equal?.
	  (every-vector
	   (lambda (x1 x2 e1 e2)
	    (let ((e (new-lambda-expression x1 e1))
		  (e-perturbation (new-lambda-expression x2 e2)))
	     (alpha-equivalent?
	      (lambda-expression-body e)
	      (lambda-expression-body e-perturbation)
	      (cons
	       (lambda-expression-variable e)
	       (append
		(vector->list (recursive-closure-procedure-variables v))
		(closure-variables v)))
	      (cons (lambda-expression-variable e-perturbation)
		    (append
		     (vector->list
		      (recursive-closure-procedure-variables v-perturbation))
		     (closure-variables v-perturbation))))))
	   (recursive-closure-argument-variables v)
	   (recursive-closure-argument-variables v-perturbation)
	   (recursive-closure-bodies v)
	   (recursive-closure-bodies v-perturbation))
	  ;; This assumes that the corresponding closure variables in v and
	  ;; v-perturbation are in the same order. See the note in vlad-equal?.
	  (every-vector
	   legitimate? (closure-values v) (closure-values v-perturbation)))
     (and (bundle? v)
	  (bundle? v-perturbation)
	  (legitimate? (bundle-primal v)
		       (bundle-primal v-perturbation))
	  (legitimate? (bundle-tangent v)
		       (bundle-tangent v-perturbation)))
     (and (reverse-tagged-value? v)
	  (reverse-tagged-value? v-perturbation)
	  (legitimate? (reverse-tagged-value-primal v)
		       (reverse-tagged-value-primal v-perturbation)))
     (and (not *scott-pairs?*)
	  (tagged-pair? v)
	  (tagged-pair? v-perturbation)
	  (equal-tags? (tagged-pair-tags v) (tagged-pair-tags v-perturbation))
	  (legitimate? (tagged-pair-car v) (tagged-pair-car v-perturbation))
	  (legitimate? (tagged-pair-cdr v)
		       (tagged-pair-cdr v-perturbation)))))

(define (bundle-internal v v-perturbation)
 (cond
  ((null? v) (make-bundle v v-perturbation))
  ((and (not *encoded-booleans?*) (boolean? v)) (make-bundle v v-perturbation))
  ((real? v) (make-bundle v v-perturbation))
  ((primitive-procedure? v) (primitive-procedure-forward v))
  ((nonrecursive-closure? v)
   (let ((e (forward-transform
	     (new-lambda-expression (closure-variable v) (closure-body v)))))
    (make-nonrecursive-closure
     (free-variables e)
     ;; This assumes that the corresponding closure variables in v,
     ;; v-perturbation, and v-forward are in the same order. See the note in
     ;; vlad-equal?.
     (map-vector
      bundle-internal (closure-values v) (closure-values v-perturbation))
     (lambda-expression-variable e)
     (index (lambda-expression-variable e)
	    (free-variables e)
	    (lambda-expression-body e))
     ;; needs work: tangent of bundle gives the index-expression and
     ;;             index-environment of the primal
     (nonrecursive-closure-index-expression v)
     (nonrecursive-closure-index-environment v))))
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
     ;; vlad-equal?.
     (map-vector
      bundle-internal (closure-values v) (closure-values v-perturbation))
     xs1
     (list->vector (map lambda-expression-variable es))
     (list->vector
      (map
       (lambda (e)
	(index (lambda-expression-variable e) xs2 (lambda-expression-body e)))
       es))
     (recursive-closure-index v)
     ;; needs work: tangent of bundle gives the index-expression and
     ;;             index-environment of the primal
     (recursive-closure-index-expression v)
     (recursive-closure-index-environment v))))
  ((bundle? v)
   (make-bundle
    (bundle-internal (bundle-primal v) (bundle-primal v-perturbation))
    (bundle-internal (bundle-tangent v) (bundle-tangent v-perturbation))))
  ((reverse-tagged-value? v)
   (make-reverse-tagged-value
    (bundle-internal (reverse-tagged-value-primal v)
		     (reverse-tagged-value-primal v-perturbation))))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   ;; needs work: tangent of bundle gives the index-expression and
   ;;             index-environment of the primal
   (create-tagged-pair
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
 (or (and (vlad-forward? v1)
	  (vlad-forward? v2)
	  (conform? (primal v1) (primal v2))
	  (conform? (tangent v1) (tangent v2)))
     (and (vlad-reverse? v1)
	  (vlad-reverse? v2)
	  (conform? (*j-inverse v1) (*j-inverse v2)))
     (and (null? v1) (null? v2))
     (and (real? v1) (real? v2))
     (and (vlad-pair? v1 '())
	  (vlad-pair? v2 '())
	  (conform? (vlad-car v1 '()) (vlad-car v2 '()))
	  (conform? (vlad-cdr v1 '()) (vlad-cdr v2 '())))))

(define (plus-internal v1 v2)
 (cond
  ((vlad-forward? v1)
   (bundle (plus-internal (primal v1) (primal v2))
	   (plus-internal (tangent v1) (tangent v2))))
  ((vlad-reverse? v1) (*j (plus-internal (*j-inverse v1) (*j-inverse v2))))
  ((null? v1) '())
  ((real? v1) (+ v1 v2))
  (else (vlad-cons (plus-internal (vlad-car v1 '()) (vlad-car v2 '()))
		   (plus-internal (vlad-cdr v1 '()) (vlad-cdr v2 '()))))))

(define (plus v1 v2)
 (unless (conform? v1 v2)
  (run-time-error "The arguments to plus are nonconformant" v1 v2))
 (plus-internal v1 v2))

(define (*j v)
 (cond
  ((null? v) (make-reverse-tagged-value v))
  ((and (not *encoded-booleans?*) (boolean? v))
   (make-reverse-tagged-value v))
  ((real? v) (make-reverse-tagged-value v))
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
     (index x xs (copy-propagate (anf-convert (lambda-expression-body e))))
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
     (recursive-closure-index v)
     (recursive-closure-index-expression v)
     (recursive-closure-index-environment v))))
  ((bundle? v) (make-reverse-tagged-value v))
  ((reverse-tagged-value? v) (make-reverse-tagged-value v))
  ((and (not *scott-pairs?*) (tagged-pair? v))
   (create-tagged-pair (cons 'reverse (tagged-pair-tags v))
		       (*j (tagged-pair-car v))
		       (*j (tagged-pair-cdr v))))
  (else (internal-error))))

(define (*j-inverse v-reverse)
 (cond
  ((null? v-reverse)
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((and (not *encoded-booleans?*) (boolean? v-reverse))
   (run-time-error
    "Attempt to take *j-inverse of a non-reverse value" v-reverse))
  ((real? v-reverse)
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
   (let ((b (find-if
	     (lambda (b)
	      (vlad-equal?
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
	  (index x xs (copy-propagate (lambda-expression-body e)))
	  (nonrecursive-closure-index-expression v-reverse)
	  (nonrecursive-closure-index-environment v-reverse))))))
  ((recursive-closure? v-reverse)
   (unless (and (not (null? (closure-tags v-reverse)))
		(eq? (first (closure-tags v-reverse)) 'reverse))
    (run-time-error
     "Attempt to take *j-inverse of a non-reverse value" v-reverse))
   (let ((b (find-if
	     (lambda (b)
	      (vlad-equal?
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
	  (recursive-closure-index v-reverse)
	  (recursive-closure-index-expression v-reverse)
	  (recursive-closure-index-environment v-reverse))))))
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
   (create-tagged-pair (rest (tagged-pair-tags v-reverse))
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
		      ((primitive-procedure-procedure callee) argument))
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
			       i
			       (recursive-closure-index-expression callee)
			       (recursive-closure-index-environment callee))))
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

(define (minimal-elements <=? s)
 ;; belongs in QobiScheme
 (remove-if
  (lambda (e)
   (some (lambda (e-prime) (and (not (eq? e-prime e)) (<=? e-prime e))) s))
  s))

(define (maximal-elements <=? s)
 ;; belongs in QobiScheme
 (remove-if
  (lambda (e)
   (some (lambda (e-prime) (and (not (eq? e-prime e)) (<=? e e-prime))) s))
  s))

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

;;; Abstract Nulls

(define (abstract-tagged-null tags)
 (if (null? tags)
     '(())
     (case (first tags)
      ((forward) (let ((v (abstract-tagged-null (rest tags))))
		  (abstract-bundle v (abstract-zero-v v))))
      ((reverse) (abstract-*j-v (abstract-tagged-null (rest tags))))
      (else (internal-error)))))

;;; Abstract Reals

(define (abstract-real? u) (or (real? u) (eq? u 'real)))

;;; Abstract Closures

(define (abstract-closure? v)
 (when (up? v) (internal-error))
 (and (= (length v) 1) (closure? (first v))))

(define (abstract-closure-variable v)
 (when (up? v) (internal-error))
 (unless (= (length v) 1) (internal-error))
 (closure-variable (first v)))

(define (abstract-closure-tags v)
 (when (up? v) (internal-error))
 (unless (= (length v) 1) (internal-error))
 (closure-tags (first v)))

(define (abstract-closure-body v)
 (when (up? v) (internal-error))
 (unless (= (length v) 1) (internal-error))
 (closure-body (first v)))

(define (nonrecursive-closure-extensional-match? u1 u2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (variable=? (closure-variable u1) (closure-variable u2))
	  (expression=? (closure-body u1) (closure-body u2)))))

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
     (list (make-nonrecursive-closure (free-variables e)
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
 (when (up? v) (unimplemented "Reverse taggedvalues with backlinks"))
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
 (equal-tags? (tagged-pair-tags u1) (tagged-pair-tags u2)))

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

(define (abstract-vlad-car-u u tags)
 (if (vlad-pair? u tags)
     (if *scott-pairs?*
	 (unimplemented "abstract-vlad-car-u for Scott pairs")
	 (tagged-pair-car u))
     (compile-time-warning "Might attempt to take car of a non-pair" u)))

(define (abstract-vlad-cdr-u u tags)
 (if (vlad-pair? u tags)
     (if *scott-pairs?*
	 (unimplemented "abstract-vlad-cdr-u for Scott pairs")
	 (tagged-pair-cdr u))
     (compile-time-warning "Might attempt to take cdr of a non-pair" u)))

;;; Abstract Aggregate Values

(define (scalar-proto-abstract-value? u)
 (or (null? u) (boolean? u) (abstract-real? u) (primitive-procedure? u)))

(define (aggregate-value-extensional-match? u1 u2)
 (or (and (closure? u1) (closure? u2) (closure-extensional-match? u1 u2))
     (and (bundle? u1) (bundle? u2) (bundle-extensional-match? u1 u2))
     (and (reverse-tagged-value? u1)
	  (reverse-tagged-value? u2)
	  (reverse-tagged-value-extensional-match? u1 u2))
     (and (tagged-pair? u1)
	  (tagged-pair? u2)
	  (tagged-pair-extensional-match? u1 u2))))

(define (aggregate-value-match? bs)
 (lambda (u1 u2)
  (or
   (and (closure? u1) (closure? u2) ((closure-match? bs) u1 u2))
   (and (bundle? u1) (bundle? u2) ((bundle-match? bs) u1 u2))
   (and (reverse-tagged-value? u1)
	(reverse-tagged-value? u2)
	((reverse-tagged-value-match? bs) u1 u2))
   (and (tagged-pair? u1) (tagged-pair? u2) ((tagged-pair-match? bs) u1 u2)))))

(define (aggregate-value-values u)
 (cond
  ((closure? u) (vector->list (closure-values u)))
  ((bundle? u) (list (bundle-primal u) (bundle-tangent u)))
  ((reverse-tagged-value? u) (list (reverse-tagged-value-primal u)))
  ((tagged-pair? u) (list (tagged-pair-car u) (tagged-pair-cdr u)))
  (else (internal-error))))

(define (make-aggregate-value-with-new-values u vs)
 ;; needs work: To check that no vs is empty-abstract-value.
 (cond ((nonrecursive-closure? u)
	(make-nonrecursive-closure (closure-variables u)
				   (list->vector vs)
				   (closure-variable u)
				   (closure-body u)
				   (nonrecursive-closure-index-expression u)
				   (nonrecursive-closure-index-environment u)))
       ((recursive-closure? u)
	(make-recursive-closure (closure-variables u)
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
       ((reverse-tagged-value? u)
	(when (up? (first vs))
	 (unimplemented "Reverse tagged values with backlinks"))
	(make-reverse-tagged-value (first vs)))
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

(define (potentially-imprecise-vlad-value->abstract-value v)
 (if (scalar-proto-abstract-value? v)
     (list (if (and *imprecise-inexacts?* (real? v) (inexact? v)) 'real v))
     ;; needs work: this doesn't fill in the index-expression and
     ;;             index-environment slots
     (list (make-aggregate-value-with-new-values
	    v (map potentially-imprecise-vlad-value->abstract-value
		   (aggregate-value-values v))))))

(define (remove-redundant-proto-abstract-values v)
 ;; This does not affect the extension of the abstract value but can yield
 ;; a smaller representation. Thus this is just an optimization. Since
 ;; (proto) abstract value subset and equality is undecidable, can only
 ;; conservatively approximate this. This selects among a hierarchy of more
 ;; precise conservative approximation alternatives.
 ;; Using a conservative approximation is sound since proto abstract values are
 ;; removed only when the predicate returns #t which is a precise result for
 ;; all of the approximations.
 (case *method-for-removing-redundant-proto-abstract-values*
  ((identity) (remove-duplicatesq v))
  ((structural) (remove-duplicatesp equalq? v))
  ((equality) (remove-duplicatesp proto-abstract-value=? v))
  ((subset) (maximal-elements proto-abstract-value-subset?
			      (remove-duplicatesp proto-abstract-value=? v)))
  (else (internal-error))))

;;; (Proto-)Abstract-Value Subset, Equality, and Union

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

(define (restrict-environment vs e f)
 (let ((xs (free-variables e)))
  (list->vector
   (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
	(free-variables (f e))))))

(define (letrec-restrict-environment vs e)
 (let ((xs (free-variables e)))
  (list->vector
   (map (lambda (x) (vector-ref vs (positionp variable=? x xs)))
	(letrec-expression-bodies-free-variables e)))))

(define (abstract-environment-subset? vs1 vs2)
 (every-vector abstract-value-subset? vs1 vs2))

(define (abstract-environment=? vs1 vs2)
 (and (abstract-environment-subset? vs1 vs2)
      (abstract-environment-subset? vs2 vs1)))

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
  (list (abstract-value-union-without-unroll
	 (remove-if target-aggregate-value? v)
	 (reduce abstract-value-union-without-unroll
		 (map first v-additions-list)
		 (empty-abstract-value)))
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

(define (widen-abstract-value v bs)
 ;; This can introduce imprecision.
 (let loop ((v (remove-redundant-proto-abstract-values* v)))
  (if (syntactic-constraints-met? v bs)
      (begin (unless (bundle-depth-limit-met? v bs)
	      (compile-time-error "Bundle depth limit exceeded"))
	     v)
      (loop (remove-redundant-proto-abstract-values*
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
   ;; First, that the domains not be equal.
   ((some (lambda (b1)
	   (some (lambda (b2)
		  (and (not (eq? b1 b2))
		       (abstract-environment=?
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
			     (abstract-environment=?
			      (environment-binding-values b1)
			      (environment-binding-values b2))))
		       bs))
		bs))
	   (b2 (find-if (lambda (b2)
			 (and (not (eq? b1 b2))
			      (abstract-environment=?
			       (environment-binding-values b1)
			       (environment-binding-values b2))))
			bs)))
     (loop (cons (make-environment-binding
		  (environment-binding-values b1)
		  (widen-abstract-value
		   (abstract-value-union (environment-binding-value b1)
					 (environment-binding-value b2))
		   bs1))
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
    (if (some (lambda (b1)
	       (some (lambda (b2)
		      (and (not (eq? b1 b2))
			   (abstract-environment-subset?
			    (environment-binding-values b1)
			    (environment-binding-values b2))))
		     bs))
	      bs)
	;; needs work: Should abstract the choice of which environment to
	;;             remove as a pick procedure.
	(loop
	 (removeq (find-if (lambda (b1)
			    (some (lambda (b2)
				   (and (not (eq? b1 b2))
					(abstract-environment-subset?
					 (environment-binding-values b1)
					 (environment-binding-values b2))))
				  bs))
			   bs)
		  bs))
	(let ((b1-b2 (pick-environment-bindings-to-coalesce bs)))
	 (loop
	  (cons (make-environment-binding
		 ;; needs work: This should be removed if not necessary and
		 ;;             moved to abstract-value-union if necessary.
		 (map-vector remove-redundant-proto-abstract-values*
			     (abstract-environment-union
			      (environment-binding-values (first b1-b2))
			      (environment-binding-values (second b1-b2))))
		 (widen-abstract-value
		  (abstract-value-union
		   (environment-binding-value (first b1-b2))
		   (environment-binding-value (second b1-b2)))
		  bs1))
		(removeq (second b1-b2) (removeq (first b1-b2) bs)))))))
   (else bs))))

(define (widen-analysis-domains bs bs1)
 ;; This can introduce imprecision.
 (map (lambda (b)
       (make-expression-binding
	(expression-binding-expression b)
	(widen-abstract-flow (expression-binding-flow b) bs1)))
      bs))

;;; Abstract Interpretation

(define (make-abstract-analysis e vs bs)
 (unless (= (vector-length vs) (length (free-variables e)))
  (internal-error
   "vs and (length (free-variables e)) should be of same length"))
 (if (some-vector empty-abstract-value? vs)
     (empty-abstract-analysis)
     (list (make-expression-binding
	    ;; It doesn't help to initialize the value to
	    ;; (widen-abstract-value (abstract-eval1 e vs bs) bs)
	    ;; because that will always be an empty abstract value.
	    e (list (make-environment-binding vs (empty-abstract-value)))))))

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
    (free-variables e)))
  '()))

(define (lookup-environment-binding e vs bs)
 (let ((b (lookup-expression-binding e bs)))
  ;; needs work: Why don't we select the minimal abstract-value-subset?
  ;;             of environment-binding-value?
  (cond (b (let ((bs (minimal-elements
		      (lambda (b1 b2)
		       (abstract-environment-subset?
			(environment-binding-values b1)
			(environment-binding-values b2)))
		      (remove-if-not (lambda (b)
				      (abstract-environment-subset?
				       vs (environment-binding-values b)))
				     (expression-binding-flow b)))))
	    ;; This is just so we catch an example where this is the case.
	    ;; This occurs in unbounded polyvariant saddle.
	    (when #f
	     (when (> (length bs) 1)
	      (internal-error "Ambiguity in lookup-environment-binding")))
	    (if (null? bs) #f (first bs))))
	(else #f))))

(define (abstract-eval1 e vs bs)
 (let ((b (lookup-environment-binding e vs bs)))
  (if b
      (if (or (abstract-environment=? vs (environment-binding-values b))
	      (and *flow-size-limit*
		   (= (length (expression-binding-flow
			       (lookup-expression-binding e bs)))
		      *flow-size-limit*)))
	  (environment-binding-value b)
	  (empty-abstract-value))
      (empty-abstract-value))))

(define (abstract-apply-closure p u1 v2)
 (cond
  ((nonrecursive-closure? u1)
   (p (closure-body u1)
      (list->vector
       (map (lambda (x)
	     (if (variable=? x (closure-variable u1))
		 v2
		 (vector-ref (closure-values u1)
			     (positionp variable=? x (closure-variables u1)))))
	    (free-variables (closure-body u1))))))
  ((recursive-closure? u1)
   (p (closure-body u1)
      (list->vector
       (map (lambda (x)
	     (cond
	      ((variable=? x (closure-variable u1)) v2)
	      ((some-vector (lambda (x1) (variable=? x x1))
			    (recursive-closure-procedure-variables u1))
	       (make-abstract-recursive-closure
		(closure-variables u1)
		(closure-values u1)
		(recursive-closure-procedure-variables u1)
		(recursive-closure-argument-variables u1)
		(recursive-closure-bodies u1)
		(positionp-vector
		 variable=? x (recursive-closure-procedure-variables u1))
		(recursive-closure-index-expression u1)
		(recursive-closure-index-environment u1)))
	      (else
	       (vector-ref (closure-values u1)
			   (positionp variable=? x (closure-variables u1))))))
	    (free-variables (closure-body u1))))))
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
			((primitive-procedure-abstract-procedure u1) u2 bs))
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
  ((variable-access-expression? e)
   (unless (= (length (free-variables e)) 1) (internal-error))
   (vector-ref vs 0))
  ((lambda-expression? e) (make-abstract-nonrecursive-closure vs e vs))
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
    (letrec-expression-body e)
    (list->vector
     (map (lambda (x)
	   (if (memp variable=? x (letrec-expression-procedure-variables e))
	       (let ((vs (letrec-restrict-environment vs e)))
		(make-abstract-recursive-closure
		 (letrec-expression-bodies-free-variables e)
		 vs
		 (list->vector (letrec-expression-procedure-variables e))
		 (list->vector (letrec-expression-argument-variables e))
		 (list->vector (letrec-expression-bodies e))
		 (positionp
		  variable=? x (letrec-expression-procedure-variables e))
		 e
		 vs))
	       (vector-ref vs (positionp variable=? x (free-variables e)))))
	  (free-variables (letrec-expression-body e))))
    bs))
  ((cons-expression? e)
   (make-abstract-tagged-pair
    (cons-expression-tags e)
    (abstract-eval1 (cons-expression-car e)
		    (restrict-environment vs e cons-expression-car)
		    bs)
    (abstract-eval1 (cons-expression-cdr e)
		    (restrict-environment vs e cons-expression-cdr)
		    bs)
    e
    vs))
  (else (internal-error))))

(define (abstract-eval1-prime e vs bs)
 (let ((b (lookup-environment-binding e vs bs)))
  (if b
      (if (or (abstract-environment=? vs (environment-binding-values b))
	      (and *flow-size-limit*
		   (= (length (expression-binding-flow
			       (lookup-expression-binding e bs)))
		      *flow-size-limit*)))
	  (empty-abstract-analysis)
	  (make-abstract-analysis e vs bs))
      (make-abstract-analysis e vs bs))))

(define (abstract-apply-prime v1 v2 bs)
 (if (empty-abstract-value? v2)
     (empty-abstract-analysis)
     (reduce
      abstract-analysis-union
      (map
       (lambda (u1)
	(cond
	 ((primitive-procedure? u1)
	  ;; needs work: should put this into slots of the primitive
	  ;;             procedures
	  (if (eq? (primitive-procedure-name u1) 'if-procedure)
	      (reduce abstract-analysis-union
		      (map (lambda (u2)
			    ((abstract-ternary-prime-u->v
			      (lambda (u1 u2 u3 bs)
			       (unless (and (nonrecursive-closure? u2)
					    (nonrecursive-closure? u3))
				(run-time-error "You used if-procedure"))
			       (if u1
				   (abstract-apply-closure
				    (lambda (e vs)
				     (abstract-eval1-prime e vs bs))
				    u2
				    (abstract-tagged-null (closure-tags u2)))
				   (abstract-apply-closure
				    (lambda (e vs)
				     (abstract-eval1-prime e vs bs))
				    u3
				    (abstract-tagged-null (closure-tags u3)))))
			      "if-procedure")
			     u2
			     bs))
			   (closed-proto-abstract-values v2))
		      (empty-abstract-analysis))
	      (empty-abstract-analysis)))
	 ((closure? u1)
	  (abstract-apply-closure
	   (lambda (e vs) (abstract-eval1-prime e vs bs)) u1 v2))
	 (else (compile-time-warning "Target might not be a procedure" u1)
	       (empty-abstract-analysis))))
       (closed-proto-abstract-values v1))
      (empty-abstract-analysis))))

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
    (letrec-expression-body e)
    (list->vector
     (map (lambda (x)
	   (if (memp variable=? x (letrec-expression-procedure-variables e))
	       (let ((vs (letrec-restrict-environment vs e)))
		(make-abstract-recursive-closure
		 (letrec-expression-bodies-free-variables e)
		 vs
		 (list->vector (letrec-expression-procedure-variables e))
		 (list->vector (letrec-expression-argument-variables e))
		 (list->vector (letrec-expression-bodies e))
		 (positionp
		  variable=? x (letrec-expression-procedure-variables e))
		 e
		 vs))
	       (vector-ref vs (positionp variable=? x (free-variables e)))))
	  (free-variables (letrec-expression-body e))))
    bs))
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
	      ;; needs work: to do one final pass without this optimization
	      ;;             to check for errors
	      (if (or #t		;debugging
		      (not *union-free?*)
		      (empty-abstract-value? (environment-binding-value b2))
		      (and (= (length (environment-binding-value b2)) 1)
			   (boolean? (first (environment-binding-value b2)))))
		  (make-environment-binding
		   (environment-binding-values b2)
		   ;; Might consider unioning with previous value here.
		   (widen-abstract-value
		    (abstract-eval (expression-binding-expression b1)
				   (environment-binding-values b2)
				   bs)
		    bs))
		  b2))
	     (expression-binding-flow b1))))
      bs))

(define (update-analysis-domains bs)
 (reduce
  abstract-analysis-union
  (map (lambda (b1)
	(reduce
	 abstract-analysis-union
	 (map (lambda (b2)
	       ;; needs work: to do one final pass without this optimization
	       ;;             to check for errors
	       (if (or #t		;debugging
		       (not *union-free?*)
		       (empty-abstract-value? (environment-binding-value b2))
		       (and (= (length (environment-binding-value b2)) 1)
			    (boolean? (first (environment-binding-value b2)))))
		   (abstract-eval-prime
		    (expression-binding-expression b1)
		    (environment-binding-values b2)
		    bs)
		   (empty-abstract-analysis)))
	      (expression-binding-flow b1))
	 (empty-abstract-analysis)))
       bs)
  (empty-abstract-analysis)))

(define (has-nonboolean-union? v)
 (and (not (up? v))
      (or (and (> (length v) 1) (not (boolean-value? v)))
	  (some (lambda (u)
		 (and (not (scalar-proto-abstract-value? u))
		      (some has-nonboolean-union? (aggregate-value-values u))))
		v))))

(define (concrete-reals-in v)
 (if (up? v)
     '()
     (reduce
      unionv
      (map (lambda (u)
	    (cond ((real? u) (list u))
		  ((scalar-proto-abstract-value? u) '())
		  (else (reduce
			 unionv
			 (map concrete-reals-in (aggregate-value-values u))
			 '()))))
	   v)
      '())))

(define (flow-analysis e bs)
 (let loop ((bs (widen-analysis-domains (initial-abstract-analysis e bs) '()))
	    (i 0))
  (when *verbose?* (format #t "~s: " i))
  (let ((bs1 (if *verbose?*
		 (time
		  "~a, "
		  (lambda ()
		   (widen-analysis-domains
		    (abstract-analysis-union (update-analysis-ranges bs)
					     (update-analysis-domains bs))
		    bs)))
		 (widen-analysis-domains
		  (abstract-analysis-union (update-analysis-ranges bs)
					   (update-analysis-domains bs))
		  bs))))
   (when *verbose?*
    (format #t "|analysis|=~s~%"
	    (reduce
	     + (map (lambda (b) (length (expression-binding-flow b))) bs1) 0)))
   (when *verbose?*
    (format #t "expressions: ~s, max flow size: ~s, bottoms: ~s, concrete reals: ~s~%"
	    (length bs)
	    (reduce max
		    (map (lambda (b) (length (expression-binding-flow b))) bs)
		    minus-infinity)
	    (reduce
	     +
	     (map (lambda (b)
		   (count-if (lambda (b) (null? (environment-binding-value b)))
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
   (when *union-free?*
    (when (some (lambda (b)
		 (some (lambda (b)
			(has-nonboolean-union? (environment-binding-value b)))
		       (expression-binding-flow b)))
		bs1)
     (for-each
      (lambda (b)
       (for-each
	(lambda (b1)
	 (when (has-nonboolean-union? (environment-binding-value b1))
	  (pp (list (abstract->concrete (expression-binding-expression b))
		    (externalize-abstract-environment
		     (free-variables (expression-binding-expression b))
		     (environment-binding-values b1))
		    (externalize-abstract-value
		     (environment-binding-value b1))))
	  (newline)))
	(expression-binding-flow b)))
      bs1)
     (compile-time-error "Some value has a non-boolean union"))
    (when (some (lambda (b)
		 (some (lambda (b)
			(some-vector has-nonboolean-union?
				     (environment-binding-values b)))
		       (expression-binding-flow b)))
		bs1)
     (for-each
      (lambda (b)
       (for-each
	(lambda (b1)
	 (when (some-vector has-nonboolean-union?
			    (environment-binding-values b1))
	  (pp (list (abstract->concrete (expression-binding-expression b))
		    (externalize-abstract-environment
		     (free-variables (expression-binding-expression b))
		     (environment-binding-values b1))))
	  (newline)))
	(expression-binding-flow b)))
      bs1)
     (compile-time-error "Some environment has a non-boolean union")))
   (if (abstract-analysis=? bs1 bs) bs (loop bs1 (+ i 1))))))

;;; Abstract Basis

(define (abstract-zero-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-zero-u v)
	     (empty-abstract-value))))

(define (abstract-zero-u u)
 (cond ((null? u) (list u))
       ((and (not *encoded-booleans?*) (boolean? u)) (list u))
       ((abstract-real? u) (if *imprecise-zero?* '(real) '(0)))
       ((primitive-procedure? u) (list u))
       ((nonrecursive-closure? u)
	(make-abstract-nonrecursive-closure
	 ;; This assumes that the closure variables are in the same order.
	 (map-vector abstract-zero-v (closure-values u))
	 (new-lambda-expression (closure-variable u) (closure-body u))
	 (nonrecursive-closure-index-environment u)))
       ((recursive-closure? u)
	(let ((es (map-vector new-lambda-expression
			      (recursive-closure-argument-variables u)
			      (recursive-closure-bodies u))))
	 (make-abstract-recursive-closure
	  ;; This assumes that the closure variables are in the same order.
	  (closure-variables u)
	  (map-vector abstract-zero-v (closure-values u))
	  (recursive-closure-procedure-variables u)
	  (map-vector lambda-expression-variable es)
	  (map-vector lambda-expression-body es)
	  (recursive-closure-index u)
	  (recursive-closure-index-expression u)
	  (recursive-closure-index-environment u))))
       ((bundle? u)
	(make-abstract-bundle (abstract-zero-v (bundle-primal u))
			      (abstract-zero-v (bundle-tangent u))))
       ((reverse-tagged-value? u)
	(make-abstract-reverse-tagged-value
	 (abstract-zero-v (reverse-tagged-value-primal u))))
       ((and (not *scott-pairs?*) (tagged-pair? u))
	(make-abstract-tagged-pair
	 (tagged-pair-tags u)
	 (abstract-zero-v (abstract-vlad-car-u u (tagged-pair-tags u)))
	 (abstract-zero-v (abstract-vlad-cdr-u u (tagged-pair-tags u)))
	 (tagged-pair-index-expression u)
	 (tagged-pair-index-environment u)))
       (else (internal-error))))

;;; Forward Mode

(define (abstract-perturb-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-perturb-u v)
	     (empty-abstract-value))))

(define (abstract-perturb-u u) (unimplemented "abstract-perturb-u"))

(define (abstract-unperturb-v v-perturbation)
 (if (up? v-perturbation)
     v-perturbation
     (reduce abstract-value-union-without-unroll
	     (map abstract-unperturb-u v-perturbation)
	     (empty-abstract-value))))

(define (abstract-unperturb-u u-perturbation)
 (unimplemented "abstract-unperturb-u"))

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
       ((and (not *encoded-booleans?*) (boolean? u-forward))
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((abstract-real? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((primitive-procedure? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((nonrecursive-closure? u-forward)
	(if (forward-variable? (closure-variable u-forward))
	    (let ((b (find-if
		      (lambda (b)
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)))
	     (if b
		 (vlad-value->abstract-value (value-binding-value b))
		 (make-abstract-nonrecursive-closure
		  ;; This assumes that the closure variables are in the same
		  ;; order.
		  (map-vector abstract-primal-v (closure-values u-forward))
		  (forward-transform-inverse
		   (new-lambda-expression
		    (closure-variable u-forward) (closure-body u-forward)))
		  ;; needs work: tangent of bundle gives the index-expression
		  ;;             and index-environment of the primal
		  (nonrecursive-closure-index-environment u-forward))))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)))
       ((recursive-closure? u-forward)
	(if (forward-variable? (closure-variable u-forward))
	    (let ((b (find-if
		      (lambda (b)
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
		   ;; This assumes that the closure variables are in the same
		   ;; order.
		   (map-vector abstract-primal-v (closure-values u-forward))
		   xs1
		   (list->vector (map lambda-expression-variable es))
		   (list->vector (map lambda-expression-body es))
		   (recursive-closure-index u-forward)
		   ;; needs work: tangent of bundle gives the index-expression
		   ;;             and index-environment of the primal
		   (recursive-closure-index-expression u-forward)
		   (recursive-closure-index-environment u-forward)))))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)))
       ((bundle? u-forward)
	(unless (or (every scalar-proto-abstract-value?
			   (bundle-primal u-forward))
		    (not (some scalar-proto-abstract-value?
			       (bundle-primal u-forward))))
	 (unimplemented))
	(if (every scalar-proto-abstract-value? (bundle-primal u-forward))
	    (bundle-primal u-forward)
	    (make-abstract-bundle
	     (abstract-primal-v (bundle-primal u-forward))
	     (abstract-primal-v (bundle-tangent u-forward)))))
       ((reverse-tagged-value? u-forward)
	(make-abstract-reverse-tagged-value
	 (abstract-primal-v (reverse-tagged-value-primal u-forward))))
       ((and (not *scott-pairs?*) (tagged-pair? u-forward))
	(if (memq 'forward (tagged-pair-tags u-forward))
	    (make-abstract-tagged-pair
	     (remove-oneq 'forward (tagged-pair-tags u-forward))
	     (abstract-primal-v (tagged-pair-car u-forward))
	     (abstract-primal-v (tagged-pair-cdr u-forward))
	     ;; needs work: tangent of bundle gives the index-expression and
	     ;;             index-environment of the primal
	     (tagged-pair-index-expression u-forward)
	     (tagged-pair-index-environment u-forward))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)))
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
       ((and (not *encoded-booleans?*) (boolean? u-forward))
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((abstract-real? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((primitive-procedure? u-forward)
	(compile-time-warning
	 "Might attempt to take tangent of a non-forward value" u-forward))
       ((nonrecursive-closure? u-forward)
	(if (forward-variable? (closure-variable u-forward))
	    (let ((b (find-if
		      (lambda (b)
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)))
	     (if b
		 (vlad-value->abstract-value (value-binding-value b))
		 (make-abstract-nonrecursive-closure
		  ;; This assumes that the closure variables are in the same
		  ;; order.
		  (map-vector abstract-tangent-v (closure-values u-forward))
		  (forward-transform-inverse
		   (new-lambda-expression
		    (closure-variable u-forward) (closure-body u-forward)))
		  ;; needs work: tangent of bundle gives the index-expression
		  ;;             and index-environment of the primal
		  (nonrecursive-closure-index-environment u-forward))))
	    (compile-time-warning
	     "Might attempt to take tangent of a non-forward value"
	     u-forward)))
       ((recursive-closure? u-forward)
	(if (forward-variable? (closure-variable u-forward))
	    (let ((b (find-if
		      (lambda (b)
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
		   ;; This assumes that the closure variables are in the same
		   ;; order.
		   (map-vector abstract-tangent-v (closure-values u-forward))
		   xs1
		   (list->vector (map lambda-expression-variable es))
		   (list->vector (map lambda-expression-body es))
		   (recursive-closure-index u-forward)
		   ;; needs work: tangent of bundle gives the index-expression
		   ;;             and index-environment of the primal
		   (recursive-closure-index-expression u-forward)
		   (recursive-closure-index-environment u-forward)))))
	    (compile-time-warning
	     "Might attempt to take tangent of a non-forward value"
	     u-forward)))
       ((bundle? u-forward)
	(unless (or (every scalar-proto-abstract-value?
			   (bundle-primal u-forward))
		    (not (some scalar-proto-abstract-value?
			       (bundle-primal u-forward))))
	 (unimplemented))
	(if (every scalar-proto-abstract-value? (bundle-tangent u-forward))
	    (bundle-tangent u-forward)
	    (make-abstract-bundle
	     (abstract-tangent-v (bundle-primal u-forward))
	     (abstract-tangent-v (bundle-tangent u-forward)))))
       ((reverse-tagged-value? u-forward)
	(make-abstract-reverse-tagged-value
	 (abstract-tangent-v (reverse-tagged-value-primal u-forward))))
       ((and (not *scott-pairs?*) (tagged-pair? u-forward))
	(if (memq 'forward (tagged-pair-tags u-forward))
	    (make-abstract-tagged-pair
	     (remove-oneq 'forward (tagged-pair-tags u-forward))
	     (abstract-tangent-v (tagged-pair-car u-forward))
	     (abstract-tangent-v (tagged-pair-cdr u-forward))
	     ;; needs work: tangent of bundle gives the index-expression and
	     ;;             index-environment of the primal
	     (tagged-pair-index-expression u-forward)
	     (tagged-pair-index-environment u-forward))
	    (compile-time-warning
	     "Might attempt to take tangent of a non-forward value"
	     u-forward)))
       (else (internal-error))))

(define (abstract-bundle-internal v v-perturbation vs1-above vs2-above cs)
 ;; vs-above is the context for v-perturbation
 (cond
  ((up? v)
   (abstract-bundle-internal (list-ref vs1-above (up-index v))
			     v-perturbation
			     (rest* vs1-above (+ (up-index v) 1))
			     vs2-above
			     cs))
  ((up? v-perturbation)
   (abstract-bundle-internal v
			     (list-ref vs2-above (up-index v-perturbation))
			     vs1-above
			     (rest* vs2-above (+ (up-index v-perturbation) 1))
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
	       ((and (not *encoded-booleans?*)
		     (boolean? u)
		     (boolean? u-perturbation)
		     (eq? u u-perturbation))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (abstract-real? u) (abstract-real? u-perturbation))
		(make-abstract-bundle (list u) (list u-perturbation)))
	       ((and (primitive-procedure? u)
		     (primitive-procedure? u-perturbation)
		     (eq? u u-perturbation))
		(vlad-value->abstract-value (primitive-procedure-forward u)))
	       ((and (nonrecursive-closure? u)
		     (nonrecursive-closure? u-perturbation)
		     (= (vector-length (closure-values u))
			(vector-length (closure-values u-perturbation)))
		     ;; This assumes that the corresponding closure variables
		     ;; in u and u-perturbation are in the same order. See the
		     ;; note in vlad-equal?.
		     (let ((e (new-lambda-expression
			       (closure-variable u) (closure-body u)))
			   (e-perturbation (new-lambda-expression
					    (closure-variable u-perturbation)
					    (closure-body u-perturbation))))
		      (alpha-equivalent?
		       (lambda-expression-body e)
		       (lambda-expression-body e-perturbation)
		       (cons (lambda-expression-variable e) (free-variables e))
		       (cons (lambda-expression-variable e-perturbation)
			     (free-variables e-perturbation)))))
		(let ((e (forward-transform
			  (new-lambda-expression
			   (closure-variable u) (closure-body u)))))
		 (make-abstract-nonrecursive-closure
		  ;; This assumes that the corresponding closure variables in
		  ;; u, u-perturbation, and u-forward are in the same order.
		  ;; See the note in vlad-equal?.
		  (map-vector (lambda (v1 v1-perturbation)
			       (abstract-bundle-internal
				v1
				v1-perturbation
				(cons v vs1-above)
				(cons v-perturbation vs2-above)
				(cons (cons v v-perturbation) cs)))
			      (closure-values u)
			      (closure-values u-perturbation))
		  e
		  ;; needs work: tangent of bundle gives the index-expression
		  ;;             and index-environment of the primal
		  (nonrecursive-closure-index-environment u))))
	       ((and
		 (recursive-closure? u)
		 (recursive-closure? u-perturbation)
		 (= (vector-length (recursive-closure-bodies u))
		    (vector-length (recursive-closure-bodies u-perturbation)))
		 (= (recursive-closure-index u)
		    (recursive-closure-index u-perturbation))
		 (= (vector-length (closure-values u))
		    (vector-length (closure-values u-perturbation)))
		 ;; This assumes that the corresponding closure variables in u
		 ;; and u-perturbation are in the same order. See the note in
		 ;; vlad-equal?.
		 (every-vector
		  (lambda (x1 x2 e1 e2)
		   (let ((e (new-lambda-expression x1 e1))
			 (e-perturbation (new-lambda-expression x2 e2)))
		    (alpha-equivalent?
		     (lambda-expression-body e)
		     (lambda-expression-body e-perturbation)
		     (cons
		      (lambda-expression-variable e)
		      (append (vector->list
			       (recursive-closure-procedure-variables u))
			      (closure-variables u)))
		     (cons
		      (lambda-expression-variable e-perturbation)
		      (append
		       (vector->list
			(recursive-closure-procedure-variables u-perturbation))
		       (closure-variables u-perturbation))))))
		  (recursive-closure-argument-variables u)
		  (recursive-closure-argument-variables u-perturbation)
		  (recursive-closure-bodies u)
		  (recursive-closure-bodies u-perturbation)))
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
			    (map lambda-expression-body es))))
		 (make-abstract-recursive-closure
		  xs
		  ;; This assumes that the corresponding closure variables in
		  ;; u, u-perturbation, and u-forward are in the same order.
		  ;; See the note in vlad-equal?.
		  (map-vector (lambda (v1 v1-perturbation)
			       (abstract-bundle-internal
				v1
				v1-perturbation
				(cons v vs1-above)
				(cons v-perturbation vs2-above)
				(cons (cons v v-perturbation) cs)))
			      (closure-values u)
			      (closure-values u-perturbation))
		  xs1
		  (list->vector (map lambda-expression-variable es))
		  (list->vector (map lambda-expression-body es))
		  (recursive-closure-index u)
		  ;; needs work: tangent of bundle gives the index-expression
		  ;;             and index-environment of the primal
		  (recursive-closure-index-expression u)
		  (recursive-closure-index-environment u))))
	       ((and (bundle? u) (bundle? u-perturbation))
		(make-abstract-bundle
		 (abstract-bundle-internal
		  (bundle-primal u)
		  (bundle-primal u-perturbation)
		  (cons v vs1-above)
		  (cons v-perturbation vs2-above)
		  (cons (cons v v-perturbation) cs))
		 (abstract-bundle-internal
		  (bundle-tangent u)
		  (bundle-tangent u-perturbation)
		  (cons v vs1-above)
		  (cons v-perturbation vs2-above)
		  (cons (cons v v-perturbation) cs))))
	       ((and (reverse-tagged-value? u)
		     (reverse-tagged-value? u-perturbation))
		(make-abstract-reverse-tagged-value
		 (abstract-bundle-internal
		  (reverse-tagged-value-primal u)
		  (reverse-tagged-value-primal u-perturbation)
		  (cons v vs1-above)
		  (cons v-perturbation vs2-above)
		  (cons (cons v v-perturbation) cs))))
	       ((and (not *scott-pairs?*)
		     (tagged-pair? u)
		     (tagged-pair? u-perturbation)
		     (equal-tags?
		      (tagged-pair-tags u) (tagged-pair-tags u-perturbation)))
		(make-abstract-tagged-pair
		 (cons 'forward (tagged-pair-tags u))
		 (abstract-bundle-internal
		  (tagged-pair-car u)
		  (tagged-pair-car u-perturbation)
		  (cons v vs1-above)
		  (cons v-perturbation vs2-above)
		  (cons (cons v v-perturbation) cs))
		 (abstract-bundle-internal
		  (tagged-pair-cdr u)
		  (tagged-pair-cdr u-perturbation)
		  (cons v vs1-above)
		  (cons v-perturbation vs2-above)
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
 ;; needs work: This should be rewritten (like all of the others) to have a
 ;;             u version that takes u and u-perturbation and a v version that
 ;;             takes v and v-perturbation. And then should change
 ;;             abstract-binary-v->v to abstract-binary-u->v
 (abstract-bundle-internal v v-perturbation '() '() '()))

;;; Reverse Mode

;;; needs work: u and v versions
(define (abstract-plus u) (unimplemented "abstract-plus"))

(define (abstract-sensitize-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-sensitize-u v)
	     (empty-abstract-value))))

(define (abstract-sensitize-u u) (unimplemented "abstract-sensitize-u"))

(define (abstract-unsensitize-v v-sensitivity)
 (if (up? v-sensitivity)
     v-sensitivity
     (reduce abstract-value-union-without-unroll
	     (map abstract-unsensitize-u v-sensitivity)
	     (empty-abstract-value))))

(define (abstract-unsensitize-u u-sensitivity)
 (unimplemented "abstract-unsensitize-u"))

(define (abstract-*j-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-*j-u v)
	     (empty-abstract-value))))

(define (abstract-*j-u u) (unimplemented "abstract-*j-u"))

(define (abstract-*j-inverse-v v-reverse)
 (if (up? v-reverse)
     v-reverse
     (reduce abstract-value-union-without-unroll
	     (map abstract-*j-inverse-u v-reverse)
	     (empty-abstract-value))))

(define (abstract-*j-inverse-u u-reverse)
 (unimplemented "abstract-*j-inverse-u"))

;;; Abstract Basis Generators

(define (abstract-unary-u->v f s) (lambda (u bs) (f u)))

(define (abstract-unary f s) (lambda (u bs) (list (f u))))

(define (abstract-unary-real f s)
 (lambda (u bs)
  (cond ((real? u) (list (f u)))
	((abstract-real? u) '(real))
	(else (compile-time-warning
	       (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-unary-predicate f s)
 (lambda (u bs) (list (if (f u) vlad-true vlad-false))))

(define (abstract-unary-real-predicate f s)
 (lambda (u bs)
  (cond ((real? u) (list (if (f u) vlad-true vlad-false)))
	((abstract-real? u) (list vlad-true vlad-false))
	(else (compile-time-warning
	       (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-binary f s)
 (lambda (u bs)
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

(define (abstract-binary-v->v f s)
 (lambda (u bs)
  (if (vlad-pair? u '())
      ;; needs work: I'm not sure that this should call
      ;;             closed-proto-abstract-values. In any case need to redo
      ;;             the implementation of abstract-bundle. See the note there.
      (f (closed-proto-abstract-values (abstract-vlad-car-u u '()))
	 (closed-proto-abstract-values (abstract-vlad-cdr-u u '())))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u))))

(define (abstract-binary-real f s)
 (lambda (u bs)
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
 (lambda (u bs)
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

(define (abstract-ternary-u->v f s)
 (lambda (u123 bs)
  (if (vlad-pair? u123 '())
      (let ((v23
	     (closed-proto-abstract-values (abstract-vlad-cdr-u u123 '()))))
       (reduce
	abstract-value-union
	(map
	 (lambda (u1)
	  (reduce
	   abstract-value-union
	   (map
	    (lambda (u23)
	     (if (vlad-pair? u23 '())
		 (let ((v3 (closed-proto-abstract-values
			    (abstract-vlad-cdr-u u23 '()))))
		  (reduce
		   abstract-value-union
		   (map (lambda (u2)
			 (reduce abstract-value-union
				 (map (lambda (u3) (f u1 u2 u3 bs)) v3)
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

(define (abstract-ternary-prime-u->v f s)
 (lambda (u123 bs)
  (if (vlad-pair? u123 '())
      (let ((v23
	     (closed-proto-abstract-values (abstract-vlad-cdr-u u123 '()))))
       (reduce
	abstract-analysis-union
	(map
	 (lambda (u1)
	  (reduce
	   abstract-analysis-union
	   (map
	    (lambda (u23)
	     (if (vlad-pair? u23 '())
		 (let ((v3 (closed-proto-abstract-values
			    (abstract-vlad-cdr-u u23 '()))))
		  (reduce
		   abstract-analysis-union
		   (map (lambda (u2)
			 (reduce abstract-analysis-union
				 (map (lambda (u3) (f u1 u2 u3 bs)) v3)
				 (empty-abstract-analysis)))
			(closed-proto-abstract-values
			 (abstract-vlad-car-u u23 '())))
		   (empty-abstract-analysis)))
		 (compile-time-warning
		  (format #f "Argument to ~a might be invalid" s) u123)))
	    v23)
	   (empty-abstract-analysis)))
	 (closed-proto-abstract-values (abstract-vlad-car-u u123 '())))
	(empty-abstract-analysis)))
      (compile-time-warning
       (format #f "Argument to ~a might be invalid" s) u123))))

;;; Pretty printer for abstract

(define (externalize-proto-abstract-value u)
 (cond
  ((and (or (not *unabbreviate-transformed?*)
	    (and (not *scott-pairs?*) (tagged-pair? u)))
	(vlad-forward? u))
   `(forward ,(externalize-abstract-value (abstract-primal-u u))
	     ,(externalize-abstract-value (abstract-tangent-u u))))
  ((and (or (not *unabbreviate-transformed?*)
	    (and (not *scott-pairs?*) (tagged-pair? u)))
	(vlad-reverse? u))
   `(reverse ,(externalize-abstract-value (abstract-*j-inverse-u u))))
  ((null? u) '())
  ((vlad-true? u) #t)
  ((vlad-false? u) #f)
  ((abstract-real? u) u)
  ;; Whenever u is a pair and the cdr of u is a singleton abstract value which
  ;; is a closure, the pretty-printing of the closure is affected because the
  ;; closure is outputted as a list.
  ((vlad-pair? u '())
   (cons (externalize-abstract-value (abstract-vlad-car-u u '()))
	 (externalize-abstract-value (abstract-vlad-cdr-u u '()))))
  ((primitive-procedure? u) (primitive-procedure-name u))
  ((nonrecursive-closure? u)
   `(nonrecursive-closure
     ,(externalize-abstract-environment
       (closure-variables u) (closure-values u))
     ,(abstract->concrete
       (new-lambda-expression (closure-variable u) (closure-body u)))))
  ((recursive-closure? u)
   `(recursive-closure
     ,(externalize-abstract-environment
       (closure-variables u) (closure-values u))
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
   `(reverse ,(externalize-abstract-value (reverse-tagged-value-primal u))))
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

(define (boolean-value? v) (and (= (length v) 2) (every boolean? v)))

(define (abstract-real-value? v) (abstract-value=? v '(real)))

(define (real-pair) (list (vlad-cons '(real) '(real))))

(define (void? v)
 (when (up? v) (internal-error))
 (and (not (boolean-value? v))
      (not (abstract-real-value? v))
      (begin (unless (= (length v) 1) (internal-error))
	     (or (scalar-proto-abstract-value? (first v))
		 (every void? (aggregate-value-values (first v)))))))

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
 (reduce
  (lambda (xs1 xs2) (unionp variable=? xs1 xs2))
  (map (lambda (b)
	(all-variables-in-expression (expression-binding-expression b)))
       bs)
  '()))

(define (generate-variable-name x xs)
 (let ((i (positionp variable=? x xs)))
  (unless i (internal-error))
  (list "x" i)))

(define (generate-specifier v vs)
 (when (up? v) (internal-error))
 (when (void? v) (internal-error))
 (cond ((boolean-value? v) "int")
       ((abstract-real-value? v) "double")
       (else (let ((i (positionp abstract-value=? v vs)))
	      (unless i (internal-error))
	      (list "struct s" i)))))

(define (generate-slot-names u xs)
 (cond ((closure? u)
	(map (lambda (x) (generate-variable-name x xs)) (closure-variables u)))
       ((bundle? u) '("p" "t"))
       ((tagged-pair? u) '("a" "d"))
       (else (internal-error))))

(define (generate-struct-declarations xs vs)
 (map (lambda (v)
       (when (up? v) (internal-error))
       (cond ((or (void? v) (boolean-value? v) (abstract-real-value? v)) '())
	     (else (unless (= (length v) 1) (internal-error))
		   (list (generate-specifier v vs)
			 "{"
			 (map (lambda (s v)
			       (if (void? v)
				   '()
				   (list (generate-specifier v vs) " " s ";")))
			      (generate-slot-names (first v) xs)
			      (aggregate-value-values (first v)))
			 "};"
			 #\newline))))
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
 (when (up? v) (internal-error))
 (cons v
       (if (or (boolean-value? v)
	       (begin (unless (= (length v) 1) (internal-error))
		      (scalar-proto-abstract-value? (first v))))
	   '()
	   (begin (unless (= (length v) 1) (internal-error))
		  (reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
			  (map all-abstract-subvalues
			       (aggregate-value-values (first v)))
			  '())))))

(define (all-abstract-subvalues-for-bundle v v-perturbation)
 (when (or (up? v) (up? v-perturbation)) (internal-error))
 (cons (list (vlad-cons v v-perturbation))
       (if (or (and (boolean-value? v) (boolean-value? v-perturbation))
	       (and (abstract-real-value? v)
		    (or (abstract-real-value? v-perturbation)
			(void? v-perturbation)))
	       (and (void? v)
		    (or (abstract-real-value? v-perturbation)
			(void? v-perturbation))))
	   '()
	   (begin (unless (and (= (length v) 1) (= (length v-perturbation) 1))
		   (internal-error))
		  (reduce (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
			  (map all-abstract-subvalues-for-bundle
			       (aggregate-value-values (first v))
			       (aggregate-value-values (first v-perturbation)))
			  '())))))

(define (component? v1 v2)
 (or (abstract-value=? v1 v2)
     (and (= (length v2) 1)
	  (not (scalar-proto-abstract-value? (first v2)))
	  (memp component? v1 (aggregate-value-values (first v2))))))

(define (cached-topological-sort p l)
 (let ((cache (map (lambda (x1)
		    (cons x1 (map (lambda (x2) (cons x2 (p x1 x2))) l)))
		   l)))
  (let loop ((l l) (c '()))
   (if (null? l)
       (reverse c)
       (let ((x (find-if
		 (lambda (x1)
		  (every (lambda (x2)
			  (or (eq? x2 x1)
			      (not (cdr (assq x1 (cdr (assq x2 cache)))))))
			 l))
		 l)))
	(unless x (fuck-up))
	(loop (removeq x l) (cons x c)))))))

(define (all-nested-abstract-values bs)
 (cached-topological-sort
  component?
  (unionp abstract-value=?
	  (all-bundles bs)
	  (reduce
	   (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
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
		      (if (and (= (length v1) 1)
			       (primitive-procedure? (first v1))
			       (eq? (primitive-procedure-name (first v1)) s))
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
 (when (up? v1) (internal-error))
 (unless (= (length v1) 1) (internal-error))
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
   (if (or (void? v) (boolean-value? v) (abstract-real-value? v))
       '()
       (begin
	(unless (= (length v) 1) (internal-error))
	(list "static INLINE "
	      (generate-specifier v vs)
	      " "
	      (generate-builtin-name "m" v vs)
	      "("
	      (commas-between-void
	       (map (lambda (s v)
		     (if (void? v) #f (list (generate-specifier v vs) " " s)))
		    (generate-slot-names (first v) xs)
		    (aggregate-value-values (first v))))
	      ");"
	      #\newline))))
  vs))

(define (generate-constructor-definitions xs vs)
 (map
  (lambda (v)
   (if (or (void? v) (boolean-value? v) (abstract-real-value? v))
       '()
       (begin
	(unless (= (length v) 1) (internal-error))
	(list "static INLINE "
	      (generate-specifier v vs)
	      " "
	      (generate-builtin-name "m" v vs)
	      "("
	      (commas-between-void
	       (map (lambda (s v)
		     (if (void? v) #f (list (generate-specifier v vs) " " s)))
		    (generate-slot-names (first v) xs)
		    (aggregate-value-values (first v))))
	      "){"
	      (generate-specifier v vs)
	      " r;"
	      (map (lambda (s v) (if (void? v) '() (list "r." s "=" s ";")))
		   (generate-slot-names (first v) xs)
		   (aggregate-value-values (first v)))
	      "return r;}"
	      #\newline))))
  vs))

(define (generate-real-primitive-declarations s s1 s2 bs vs)
 (map (lambda (v)
       (unless (and (= (length v) 1) (abstract-real? (first v)))
	(internal-error))
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
       (unless (and (= (length v) 1) (abstract-real? (first v)))
	(internal-error))
       (list "static INLINE "
	     s1
	     " "
	     (generate-builtin-name s2 v vs)
	     "("
	     (if (void? v) "void" (list (generate-specifier v vs) " x"))
	     "){return "
	     (format #f s3 (if (void? v) (first v) "x"))
	     ";}"
	     #\newline))
      (all-primitives s bs)))

(define (generate-real*real-primitive-declarations s s1 s2 bs vs)
 (map (lambda (v)
       (unless (= (length v) 1) (internal-error))
       (let* ((v1 (abstract-vlad-car-u (first v) '()))
	      (v2 (abstract-vlad-cdr-u (first v) '())))
	(unless (and (= (length v1) 1)
		     (abstract-real? (first v1))
		     (= (length v2) 1)
		     (abstract-real? (first v2)))
	 (internal-error))
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
       (unless (= (length v) 1) (internal-error))
       (let* ((v1 (abstract-vlad-car-u (first v) '()))
	      (v2 (abstract-vlad-cdr-u (first v) '())))
	(unless (and (= (length v1) 1)
		     (abstract-real? (first v1))
		     (= (length v2) 1)
		     (abstract-real? (first v2)))
	 (internal-error))
	(list "static INLINE "
	      s1
	      " "
	      (generate-builtin-name s2 v vs)
	      "("
	      (if (void? v) "void" (list (generate-specifier v vs) " x"))
	      "){return "
	      (format #f
		      s3
		      (if (void? v1) (first v1) "x.a")
		      (if (void? v2) (first v2) "x.d"))
	      ";}"
	      #\newline)))
      (all-primitives s bs)))

(define (generate-if-declarations bs vs)
 (map
  (lambda (v)
   (unless (= (length v) 1) (internal-error))
   (let* ((v1 (abstract-vlad-car-u (first v) '()))
	  (v2 (abstract-vlad-cdr-u (first v) '())))
    (unless (= (length v2) 1) (internal-error))
    (let* ((v3 (abstract-vlad-car-u (first v2) '()))
	   (v4 (abstract-vlad-cdr-u (first v2) '())))
     (unless (= (length v3) 1) (internal-error))
     (unless (= (length v4) 1) (internal-error))
     (when (and (boolean-value? v1)
		(not
		 (abstract-value=?
		  (abstract-apply
		   v3 (abstract-tagged-null (abstract-closure-tags v3)) bs)
		  (abstract-apply
		   v4 (abstract-tagged-null (abstract-closure-tags v4)) bs))))
      (unimplemented "balancing"))
     (let ((v5 (if (or (boolean-value? v1)
		       (begin (unless (= (length v1) 1) (internal-error))
			      (first v1)))
		   (abstract-apply
		    v3 (abstract-tagged-null (abstract-closure-tags v3)) bs)
		   (abstract-apply
		    v4 (abstract-tagged-null (abstract-closure-tags v4)) bs))))
      (if (void? v5)
	  '()
	  (list "static INLINE "
		(generate-specifier v5 vs)
		" "
		(generate-builtin-name "if_procedure" v vs)
		"("
		(if (void? v) "void" (list (generate-specifier v vs) " x"))
		");"
		#\newline))))))
  (all-primitives 'if-procedure bs)))

(define (generate-if-definitions bs vs v1v2s)
 (map
  (lambda (v)
   (unless (= (length v) 1) (internal-error))
   (let* ((v1 (abstract-vlad-car-u (first v) '()))
	  (v2 (abstract-vlad-cdr-u (first v) '())))
    (unless (= (length v2) 1) (internal-error))
    (let* ((v3 (abstract-vlad-car-u (first v2) '()))
	   (v4 (abstract-vlad-cdr-u (first v2) '())))
     (unless (= (length v3) 1) (internal-error))
     (unless (= (length v4) 1) (internal-error))
     (when (and (boolean-value? v1)
		(not
		 (abstract-value=?
		  (abstract-apply
		   v3 (abstract-tagged-null (abstract-closure-tags v3)) bs)
		  (abstract-apply
		   v4 (abstract-tagged-null (abstract-closure-tags v4)) bs))))
      (unimplemented "balancing"))
     (let ((v5 (if (or (boolean-value? v1)
		       (begin (unless (= (length v1) 1) (internal-error))
			      (first v1)))
		   (abstract-apply
		    v3 (abstract-tagged-null (abstract-closure-tags v3)) bs)
		   (abstract-apply
		    v4 (abstract-tagged-null (abstract-closure-tags v4)) bs))))
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
	   (if (boolean-value? v1)
	       (list
		"x.a?"
		(generate-function-name
		 v3 (abstract-tagged-null (abstract-closure-tags v3)) v1v2s)
		"("
		(if (void? v3) '() "x.d.a")
		")"
		":"
		(generate-function-name
		 v4 (abstract-tagged-null (abstract-closure-tags v4)) v1v2s)
		"("
		(if (void? v4) '() "x.d.d")
		")")
	       (if (first v1)
		   (list (generate-function-name
			  v3
			  (abstract-tagged-null (abstract-closure-tags v3))
			  v1v2s)
			 "("
			 (if (void? v3) '() "x.d.a")
			 ")")
		   (list (generate-function-name
			  v4
			  (abstract-tagged-null (abstract-closure-tags v4))
			  v1v2s)
			 "("
			 (if (void? v4) '() "x.d.d")
			 ")")))
	   ";}"
	   #\newline))))))
  (all-primitives 'if-procedure bs)))

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
	      (map (lambda (b)
		    (let ((v1 (abstract-eval1 (application-callee e)
					      (restrict-environment
					       (environment-binding-values b)
					       e
					       application-callee)
					      bs)))
		     (cond
		      ((abstract-closure? v1)
		       (list
			(list v1
			      (abstract-eval1 (application-argument e)
					      (restrict-environment
					       (environment-binding-values b)
					       e
					       application-argument)
					      bs))))
		      ((and (= (length v1) 1)
			    (primitive-procedure? (first v1))
			    (eq? (primitive-procedure-name (first v1))
				 'if-procedure))
		       (let* ((v (abstract-eval1
				  (application-argument e)
				  (restrict-environment
				   (environment-binding-values b)
				   e
				   application-argument)
				  bs)))
			(unless (= (length v) 1) (internal-error))
			(let* ((v1 (abstract-vlad-car-u (first v) '()))
			       (v2 (abstract-vlad-cdr-u (first v) '())))
			 (unless (= (length v2) 1) (internal-error))
			 (let* ((v3 (abstract-vlad-car-u (first v2) '()))
				(v4 (abstract-vlad-cdr-u (first v2) '())))
			  (unless (= (length v3) 1) (internal-error))
			  (unless (= (length v4) 1) (internal-error))
			  (let ((v5 (if (or (boolean-value? v1)
					    (begin (unless (= (length v1) 1)
						    (internal-error))
						   (first v1)))
					(abstract-apply
					 v3
					 (abstract-tagged-null
					  (abstract-closure-tags v3))
					 bs)
					(abstract-apply
					 v4
					 (abstract-tagged-null
					  (abstract-closure-tags v4))
					 bs))))
			   (if (void? v5)
			       '()
			       (if (boolean-value? v1)
				   ;; We make the assumption that v3 and v4
				   ;; will not be abstract-value=?. If this
				   ;; assumption is false then there may be
				   ;; duplicates.
				   (list (list v3
					       (abstract-tagged-null
						(abstract-closure-tags v3)))
					 (list v4
					       (abstract-tagged-null
						(abstract-closure-tags v4))))
				   (if (first v1)
				       (list
					(list
					 v3
					 (abstract-tagged-null
					  (abstract-closure-tags v3))))
				       (list
					(list
					 v4
					 (abstract-tagged-null
					  (abstract-closure-tags v4))))))))))))
		      (else '()))))
		   (expression-binding-flow b))
	      '())
	     '())))
       bs)
  '()))

(define (generate-function-declarations bs xs vs v1v2s)
 (map
  (lambda (v1v2)
   (let* ((v1 (first v1v2))
	  (v2 (second v1v2))
	  (v3 (abstract-apply v1 v2 bs)))
    (if (void? v3)
	'()
	(list "static "
	      (if (nonrecursive-closure? (first v1)) "inline " '())
	      (generate-specifier v3 vs)
	      " "
	      (generate-function-name v1 v2 v1v2s)
	      "("
	      (commas-between-void
	       (list (if (void? v1) #f (list (generate-specifier v1 vs) " c"))
		     (if (void? v2)
			 #f
			 (list (generate-specifier v2 vs)
			       " "
			       (generate-variable-name
				(abstract-closure-variable v1) xs)))))
	      ");"
	      #\newline))))
  v1v2s))

(define (generate-reference x xs2 xs xs1)
 (cond ((memp variable=? x xs2) "c")
       ((memp variable=? x xs) (list "c." (generate-variable-name x xs1)))
       (else (generate-variable-name x xs1))))

(define (generate-expression e vs xs xs2 bs xs1 vs1 v1v2s)
 (let ((v (abstract-eval1 e vs bs)))
  (when (up? v) (internal-error))
  (cond
   ((void? v)
    (unless (= (length v) 1) (internal-error))
    (let ((u (first v)))
     (cond
      ((null? u) (internal-error))
      ((eq? u #t) "TRUE")
      ((eq? u #f) "FALSE")
      ;; This assumes that Scheme inexact numbers are printed as C doubles.
      ((real? u) (exact->inexact u))
      ((primitive-procedure? u) (internal-error))
      ((nonrecursive-closure? u) (internal-error))
      ((recursive-closure? u) (internal-error))
      ((bundle? u) (internal-error))
      ((tagged-pair? u) (internal-error))
      (else (internal-error)))))
   ((variable-access-expression? e)
    (generate-reference (variable-access-expression-variable e) xs2 xs xs1))
   ((lambda-expression? e)
    (unless (= (length v) 1) (internal-error))
    (list
     (generate-builtin-name "m" v vs1)
     "("
     (commas-between
      (map (lambda (x s v) (if (void? v) #f (generate-reference x xs2 xs xs1)))
	   (closure-variables (first v))
	   (generate-slot-names (first v) xs1)
	   (aggregate-value-values (first v))))
     ")"))
   ((application? e)
    (let ((v1 (abstract-eval1 (application-callee e)
			      (restrict-environment vs e application-callee)
			      bs))
	  (v2 (abstract-eval1 (application-argument e)
			      (restrict-environment vs e application-argument)
			      bs)))
     ;; needs work: To give an error on an improper call.
     (unless (= (length v1) 1) (internal-error))
     (if (primitive-procedure? (first v1))
	 (list
	  ((primitive-procedure-generator (first v1)) v2 vs1)
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
    (generate-expression
     (letrec-expression-body e)
     (list->vector
      (map (lambda (x)
	    (if (memp variable=? x (letrec-expression-procedure-variables e))
		(let ((vs (letrec-restrict-environment vs e)))
		 (make-abstract-recursive-closure
		  (letrec-expression-bodies-free-variables e)
		  vs
		  (list->vector (letrec-expression-procedure-variables e))
		  (list->vector (letrec-expression-argument-variables e))
		  (list->vector (letrec-expression-bodies e))
		  (positionp
		   variable=? x (letrec-expression-procedure-variables e))
		  e
		  vs))
		(vector-ref vs (positionp variable=? x (free-variables e)))))
	   (free-variables (letrec-expression-body e))))
     xs
     xs2
     bs
     xs1
     vs1
     v1v2s))
   ((cons-expression? e)
    (unless (= (length v) 1) (internal-error))
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
  (when (up? v) (internal-error))
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
     (unless (= (length v1) 1) (internal-error))
     (if (primitive-procedure? (first v1))
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
		 (make-abstract-recursive-closure
		  (letrec-expression-bodies-free-variables e)
		  vs
		  (list->vector (letrec-expression-procedure-variables e))
		  (list->vector (letrec-expression-argument-variables e))
		  (list->vector (letrec-expression-bodies e))
		  (positionp
		   variable=? x (letrec-expression-procedure-variables e))
		  e
		  vs))))
	(unless (= (length v) 1) (internal-error))
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
			(closure-variables (first v))
			(generate-slot-names (first v) xs1)
			(aggregate-value-values (first v))))
		  ");"))))
      (letrec-expression-procedure-variables e))
     (generate-letrec-bindings
      (letrec-expression-body e)
      (list->vector
       (map (lambda (x)
	     (if (memp variable=? x (letrec-expression-procedure-variables e))
		 (let ((vs (letrec-restrict-environment vs e)))
		  (make-abstract-recursive-closure
		   (letrec-expression-bodies-free-variables e)
		   vs
		   (list->vector (letrec-expression-procedure-variables e))
		   (list->vector (letrec-expression-argument-variables e))
		   (list->vector (letrec-expression-bodies e))
		   (positionp
		    variable=? x (letrec-expression-procedure-variables e))
		   e
		   vs))
		 (vector-ref vs (positionp variable=? x (free-variables e)))))
	    (free-variables (letrec-expression-body e))))
      xs
      xs2
      bs
      xs1
      vs1
      v1v2s)))
   ((cons-expression? e)
    (unless (= (length v) 1) (internal-error))
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

(define (generate-function-definitions bs xs vs v1v2s)
 (map
  (lambda (v1v2)
   (let* ((v1 (first v1v2))
	  (v2 (second v1v2))
	  (v3 (abstract-apply v1 v2 bs)))
    (unless (= (length v1) 1) (internal-error))
    (if (void? v3)
	'()
	(list "static "
	      (if (nonrecursive-closure? (first v1)) "inline " '())
	      (generate-specifier v3 vs)
	      " "
	      (generate-function-name v1 v2 v1v2s)
	      "("
	      (commas-between-void
	       (list (if (void? v1) #f (list (generate-specifier v1 vs) " c"))
		     (if (void? v2)
			 #f
			 (list (generate-specifier v2 vs)
			       " "
			       (generate-variable-name
				(abstract-closure-variable v1) xs)))))
	      "){"
	      (generate-letrec-bindings
	       (abstract-closure-body v1)
	       (abstract-apply-closure (lambda (e vs) vs) (first v1) v2)
	       (closure-variables (first v1))
	       (cond ((nonrecursive-closure? (first v1)) '())
		     ((recursive-closure? (first v1))
		      (vector->list
		       (recursive-closure-procedure-variables (first v1))))
		     (else (internal-error)))
	       bs
	       xs
	       vs
	       v1v2s)
	      "return "
	      (generate-expression
	       (abstract-closure-body v1)
	       (abstract-apply-closure (lambda (e vs) vs) (first v1) v2)
	       (closure-variables (first v1))
	       (cond ((nonrecursive-closure? (first v1)) '())
		     ((recursive-closure? (first v1))
		      (vector->list
		       (recursive-closure-procedure-variables (first v1))))
		     (else (internal-error)))
	       bs
	       xs
	       vs
	       v1v2s)
	      ";}"
	      #\newline))))
  v1v2s))

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
		     (if (and (= (length v1) 1)
			      (primitive-procedure? (first v1))
			      (eq? (primitive-procedure-name (first v1)) s))
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
   (component? (widen-abstract-value
		(abstract-bundle (abstract-vlad-car-u (first v1) '())
				 (abstract-vlad-cdr-u (first v1) '()))
		bs)
	       (widen-abstract-value
		(abstract-bundle (abstract-vlad-car-u (first v2) '())
				 (abstract-vlad-cdr-u (first v2) '()))
		bs)))
  (remove-if
   void?
   (reduce
    (lambda (vs1 vs2) (unionp abstract-value=? vs1 vs2))
    (map
     (lambda (v)
      (unless (= (length v) 1) (internal-error))
      (all-abstract-subvalues-for-bundle
       (abstract-vlad-car-u (first v) '())
       (abstract-vlad-cdr-u (first v) '())))
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
			  (if (and (= (length v1) 1)
				   (primitive-procedure? (first v1))
				   (eq? (primitive-procedure-name (first v1))
					'bundle))
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
       (let ((v1 (widen-abstract-value (abstract-zero-v v) bs)))
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
       (if (or (void? v) (boolean-value? v) (abstract-real-value? v))
	   '()
	   (begin (unless (= (length v) 1) (internal-error))
		  (let ((v1 (widen-abstract-value (f v) bs)))
		   (if (void? v1)
		       '()
		       (list "static INLINE "
			     (generate-specifier v1 vs)
			     " "
			     (generate-builtin-name s1 v vs)
			     "("
			     (generate-specifier v vs)
			     " x);"
			     #\newline))))))
      (all-ad s bs)))

(define (generate-bundle-declarations bs vs)
 (map (lambda (v)
       (unless (= (length v) 1) (internal-error))
       (let ((v1 (widen-abstract-value
		  (abstract-bundle (abstract-vlad-car-u (first v) '())
				   (abstract-vlad-cdr-u (first v) '()))
		  bs)))
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
       (let ((v1 (widen-abstract-value (abstract-zero-v v) bs)))
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
	     (cond
	      ((boolean-value? v1) "x")
	      ((abstract-real-value? v1) "0.0")
	      (else (unless (= (length v) 1) (internal-error))
		    (list (generate-builtin-name "m" v1 vs)
			  "("
			  (commas-between
			   (map (lambda (s v)
				 (if (void? (widen-abstract-value
					     (abstract-zero-v v) bs))
				     #f
				     (list (generate-builtin-name "zero" v vs)
					   "("
					   (if (void? v) '() (list "x." s))
					   ")")))
				(generate-slot-names (first v) xs)
				(aggregate-value-values (first v))))
			  ")")))
	     ";}"
	     #\newline))))
      (all-ad 'zero bs)))

(define (generate-primal-definitions bs xs vs)
 (map
  (lambda (v)
   (if (or (void? v) (boolean-value? v) (abstract-real-value? v))
       '()
       (begin
	(unless (= (length v) 1) (internal-error))
	(let ((v1 (widen-abstract-value (abstract-primal-v v) bs)))
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
	      (if (or (boolean-value? v1) (abstract-real-value? v1))
		  "x.p"
		  (list (generate-builtin-name "m" v1 vs)
			"("
			(commas-between
			 (map (lambda (s v)
			       (if (void? (widen-abstract-value
					   (abstract-primal-v v) bs))
				   #f
				   (list (generate-builtin-name "primal" v vs)
					 "(x."
					 s
					 ")")))
			      (generate-slot-names (first v) xs)
			      (aggregate-value-values (first v))))
			")"))
	      ";}"
	      #\newline))))))
  (all-ad 'primal bs)))

(define (generate-tangent-definitions bs xs vs)
 (map
  (lambda (v)
   (if (or (void? v) (boolean-value? v) (abstract-real-value? v))
       '()
       (begin
	(unless (= (length v) 1) (internal-error))
	(let ((v1 (widen-abstract-value (abstract-tangent-v v) bs)))
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
	      (if (or (boolean-value? v1) (abstract-real-value? v1))
		  "x.t"
		  (list (generate-builtin-name "m" v1 vs)
			"("
			(commas-between
			 (map (lambda (s v)
			       (if (void? (widen-abstract-value
					   (abstract-tangent-v v) bs))
				   #f
				   (list (generate-builtin-name "tangent" v vs)
					 "(x."
					 s
					 ")")))
			      (generate-slot-names (first v) xs)
			      (aggregate-value-values (first v))))
			")"))
	      ";}"
	      #\newline))))))
  (all-ad 'tangent bs)))

(define (generate-bundle-definitions bs xs vs)
 (map
  (lambda (v)
   (unless (= (length v) 1) (internal-error))
   (let* ((v1 (abstract-vlad-car-u (first v) '()))
	  (v2 (abstract-vlad-cdr-u (first v) '()))
	  (v3 (widen-abstract-value (abstract-bundle v1 v2) bs)))
    (unless (= (length v3) 1) (internal-error))
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
	  (if (or (boolean-value? v1)
		  (begin (unless (= (length v1) 1) (internal-error))
			 (scalar-proto-abstract-value? (first v1))))
	      (list (if (void? v1) #f "x.a") (if (void? v2) #f "x.d"))
	      (map (lambda (s4a s4b v4)
		    (if (void? v4)
			#f
			(let ((v5 (list (vlad-cons (widen-abstract-value
						    (abstract-primal-v v4)
						    bs)
						   (widen-abstract-value
						    (abstract-tangent-v v4)
						    bs)))))
			 (list (generate-builtin-name "bundle" v5 vs)
			       "("
			       (generate-builtin-name "m" v5 vs)
			       "("
			       (commas-between
				(map (lambda (s4 s6 v6)
				      (if (void? v6) #f (list "x." s6 "." s4)))
				     (list s4a s4b)
				     (generate-slot-names (first v5) xs)
				     (aggregate-value-values (first v5))))
			       "))"))))
		   (generate-slot-names (first v1) xs)
		   (generate-slot-names (first v2) xs)
		   (aggregate-value-values (first v3)))))
	 ");}"
	 #\newline))))
  (all-bundles bs)))

(define (generate e bs bs0)
 (let* ((xs (all-variables bs))
	(vs (all-nested-abstract-values bs))
	(v1v2s (all-functions bs)))
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
   (generate-if-declarations bs vs)
   "static INLINE double read_real(void);" #\newline
   (generate-real-primitive-declarations 'real "double" "real" bs vs)
   (generate-real-primitive-declarations 'write "double" "write" bs vs)
   (generate-zero-declarations bs vs)
   (generate-ad-declarations abstract-primal-v 'primal "primal" bs vs)
   (generate-ad-declarations abstract-tangent-v 'tangent "tangent" bs vs)
   (generate-bundle-declarations bs vs)
   (generate-function-declarations bs xs vs v1v2s)
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
   (generate-if-definitions bs vs v1v2s)
   "static INLINE double read_real(void){double x;scanf(\"%lf\",&x);return x;}"
   #\newline
   (generate-real-primitive-definitions 'real "double" "real" "~a" bs vs)
   (generate-real-primitive-definitions
    'write "double" "write" "write_real(~a)" bs vs)
   (generate-zero-definitions bs xs vs)
   (generate-primal-definitions bs xs vs)
   (generate-tangent-definitions bs xs vs)
   (generate-bundle-definitions bs xs vs)
   (generate-function-definitions bs xs vs v1v2s)
   (list
    "int main(void){"
    (let ((vs
	   (vector->list
	    (environment-binding-values
	     (first
	      (expression-binding-flow (lookup-expression-binding e bs)))))))
     (if (every void? vs)
	 '()
	 ;; needs work: to fill in slots
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
	  (map (lambda (v x)
		(let loop ((u (value-binding-value
			       (find-if
				(lambda (b)
				 (variable=? x (value-binding-variable b)))
				bs0)))
			   (c (list "c." (generate-variable-name x xs)))
			   (v v))
		 (if (void? v)
		     '()
		     (cond
		      ((boolean-value? v) (list c "=" (if u "1" "0") ";"))
		      ((abstract-real-value? v) (list c "=" u ";"))
		      ((and (= (length v) 1) (vlad-pair? (first v) '()))
		       (list (loop (vlad-car u '())
				   (list c ".a")
				   (abstract-vlad-car-u (first v) '()))
			     (loop (vlad-cdr u '())
				   (list c ".a")
				   (abstract-vlad-car-u (first v) '()))))
		      (else (internal-error))))))
	       vs
	       (free-variables e)))))
    (generate-letrec-bindings
     e
     (environment-binding-values
      (first
       (expression-binding-flow (lookup-expression-binding e bs))))
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
	   (first
	    (expression-binding-flow (lookup-expression-binding e bs))))
	  bs))
	'()
	(list
	 (generate-expression
	  e
	  (environment-binding-values
	   (first
	    (expression-binding-flow (lookup-expression-binding e bs))))
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
	 x procedure abstract-procedure generator forward reverse)
 (set! *value-bindings*
       (cons (make-value-binding
	      x
	      (make-primitive-procedure
	       x procedure abstract-procedure generator forward reverse 0))
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
	      (new-variable-access-expression 'x2)))
	    ;; needs work: to fill in index-expression
	    #f
	    '#())
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
	      (new-variable-access-expression 'x2)))
	    ;; needs work: to fill in index-expression
	    #f
	    '#())
	   #f))
 ;; In the following, all real constants are inexact so that they are
 ;; imprecise under -imprecise-inexacts.
 (define-primitive-procedure '+
  (binary-real + "+")
  (abstract-binary-real + "+")
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
  (abstract-binary-real - "-")
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
  (abstract-binary-real * "*")
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
  (abstract-binary-real divide "/")
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
  (abstract-unary-real sqrt "sqrt")
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
  (abstract-unary-real exp "exp")
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
  (abstract-unary-real log "log")
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
  (abstract-unary-real sin "sin")
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
  (abstract-unary-real cos "cos")
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
  (abstract-binary-real atan "atan")
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
  (abstract-binary-real-predicate = "=")
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
  (abstract-binary-real-predicate < "<")
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
  (abstract-binary-real-predicate > ">")
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
  (abstract-binary-real-predicate <= "<=")
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
  (abstract-binary-real-predicate >= ">=")
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
  (abstract-unary-real-predicate zero? "zero?")
  (lambda (v vs) (generate-builtin-name "iszero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (zero? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?")
  (abstract-unary-real-predicate positive? "positive?")
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
  (abstract-unary-real-predicate negative? "negative?")
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
  (abstract-unary-predicate null? "null?")
  (lambda (v vs) (unimplemented "null?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (null? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'boolean?
  (unary-predicate vlad-boolean? "boolean?")
  (abstract-unary-predicate vlad-boolean? "boolean?")
  (lambda (v vs) (unimplemented "boolean?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (boolean? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'real?
  (unary-predicate real? "real?")
  (abstract-unary-predicate real? "real?")
  (lambda (v vs) (unimplemented "real?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (real? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'pair?
  (unary-predicate (lambda (x) (vlad-pair? x '())) "pair?")
  (abstract-unary-predicate (lambda (x) (vlad-pair? x '())) "pair?")
  (lambda (v vs) (unimplemented "pair?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (pair? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?")
  (abstract-unary-predicate vlad-procedure? "procedure?")
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
  (abstract-unary-predicate vlad-forward? "forward?")
  (lambda (v vs) (unimplemented "forward?"))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) (j* (lambda (x) (bundle x (zero x)))))
     (j* (forward? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'reverse?
  (unary-predicate vlad-reverse? "reverse?")
  (abstract-unary-predicate vlad-reverse? "reverse?")
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
    (lambda (x1 x2 x3)
     (unless (and (nonrecursive-closure? x2) (nonrecursive-closure? x3))
      (run-time-error "You used if-procedure"))
     (if x1
	 (call x2 (tagged-null (closure-tags x2)))
	 (call x3 (tagged-null (closure-tags x3)))))
    "if-procedure")
   (abstract-ternary-u->v
    (lambda (u1 u2 u3 bs)
     (unless (and (nonrecursive-closure? u2) (nonrecursive-closure? u3))
      (run-time-error "You used if-procedure"))
     (if u1
	 (abstract-apply-closure (lambda (e vs) (abstract-eval1 e vs bs))
				 u2
				 (abstract-tagged-null (closure-tags u2)))
	 (abstract-apply-closure (lambda (e vs) (abstract-eval1 e vs bs))
				 u3
				 (abstract-tagged-null (closure-tags u3)))))
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
   (abstract-unary-u->v (lambda (u) (abstract-vlad-car-u u '())) "car")
   (lambda (v vs) "car")
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
   (abstract-unary-u->v (lambda (u) (abstract-vlad-cdr-u u '())) "cdr")
   (lambda (v vs) "cdr")
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
  (unary (lambda (x) (read-real)) "read-real")
  (abstract-unary-u->v (lambda (u) '(real)) "read-real")
  (lambda (v vs) "read_real")
  ;; needs work: is this right?
  '(lambda ((forward (ignore))) (bundle (read-real) (read-real)))
  ;; needs work: is this right?
  '(lambda ((reverse (ignore)))
    (cons (*j (read-real))
	  (lambda ((sensitivity y)) (cons '() (sensitivity y))))))
 (define-primitive-procedure 'real
  (unary-real identity "real")
  (abstract-unary-real (lambda (u) 'real) "real")
  (lambda (v vs) (generate-builtin-name "real" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (real x) (real (perturbation x)))))
  ;; needs work
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j x) (lambda ((sensitivity y)) (cons '() (sensitivity y)))))))
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write")
  (abstract-unary identity "write")
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
  (abstract-unary-u->v abstract-zero-u "zero")
  (lambda (v vs) (generate-builtin-name "zero" v vs))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (zero x) (zero (perturbation x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x)) (lambda ((sensitivity y)) (cons '() (zero x)))))))
 (define-primitive-procedure 'primal
  (unary primal "primal")
  (abstract-unary-u->v abstract-primal-u "primal")
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
  (abstract-unary-u->v abstract-tangent-u "tangent")
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
  (abstract-binary-v->v abstract-bundle "bundle")
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
  (abstract-binary abstract-plus "plus")
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
  (abstract-unary-u->v abstract-*j-u "*j")
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
  (abstract-unary-u->v abstract-*j-inverse-u "*j-inverse")
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
