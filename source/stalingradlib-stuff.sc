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

(define-structure cons-expression tags car cdr)

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

(define-structure tagged-pair tags car cdr)

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

(define-structure abstract-environment-binding abstract-values abstract-value)

(define-structure abstract-expression-binding expression abstract-flow)

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

(define *l1* #f)			;flow size limit

(define *l2* #f)			;concrete real abstract value limit

(define *l3* #f)			;matching closure abstract value limit

(define *l4* #f)			;closure nesting depth limit

(define *depth-measure* matching-nonrecursive-closure-depth)

(define *l5* #f)			;matching pair abstract value limit

(define *l6* #f)			;pair nesting depth limit

(define *l7* #f)			;matching bundle abstract value limit

(define *l8* #f)			;bundle nesting depth limit

(define *warn?* #t)

(define *expression-equality* 'structural)

(define *method-for-removing-redundant-proto-abstract-values* 'structural)

(define *quiet?* #f)

(define *parse-abstract?* #f)

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

(define (vlad-cons v1 v2)
 ;; (lambda (m) (let* ((x1 (m a)) (x2 (x1 d))) x2))
 (if *church-pairs?*
     (make-nonrecursive-closure
      '(a d)
      (vector v1 v2)
      'm
      (index
       'm
       '(a d)
       (new-let* '(x1 x2)
		 (list (new-application (new-variable-access-expression 'm)
					(new-variable-access-expression 'a))
		       (new-application (new-variable-access-expression 'x1)
					(new-variable-access-expression 'd)))
		 (new-variable-access-expression 'x2))))
     (make-tagged-pair '() v1 v2)))

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
	  (make-tagged-pair tags (first xs) (loop (rest xs)))))))

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

(define (new-cons-expression e1 e2) (make-cons-expression '() e1 e2))

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
	    (make-cons-expression
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

(define (letrec-expression-recursive-closure-variables e)
 (letrec-recursive-closure-variables
  (letrec-expression-procedure-variables e)
  (letrec-expression-argument-variables e)
  (letrec-expression-bodies e)))

(define (free-variables-old e)
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
       ((cons-expression? e) (free-variables-old e))
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
  ((cons-expression? e)
   (make-cons-expression (cons-expression-tags e)
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
		   (make-cons-expression
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
	(make-cons-expression (cons-expression-tags e)
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
	(make-cons-expression (cons-expression-tags e)
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
	(make-tagged-pair (tagged-pair-tags x)
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
	(make-cons-expression (cons 'forward (cons-expression-tags e))
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
   (make-cons-expression (rest (cons-expression-tags e))
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
	       ((and (not *church-pairs?*) (tagged-pair? x-forward))
		(unless (and
			 (not (null? (tagged-pair-tags x-forward)))
			 (eq? (first (tagged-pair-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take primal of a non-forward value" x-forward))
		(make-tagged-pair (rest (tagged-pair-tags x-forward))
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
		(make-tagged-pair (rest (tagged-pair-tags x-forward))
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
     (index x1 xs (lambda-expression-body e)))))
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
     (recursive-closure-index x))))
  ((bundle? x) (make-bundle x x-perturbation))
  ((reverse-tagged-value? x) (make-bundle x x-perturbation))
  ((and (not *church-pairs?*) (tagged-pair? x))
   (make-tagged-pair
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
     (make-cons-expression tags e1 e2)))

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
		      (make-cons-expression
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
	  (cons (make-cons-expression
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
	   ((and (not *church-pairs?*) (tagged-pair? v))
	    (make-tagged-pair (cons 'reverse (tagged-pair-tags v))
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
	   ((and (not *church-pairs?*) (tagged-pair? x-reverse))
	    (unless (and (not (null? (tagged-pair-tags x-reverse)))
			 (eq? (first (tagged-pair-tags x-reverse)) 'reverse))
	     (run-time-error
	      "Attempt to take primal of a non-reverse value" x-reverse))
	    (make-tagged-pair (rest (tagged-pair-tags x-reverse))
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
			       i)))
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
       ((cons-expression? e)
	;; This LET* is to specify the evaluation order.
	(let* ((car (evaluate (cons-expression-car e) v vs))
	       (cdr (evaluate (cons-expression-cdr e) v vs)))
	 (make-tagged-pair (cons-expression-tags e) car cdr)))
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

(define (replaceq x x-prime l) (list-replace l (positionq x l) x-prime))

(define (rest* l k) (if (zero? k) l (rest* (rest l) (- k 1))))

(define (every-eq? l1 l2)
 ;; optimization
 (or (eq? l1 l2) (and (= (length l1) (length l2)) (every eq? l1 l2))))

(define (minimal-elements <? s)
 ;; belongs in QobiScheme
 (remove-if (lambda (e) (some (lambda (e-prime) (<? e-prime e)) s)) s))

;;; VLAD stuff

(define (parse-abstract e-source)
 ;; here I am
 (set! *value-bindings* '())
 (initialize-basis!)
 (let* ((e-ps (map (lambda (b)
		    (let ((x (value-binding-variable b))
			  (p (value-binding-value b)))
		     `(cons* ,x
			     ,(primitive-procedure-forward p)
			     ,(primitive-procedure-reverse p))))
		   *value-bindings*))
	(e (cons 'list (cons `(lambda ((ignore)) ,e-source) e-ps)))
	(e (concrete->abstract-expression e))
	(bs (map (lambda (v) (make-value-binding (gensym) v))
		 (constants-in e)))
	(e (constant-convert bs e))
	(e (copy-propagate (anf-convert (alpha-convert e (free-variables e)))))
	(xs (free-variables e))
	(bs (append bs *value-bindings*))
	(result (evaluate
		 (index #f xs e)
		 'unspecified
		 (list->vector
		  (map (lambda (x)
			(value-binding-value
			 (find-if (lambda (b)
				   (variable=? x (value-binding-variable b)))
				  bs)))
		       xs))))
	(e-source-parsed (nonrecursive-closure-body (vlad-car result '())))
	(bs-for-e-source
	 (map (lambda (x v) (make-value-binding x v))
	      (nonrecursive-closure-variables (vlad-car result '()))
	      (vector->list
	       (nonrecursive-closure-values (vlad-car result '()))))))
  (let loop ((pfrs (vlad-cdr result '())))
   (if (null? pfrs)
       (list e-source-parsed bs-for-e-source)
       (let* ((pfr (vlad-car pfrs '()))
	      (p (vlad-car pfr '()))
	      (p-f (vlad-car (vlad-cdr pfr '()) '()))
	      (p-r (vlad-cdr (vlad-cdr pfr '()) '())))
	(set-primitive-procedure-forward! p p-f)
	(set-primitive-procedure-reverse! p p-r)
	(loop (vlad-cdr pfrs '())))))))

;;; Expression Equality

(define (expression? x)
 (or (constant-expression? x)
     (variable-access-expression? x)
     (lambda-expression? x)
     (application? x)
     (letrec-expression? x)
     (cons-expression? x)))

(define (expression-eqv? e1 e2)
 ;; optimization
 (or (eq? e1 e2)
     (and (constant-expression? e1)
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
	  ;; brownfis - to change, uncomment below
	  ;; (equal? (cons-expression-tags e1) (cons-expression-tags e2))
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

;;; Real Procedures

(define (abstract-real? u) (or (real? u) (eq? u 'real)))

;;; Closure Procedures

(define (nonrecursive-closure-match? u1 u2)
 (if (eq? *expression-equality* 'alpha)
     (unimplemented "Alpha equivalence")
     (and (variable=? (nonrecursive-closure-variable u1)
		      (nonrecursive-closure-variable u2))
	  (expression=? (nonrecursive-closure-body u1)
			(nonrecursive-closure-body u2)))))

(define (new-nonrecursive-closure vs e)
 (let ((xs (free-variables e))
       (x (lambda-expression-variable e))
       (e (lambda-expression-body e)))
  (list (make-nonrecursive-closure xs vs x e))))

(define (recursive-closure-match? u1 u2)
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

(define (new-recursive-closure xs vs xs-procedures xs-arguments es i)
 (list (make-recursive-closure xs vs xs-procedures xs-arguments es i)))

(define (recursive-closure-procedure-lambda-expressions v)
 (map-vector new-lambda-expression
	     (recursive-closure-argument-variables v)
	     (recursive-closure-bodies v)))

(define (closure-match? u1 u2)
 (unless (and (closure? u1) (closure? u2))
  (internal-error "u1 and u2 should both be closures"))
 (or (and (nonrecursive-closure? u1)
	  (nonrecursive-closure? u2)
	  (nonrecursive-closure-match? u1 u2))
     (and (recursive-closure? u1)
	  (recursive-closure? u2)
	  (recursive-closure-match? u1 u2))))

(define (closure-values u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-values u))
       ((recursive-closure? u) (recursive-closure-values u))
       (else (internal-error "Not a closure"))))

;;; Pair Procedures

(define (tagged-pair-match? u1 u2)
 (equal? (tagged-pair-tags u1) (tagged-pair-tags u2)))

;;; Bundle Procedures

(define (make-bundle-protected v1 v2)
 (when (or (up? v1) (up? v2)) (unimplemented "Bundles with backlinks"))
 (make-bundle v1 v2))

(define (bundle-match? u1 u2) #t)

;;; Reverse Tagged Value Procedures

(define (make-reverse-tagged-value-protected v)
 (when (up? v) (unimplemented "Reverse-tagged-values with backlinks"))
 (make-reverse-tagged-value v))

;;; Branching Value Procedures

(define (branching-value-match? u1 u2)
 (or (and (closure? u1) (closure? u2) (closure-match? u1 u2))
     (and (tagged-pair? u1) (tagged-pair? u2) (tagged-pair-match? u1 u2))
     (and (bundle? u1) (bundle? u2) (bundle-match? u1 u2))))

(define (branching-value-values u)
 (cond ((closure? u) (vector->list (closure-values u)))
       ((tagged-pair? u) (list (tagged-pair-car u) (tagged-pair-cdr u)))
       ((bundle? u) (list (bundle-primal u) (bundle-tangent u)))
       (else (internal-error))))

(define (make-branching-value-with-new-values u vs)
 ;; performance optimization
 (cond ((every-eq? vs (branching-value-values u)) u)
       ((nonrecursive-closure? u)
	(make-nonrecursive-closure (nonrecursive-closure-variables u)
				   (list->vector vs)
				   (nonrecursive-closure-variable u)
				   (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure (recursive-closure-variables u)
				(list->vector vs)
				(recursive-closure-procedure-variables u)
				(recursive-closure-argument-variables u)
				(recursive-closure-bodies u)
				(recursive-closure-index u)))
       ((tagged-pair? u)
	(make-tagged-pair (tagged-pair-tags u) (first vs) (second vs)))
       ((bundle? u) (make-bundle-protected (first vs) (second vs)))
       (else (internal-error))))

;;; Abstract Values

(define (empty-abstract-value) '())

(define (atomic-proto-abstract-value? u)
 (or (null? u) (boolean? u) (abstract-real? u) (primitive-procedure? u)))

(define (vlad-value->abstract-value v)
 (if (atomic-proto-abstract-value? v)
     (list v)
     (list (make-branching-value-with-new-values
	    v (map vlad-value->abstract-value (branching-value-values v))))))

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

(define (proto-abstract-value-subset?-internal u1 u2 cs vs1-above vs2-above)
 (or (and (null? u1) (null? u2))
     (and (boolean? u1) (boolean? u2) (eq? u1 u2))
     (and (eq? u1 'real) (eq? u2 'real))
     (and (real? u1) (eq? u2 'real))
     (and (real? u1) (real? u2) (= u1 u2))
     (and (primitive-procedure? u1) (primitive-procedure? u2) (eq? u1 u2))
     (and (branching-value-match? u1 u2)
	  (every
	   (lambda (v1 v2)
	    (abstract-value-subset?-internal v1 v2 cs vs1-above vs2-above))
	   (branching-value-values u1)
	   (branching-value-values u2)))))

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

(define (proto-abstract-value-nondisjoint?-internal
	 u1 u2 cs vs1-above vs2-above)
 (or (and (null? u1) (null? u2))
     (and (boolean? u1) (boolean? u2) (eq? u1 u2))
     (and (eq? u1 'real) (eq? u2 'real))
     (and (eq? u1 'real) (real? u2))
     (and (real? u1) (eq? u2 'real))
     (and (real? u1) (real? u2) (= u1 u2))
     (and (primitive-procedure? u1) (primitive-procedure? u2) (eq? u1 u2))
     (and (branching-value-match? u1 u2)
	  (every (lambda (v1 v2)
		  (abstract-value-nondisjoint?-internal
		   v1 v2 cs vs1-above vs2-above))
		 (branching-value-values u1)
		 (branching-value-values u2)))))

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
 ;; performance optimization
 ;; This is an imprecise version. A #f result is precise.
 (or (up? v1)
     (up? v2)
     (some (lambda (u1)
	    (some (lambda (u2)
		   (or (and (null? u1) (null? u2))
		       (and (boolean? u1) (boolean? u2) (eq? u1 u2))
		       (and (eq? u1 'real) (eq? u2 'real))
		       (and (eq? u1 'real) (real? u2))
		       (and (real? u1) (eq? u2 'real))
		       (and (real? u1) (real? u2) (= u1 u2))
		       (and (primitive-procedure? u1)
			    (primitive-procedure? u2)
			    (eq? u1 u2))
		       (and (branching-value-match? u1 u2)
			    (every abstract-value-nondisjoint?
				   (branching-value-values u1)
				   (branching-value-values u2)))))
		  v2))
	   v1)))

(define (closed-proto-abstract-values v)
 (let loop ((v v) (vs-above '()))
  (if (up? v)
      (if (= (up-index v) (- (length vs-above) 1))
	  (map (lambda (u)
		(if (atomic-proto-abstract-value? u)
		    u
		    (make-branching-value-with-new-values
		     u
		     (map (lambda (v)
			   (if (memq v vs-above)
			       (make-up (+ (positionq v vs-above) 1))
			       v))
			  (branching-value-values u)))))
	       (last vs-above))
	  v)
      (let ((v1 (map (lambda (u)
		      (if (atomic-proto-abstract-value? u)
			  u
			  (make-branching-value-with-new-values
			   u
			   (map (lambda (v1) (loop v1 (cons v vs-above)))
				(branching-value-values u)))))
		     v)))
       ;; performance optimization
       (if (every-eq? v v1) v v1)))))

(define (abstract-value-union v1 v2)
 ;; This cannot introduce imprecision.
 ;; optimization
 (cond ((null? v1) v2)
       ((null? v2) v1)
       ((eq? v1 v2) v1)
       ((and (up? v1) (up? v2) (= (up-index v1) (up-index v2))) v1)
       ((or (up? v1) (up? v2))
	(internal-error "Can't union a union type with a backlink"))
       (else (remove-redundant-proto-abstract-values
	      (append (closed-proto-abstract-values v1)
		      (closed-proto-abstract-values v2))))))

(define (abstract-value-union-without-unroll v1 v2)
 ;; This can introduce imprecision, as illustrated by the following example:
 ;; {(),pair(0,^0)} U {(),pair(1,^0)} would yield
 ;; {(),pair(0,^0),pair(1,^0)} which includes pair(0,pair(1,())) in its
 ;; extension even though it is not in the extension of either argument.
 ;; optimization
 (cond ((null? v1) v2)
       ((null? v2) v1)
       ((eq? v1 v2) v1)
       ((and (up? v1) (up? v2) (= (up-index v1) (up-index v2))) v1)
       ((or (up? v1) (up? v2))
	(internal-error "Can't union a union type with a backlink"))
       (else (remove-redundant-proto-abstract-values (append v1 v2)))))

;;; needs work: why do we sometimes call abstract-value-union-without-unroll
;;;             and sometimes call imprecise-abstract-value-union

(define (imprecise-abstract-value-union v1 v2)
 (abstract-value-union-without-unroll v1 v2))

;;; Abstract-Environment Subset, Equality, Disjointness, and Union

(define (restrict-environment vs xs xs-new)
 (list->vector
  (map (lambda (x-new)
	(vector-ref vs (position-if (lambda (x) (variable=? x x-new)) xs)))
       xs-new)))

(define (abstract-environment-subset? vs1 vs2)
 (every-vector abstract-value-subset? vs1 vs2))

(define (abstract-environment-proper-subset? vs1 vs2)
 ;; needs work: This is not a sound predicate. If it returns #t then it means
 ;;             that the second conjunct is imprecise. If it returns #f then
 ;;             it means that the first conjunct could be imprecise. We thus
 ;;             need to eliminate this predicate. It is used in two places.
 ;;             One is abstract-value-in-matching-abstract-environment. I
 ;;             believe that that could (and should) be replaced with
 ;;             abstract-environment-subset?. The other is
 ;;             introduce-imprecision-to-abstract-mapping-in-flow. I have not
 ;;             reviewed that code yet so I do not know what can or need be
 ;;             done there.
 (and (abstract-environment-subset? vs1 vs2)
      (not (abstract-environment-subset? vs2 vs1))))

(define (abstract-environment=? vs1 vs2)
 (and (abstract-environment-subset? vs1 vs2)
      (abstract-environment-subset? vs2 vs1)))

(define (abstract-environment-nondisjoint? vs1 vs2)
 (every-vector abstract-value-nondisjoint? vs1 vs2))

(define (abstract-environment-union vs1 vs2)
 (map-vector abstract-value-union vs1 vs2))

(define (imprecise-abstract-environment-union vs1 vs2)
 (map-vector imprecise-abstract-value-union vs1 vs2))

;;; Abstract-Flow Equality and Union

(define (empty-abstract-flow) '())

(define (create-abstract-flow vs v)
 (list (make-abstract-environment-binding vs v)))

(define (abstract-flow=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 (or
  ;; optimization
  (eq? bs1 bs2)
  ;; needs work: Can make O(n) instead of O(n^2).
  (set-equalp?
   (lambda (b1 b2)
    (and (abstract-environment=?
	  (abstract-environment-binding-abstract-values b1)
	  (abstract-environment-binding-abstract-values b2))
	 (abstract-value=? (abstract-environment-binding-abstract-value b1)
			   (abstract-environment-binding-abstract-value b2))))
   bs1
   bs2)))

(define (abstract-flow-union bs1 bs2)
 ;; This is one place where imprecision can be introduced.
 ;; needs work: I wrote the above comment a while ago and now don't remember
 ;;             how imprecision is introduced. I need to refresh my memory.
 (if (null? bs1)
     bs2
     (let ((b2 (find-if
		(lambda (b2)
		 (abstract-environment=?
		  (abstract-environment-binding-abstract-values (first bs1))
		  (abstract-environment-binding-abstract-values b2)))
		bs2)))
      (if b2
	  (abstract-flow-union
	   (rest bs1)
	   (cons (make-abstract-environment-binding
		  (abstract-environment-binding-abstract-values b2)
		  (abstract-value-union
		   (abstract-environment-binding-abstract-value (first bs1))
		   (abstract-environment-binding-abstract-value b2)))
		 (removeq b2 bs2)))
	  (cons (first bs1) (abstract-flow-union (rest bs1) bs2))))))

;;; Abstract-Analysis Equality and Union
;;; It's possible that the order of expressions in abstract analyses (for the
;;;   whole program) never changes.  There will be abstract analyses (lists of
;;;   abstract expression bindings) which result from the procedure
;;;   update-abstract-analysis-domains which don't have entries for each
;;;   expression (and may not be properly ordered).  However, the analysis for
;;;   the whole program's order doesn't change, I think.

(define (empty-abstract-analysis) '())

(define (create-abstract-analysis e vs v)
 (unless (= (vector-length vs) (length (free-variables e)))
  (internal-error
   "vs and (length (free-variables e)) should be of same length"))
 (list (make-abstract-expression-binding e (create-abstract-flow vs v))))

(define (abstract-analysis=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (set-equalp?
  (lambda (b1 b2)
   (and (expression=? (abstract-expression-binding-expression b1)
		      (abstract-expression-binding-expression b2))
	(abstract-flow=? (abstract-expression-binding-abstract-flow b1)
			 (abstract-expression-binding-abstract-flow b2))))
  bs1
  bs2))

(define (abstract-analysis-union bs1 bs2)
 (if (null? bs1)
     bs2
     (let ((b2 (lookup-expression-binding
		(abstract-expression-binding-expression (first bs1)) bs2)))
      (if b2
	  (abstract-analysis-union
	   (rest bs1)
	   (cons (make-abstract-expression-binding
		  (abstract-expression-binding-expression (first bs1))
		  (abstract-flow-union
		   (abstract-expression-binding-abstract-flow (first bs1))
		   (abstract-expression-binding-abstract-flow b2)))
		 (removeq b2 bs2)))
	  (cons (first bs1) (abstract-analysis-union (rest bs1) bs2))))))

;;; Widen

;;; General

(define (some-proto-abstract-value?-internal p u vs-above)
 (and (not (atomic-proto-abstract-value? u))
      (some (lambda (v) (some-abstract-value?-internal p v vs-above))
	    (branching-value-values u))))

(define (some-abstract-value?-internal p v vs-above)
 (or (p v vs-above)
     (and (not (up? v))
	  (some (lambda (u)
		 (some-proto-abstract-value?-internal p u (cons v vs-above)))
		v))))

(define (some-proto-abstract-value? p u)
 (some-proto-abstract-value?-internal p u '()))

(define (some-abstract-value? p v) (some-abstract-value?-internal p v '()))

(define (process-nodes-in-abstract-value-tree f v vs-above)
 (if (up? v)
     v
     (let ((v-new (f v vs-above)))
      (let loop ((us v-new) (us-new '()))
       (if (null? us)
	   ;; optimization
	   (let ((us-new (reverse us-new))) (if (every-eq? v us-new) v us-new))
	   (let ((u (first us)))
	    (if (atomic-proto-abstract-value? u)
		(loop (rest us) (cons u us-new))
		(loop (rest us)
		      (cons (make-branching-value-with-new-values
			     u (map (lambda (v1)
				     (process-nodes-in-abstract-value-tree
				      f v1 (cons v vs-above)))
				    (branching-value-values u)))
			    us-new)))))))))

(define (remove-duplicate-proto-abstract-values v)
 (process-nodes-in-abstract-value-tree
  (lambda (v vs-above) (remove-redundant-proto-abstract-values v)) v '()))

(define (free-up? v vs-above)
 (and (up? v) (>= (up-index v) (length vs-above))))

(define (free-up-index up up-context)
 (let ((l (- (up-index up) (length up-context))))
  (if (negative? l) #f l)))

(define (make-free-up index up-context)
 (make-up (+ index (length up-context))))

(define (proto-process-free-ups-internal f u vs-above)
 (if (atomic-proto-abstract-value? u)
     u
     (make-branching-value-with-new-values
      u
      (map (lambda (v) (process-free-ups-internal f v vs-above))
	   (branching-value-values u)))))

(define (process-free-ups-internal f v vs-above)
 (cond ((free-up? v vs-above) (f v vs-above))
       ((up? v) v)
       (else (map (lambda (u)
		   (proto-process-free-ups-internal f u (cons v vs-above)))
		  v))))

(define (proto-process-free-ups f u) (proto-process-free-ups-internal f u '()))

(define (process-free-ups f v) (process-free-ups-internal f v '()))

(define (decrement-free-ups-by k v)
 (process-free-ups (lambda (up vs-above) (make-up (- (up-index up) k))) v))

(define (decrement-free-ups v) (decrement-free-ups-by 1 v))

(define (create-addition i vs) (append (make-list i '()) (list vs)))

(define (move-additions-up v-new additions)
 ;; v-new is current v after any additions
 ;; This assumes that all additions are to values above v-new.
 ;; i is the post move-up free-up-index of the value to which the current set
 ;;   of additions is to be added.
 (let loop ((vss additions) (i 0))
  (if (= (length vss) i)
      vss
      (let* ((vs (list-ref vss i))
	     (add-in-v-new?
	      (some
	       (lambda (v)
		(and (not (and (up? v) (= (up-index v) 0)))
		     (some-abstract-value?
		      (lambda (v vs-above)
		       (and (free-up? v vs-above)
			    (= (free-up-index v vs-above) 0)))
		      v)))
	       vs))
	     (vs-new
	      (append (map (lambda (v)
			    (if (and (up? v) (= (up-index v) 0))
				v-new
				(process-free-ups
				 (lambda (v vs-above)
				  (if (= (free-up-index v vs-above) 0)
				      (make-free-up i vs-above)
				      (make-up (- (up-index v) 1))))
				 v)))
			   vs)
		      (if add-in-v-new? (list v-new) '()))))
       (loop (list-replace vss i vs-new) (+ i 1))))))

(define (move-values-up-tree v additions)
 ;; returns (LIST value additions)
 (when (null? additions)
  (internal-error "Shouldn't we NOT do this if (null? additions)?"))
 (let* ((vs-to-add (first additions))
	(paranoid
	 (when (some up? vs-to-add)
	  (internal-error "No additions should be UPs...should they?")))
	(v-new (remove-redundant-proto-abstract-values
		(reduce append
			(cons v (map decrement-free-ups vs-to-add))
			'())))
	(additions-new (move-additions-up v-new (rest additions))))
  (list v-new additions-new)))

;;; Matching Values

(define (pick-nonrecursive-closures-to-coalesce us) (sublist us 0 2))

(define (pick-recursive-closures-to-coalesce us) (sublist us 0 2))

(define (pick-closures-to-coalesce us)
 (cond
  ((every nonrecursive-closure? us)
   (pick-nonrecursive-closures-to-coalesce us))
  ((every recursive-closure? us)
   (pick-recursive-closures-to-coalesce us))
  (else (internal-error "us must be a list of {non,}recursive-closures"))))

(define (pick-pairs-to-coalesce us) (sublist us 0 2))

(define (pick-bundles-to-coalesce us) (sublist us 0 2))

(define (merge-additions vss1 vss2)
 ;; An addition is a list of sets of values, each set represented by a list.
 ;; The first element in the list is the set of values to be added into the
 ;;   "current" value, the second is those to be added to the current value's
 ;;   parent, and so on and so forth.
 ;; Each value in the addition is treated as if it were a child value of the
 ;;   current value.  This means that free references (FREE-UP 0) refer to the
 ;;   current value, (FREE-UP 1) refer to the current value's parent, and so on
 ;;   and so forth.
 (let ((l1 (length vss1))
       (l2 (length vss2)))
  (cond ((< l1 l2) (merge-additions (append vss1 (make-list (- l2 l1) '()))
				    vss2))
	((< l2 l1) (merge-additions vss1
				    (append vss2 (make-list (- l1 l2) '()))))
	(else (map append vss1 vss2)))))

(define (union-for-widening v1 v2)
 ;; assumed: v1 and v2 share the same context.  In other words, all
 ;;          free-up-reference-levels which are the same refer to the same
 ;;          values.
 (cond
  ((and (up? v1) (up? v2))
   (cond ((> (up-index v1) (up-index v2))
	  (list v1 (create-addition (up-index v1) (list v2))))
	 ((< (up-index v1) (up-index v2))
	  (list v2 (create-addition (up-index v2) (list v1))))
	 (else				; (= (up-index v1) (up-index v2))
	  (list v1 '()))))
  ((up? v1) (list v1 (create-addition (up-index v1) (list v2))))
  ((up? v2) (list v2 (create-addition (up-index v2) (list v1))))
  (else (list (remove-redundant-proto-abstract-values (append v1 v2)) '()))))

(define (limit-matching-branching-values-at-one-level
	 v k target-branching-value? branching-value-match?
	 pick-us-to-coalesce)
 (let outer ((branching-uss (transitive-equivalence-classesp
			     branching-value-match?
			     (remove-if-not target-branching-value? v)))
	     (us (remove-if target-branching-value? v))
	     (additions '())
	     (changed? #f))
  (cond ((null? branching-uss)
	 (if changed? (list us additions) (list v additions))) ; additions='()
	((<= (length (first branching-uss)) k)
	 (outer (rest branching-uss)
		(append us (first branching-uss))
		additions
		changed?))
	(else
	 (let* ((u1-u2 (pick-us-to-coalesce (first branching-uss)))
		(u1 (first u1-u2))
		(u2 (second u1-u2)))
	  (let inner ((vs1 (branching-value-values u1))
		      (vs2 (branching-value-values u2))
		      (vs '())
		      (additions additions))
	   (if (null? vs1)
	       (let* ((u-new (make-branching-value-with-new-values
			      u1 (reverse vs)))
		      (branching-uss-new
		       (cons
			(cons u-new
			      (removeq u2 (removeq u1 (first branching-uss))))
			(rest branching-uss))))
		(outer branching-uss-new us additions #t))
	       (let ((v-additions
		      (union-for-widening (first vs1) (first vs2))))
		(inner (rest vs1)
		       (rest vs2)
		       (cons (first v-additions) vs)
		       (merge-additions (second v-additions)
					additions))))))))))

;;; We'll collect additions for pair of matching branching values at one level
;;;   and then start to apply closures.
;;; When there are no additions at the "top level", we'll collect all the
;;;   additions for each of the child abstract values and then start to apply
;;;   them.

(define (limit-matching-branching-values-over-tree-internal
	 limit-at-one-level v)
 ;; returns: (LIST value additions)
 (if (up? v)
     (list v '())
     (let* ((v-additions (limit-at-one-level v))
	    (v-new (first v-additions))
	    (additions (second v-additions))
	    ;; optimization
	    (changed? (not (eq? v-new v))))
      (cond
       ((and (null? additions) (up? v-new)) (list v-new '()))
       ((null? additions)
	;; recursively widen each abstract value below v-new
	(let outer ((us v-new) (us-new '()) (additions '()))
	 (if (null? us)
	     (let ((us-new (reverse us-new)))
	      (if (null? additions)
		  ;; optimization
		  (if (every-eq? us-new v) (list v '()) (list us-new '()))
		  (let* ((v-additions
			  (move-values-up-tree us-new additions))
			 (v-new (first v-additions))
			 (additions-new (second v-additions)))
		   (if (null? additions-new)
		       (limit-matching-branching-values-over-tree-internal
			limit-at-one-level v-new)
		       v-additions))))
	     (let ((u (first us)))
	      (if (atomic-proto-abstract-value? u)
		  (outer (rest us) (cons u us-new) additions)
		  (let inner ((vs (branching-value-values u))
			      (vs-new '())
			      (additions additions))
		   (if (null? vs)
		       (let ((u-new (make-branching-value-with-new-values
				     u (reverse vs-new))))
			(outer (rest us)
			       (cons u-new us-new)
			       additions))
		       (let*
			 ((v-additions
			   (limit-matching-branching-values-over-tree-internal
			    limit-at-one-level (first vs)))
			  (v-new (first v-additions))
			  (additions-new (second v-additions)))
			(inner
			 (rest vs)
			 (cons v-new vs-new)
			 (merge-additions additions additions-new))))))))))
       (else (let* ((v-additions (move-values-up-tree v-new additions))
		    (v-new (first v-additions))
		    (additions-new (second v-additions)))
	      (if (null? additions-new)
		  (limit-matching-branching-values-over-tree-internal
		   limit-at-one-level v-new)
		  v-additions)))))))

(define (limit-matching-reals v)
 ;; This assumes that there are no duplicate concrete reals within an abstract
 ;; value.
 (if (eq? *l2* #f)
     v
     (process-nodes-in-abstract-value-tree
      (lambda (v vs-above) (if (> (count-if abstract-real? v) *l2*)
			       (cons 'real (remove-if abstract-real? v))
			       v))
      v
      '())))

(define (limit-matching-closures v)
 (if (eq? *l3* #f)
     v
     (let* ((limit-matching-closures-at-one-level
	     (lambda (v)
	      (limit-matching-branching-values-at-one-level
	       v *l3* closure? closure-match?
	       pick-closures-to-coalesce)))
	    (result (limit-matching-branching-values-over-tree-internal
		     limit-matching-closures-at-one-level v)))
      (unless (null? (second result))
       (internal-error "Some addition wasn't applied"))
      (first result))))

(define (limit-matching-pairs v)
 (if (eq? *l5* #f)
     v
     (let* ((limit-matching-pairs-at-one-level
	     (lambda (v)
	      (limit-matching-branching-values-at-one-level
	       v *l5* tagged-pair? tagged-pair-match?
	       pick-pairs-to-coalesce)))
	    (result (limit-matching-branching-values-over-tree-internal
		     limit-matching-pairs-at-one-level v)))
      (unless (null? (second result))
       (internal-error "Some addition wasn't applied"))
      (first result))))

(define (limit-matching-bundles v)
 (if (eq? *l7* #f)
     v
     (let* ((limit-matching-bundles-at-one-level
	     (lambda (v)
	      (limit-matching-branching-values-at-one-level
	       v *l7* bundle? bundle-match?
	       pick-bundles-to-coalesce)))
	    (result (limit-matching-branching-values-over-tree-internal
		     limit-matching-bundles-at-one-level v)))
      (unless (null? (second result))
       (internal-error "Some addition wasn't applied"))
      (first result))))

;;; Depth

(define (abstract-value-depth path)
 (cond ((null? path) 0)
       ((and (list? (first path))
	     ;; () makes list? true, so guard against it
	     (not (null? (first path))))
	(+ 1 (abstract-value-depth (rest path))))
       (else (abstract-value-depth (rest path)))))

;;; needs work: This is the nonrecursive depth measure that's been used, but it
;;;             isn't quite ideal--ideally we would use
;;;             matching-closure-depth-careful.  One would have to look closely
;;;             at the depth-limiting code (limit-l4-depth and so on) to ensure
;;;             that using matching-closure-depth-careful wouldn't break
;;;             anything.
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

(define (matching-closure-depth-careful path)
 ;; it is assumed that path starts with an abstract value
 (cond ((null? path) 0)
       ((null? (rest path)) 0)
       (else (reduce
	      max
	      (map length (transitive-equivalence-classesp
			   closure-match? (remove-if-not closure? path)))
	      minus-infinity))))

(define (pair-depth path)
 (count-if (lambda (u-or-v) (tagged-pair? u-or-v)) path))

(define (bundle-depth path) (count-if (lambda (u-or-v) (bundle? u-or-v)) path))

(define (path-of-depth-greater-than-k k depth u-or-v)
 (let loop ((u-or-v u-or-v) (path '()))
  (let ((add-to-path (lambda (u-or-v) (append path (list u-or-v)))))
   (cond ((up? u-or-v) (if (> (depth path) k) path #f))
	 ;; if u-or-v is an abstract value...
	 ((and (list? u-or-v) (not (null? u-or-v)))
	  (let inner ((us u-or-v))
	   (if (null? us)
	       (if (> (depth (add-to-path u-or-v)) k) (add-to-path u-or-v) #f)
	       (let ((result (loop (first us) (add-to-path u-or-v))))
		(if (eq? #f result)
		    (inner (rest us))
		    result)))))
	 (else				; u-or-v is a proto-abstract value...
	  (let ((u u-or-v))
	   (define (do-branching-value vs)
	    (let inner ((vs vs))
	     (if (null? vs)
		 (if (> (depth (add-to-path u)) k)
		     (add-to-path u)
		     #f)
		 (let ((result (loop (first vs) (add-to-path u))))
		  (if (eq? #f result)
		      (inner (rest vs))
		      result)))))
	   (if (atomic-proto-abstract-value? u)
	       (if (> (depth (add-to-path u)) k) (add-to-path u) #f)
	       (let inner ((vs (branching-value-values u)))
		(if (null? vs)
		    (if (> (depth (add-to-path u)) k) (add-to-path u) #f)
		    (let ((result (loop (first vs) (add-to-path u))))
		     (if (eq? #f result) (inner (rest vs)) result)))))))))))

(define (get-values-to-merge k depth path)
 ;; not quite general: path needs to be of form [] | [v u] ++ path
 (let loop ((i 0) (last-depth -1) (va #f) (vb #f))
  (cond
   ((not (or (eq? va #f) (eq? vb #f))) (list va vb))
   ((> (* 2 i) (length path)) (internal-error))
   (else
    (let ((d (depth (sublist path 0 (* 2 i)))))
     (cond ((and (= d k) (> d last-depth))
	    (loop (+ i 1) d (list-ref path (* 2 (- i 1))) vb))
	   ((and (= d (+ k 1)) (= last-depth k))
	    (loop (+ i 1) d va (list-ref path (* 2 (- i 1)))))
	   (else (loop (+ i 1) d va vb))))))))

(define (reduce-depth path v-target v-add)
 ;; path = [] | [v u] ++ path
 (let ((result
	(let loop ((path path) (vs-above '()))
	 (when (null? path) (internal-error))
	 (let ((v (first path)))
	  (if (eq? v v-add)
	      (let ((index (positionq v-target vs-above)))
	       (list (make-up index) (create-addition index (list v))))
	      (let* ((v-and-additions
		      (loop (rest (rest path)) (cons v vs-above)))
		     (v-new (first v-and-additions))
		     (additions (second v-and-additions))
		     (u (second path))
		     (v-down (third path))
		     (u-new (make-branching-value-with-new-values
			     u (map (lambda (v) (if (eq? v v-down) v-new v))
				    (branching-value-values u)))))
	       (if (null? additions)
		   (list (replaceq u u-new v) '())
		   (move-values-up-tree (replaceq u u-new v) additions))))))))
  (unless (null? (second result))
   (internal-error "Addition(s) not processed in reduce-depth"))
  (first result)))

(define (limit-l4-depth v)
 (if (eq? *l4* #f)
     v
     (let loop ((v v) (v-new '()))
      (if (null? v)
	  (let ((v-new (reverse v-new)))
	   (if every-eq? v-new v) v v-new)
	  (let ((path (path-of-depth-greater-than-k
		       *l4* *depth-measure* (list (first v)))))
	   (if (eq? path #f)
	       (loop (rest v)
		     (if (memp equalq? (first v) v-new)
			 v-new
			 (cons (first v) v-new)))
	       (let* ((va-vb (get-values-to-merge *l4* *depth-measure* path))
		      (v-tmp
		       (reduce-depth path (first va-vb) (second va-vb))))
		(loop (append v-tmp (rest v)) v-new))))))))

(define (limit-l6-depth v)
 (if (eq? *l6* #f)
     v
     (let loop ((path (path-of-depth-greater-than-k *l6* pair-depth v)) (v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge *l6* pair-depth path))
		 (v-new (reduce-depth path (first va-vb) (second va-vb))))
	   (loop (path-of-depth-greater-than-k *l6* pair-depth v-new)
		 v-new))))))

(define (aesthetic-reduce-l6-depth v)
 (if (eq? *l6* #f)
     v
     (let outer ((limit (- *l6* 1)) (v v))
      (if (< limit 1)
	  v
	  (let ((v-new
		 (let inner ((path (path-of-depth-greater-than-k
				    limit pair-depth v))
			     (v v))
		  (if (eq? path #f)
		      v
		      (let* ((va-vb (get-values-to-merge
				     limit pair-depth path))
			     (v-new (reduce-depth
				     path (first va-vb) (second va-vb))))
		       (inner (path-of-depth-greater-than-k
			       limit pair-depth v-new)
			      v-new))))))
	   (if (abstract-value=? v-new v)
	       (outer (- limit 1) v-new)
	       v))))))

;;; Syntactic Constraints

(define (l1-met? bs) (or (not *l1*) (<= (length bs) *l1*)))

(define (l2-met? v)
 (or (not *l2*)
     (not (some-abstract-value?
	   (lambda (v vs) (if (up? v) #f (> (count-if abstract-real? v) *l2*)))
	   v))))

(define (l3-met? v)
 (or (not *l3*)
     (not (some-abstract-value?
	   (lambda (v vs)
	    (if (up? v)
		#f
		(some (lambda (us) (> (length us) *l3*))
		      (transitive-equivalence-classesp
		       closure-match? (remove-if-not closure? v)))))
	   v))))

(define (l4-met? v)
 (or (not *l4*)
     (eq? (path-of-depth-greater-than-k *l4* *depth-measure* v) #f)))

(define (l5-met? v)
 (or (not *l5*)
     (not (some-abstract-value?
	   (lambda (v vs)
	    (if (up? v)
		#f
		(some (lambda (us) (> (length us) *l5*))
		      (transitive-equivalence-classesp
		       tagged-pair-match? (remove-if-not tagged-pair? v)))))
	   v))))

(define (l6-met? v)
 (or (not *l6*)
     (eq? (path-of-depth-greater-than-k *l6* pair-depth v) #f)))

(define (l7-met? v)
 (or (not *l7*)
     (not (some-abstract-value?
	   (lambda (v vs)
	    (if (up? v)
		#f
		(some (lambda (us) (> (length us) *l7*))
		      (transitive-equivalence-classesp
		       bundle-match? (remove-if-not bundle? v)))))
	   v))))

(define (l8-met? v)
 (or (not *l8*)
     (eq? (path-of-depth-greater-than-k *l8* bundle-depth v) #f)))

(define (widen-abstract-value v)
 (define (syntactic-constraints-met? v)
  (and (l2-met? v)
       (l3-met? v)
       (l4-met? v)
       (l5-met? v)
       (l6-met? v)
       (l7-met? v)))
 (let loop ((v v) (v-old 'old))
  (when (eq? v v-old) (internal-error "widen-abstract-value infinite loop"))
  (if (syntactic-constraints-met? v)
      v
      (loop
       ;; For some reason, performance is enhanced (at least in some observed
       ;;   cases) by calling limit-matching-{closures,pairs,bundles} both
       ;;   before and after reducing the depth of the abstract value.
       (let* ((v1 (remove-duplicate-proto-abstract-values v))
	      (v2a (limit-matching-closures v1))
	      (v3a (limit-matching-pairs v2a))
	      (v3b (limit-matching-bundles v3a))
	      (v4a (limit-l4-depth v3b))
	      (v5a (limit-l6-depth v4a))
	      (v5b (aesthetic-reduce-l6-depth v5a))
	      (v6a (limit-matching-closures v5b))
	      (v7a (limit-matching-pairs v6a))
	      (v7b (limit-matching-bundles v7a))
	      (v8a (remove-duplicate-proto-abstract-values v7b))
	      (v9a (limit-matching-reals v8a))
	      (v10a (remove-duplicate-proto-abstract-values v9a)))
	v10a)
       v))))

(define (remove-redundant-abstract-mappings bs)
 ;; An abstract mapping xi->yi in f=[x1->y1, ..., xn->yn] is redundant if
 ;;  there exists xj->yj in f such that:
 ;;   1. (subset? xi xj) AND
 ;;   2. (subset? yj yi)
 (let loop ((i 0) (bs bs))
  (cond ((= i (length bs)) bs)
	((some-n
	  (lambda (j)
	   (and (not (= i j))
		(let ((bi (list-ref bs i))
		      (bj (list-ref bs j)))
		 (and (abstract-environment-subset?
		       (abstract-environment-binding-abstract-values bi)
		       (abstract-environment-binding-abstract-values bj))
		      (abstract-value-subset?
		       (abstract-environment-binding-abstract-value bj)
		       (abstract-environment-binding-abstract-value bi))))))
	  (length bs))
	 (loop i (list-remove bs i)))
	(else (loop (+ i 1) bs)))))

(define (make-abstract-mapping-safe-to-add b bs0)
 ;; In order to add an abstract environment binding b = x0->y0 to an abstract
 ;;  flow bs0 = [x1->y1, ..., xn->yn] without reducing the extension of the
 ;;  abstract flow, we instead add the wider binding b' = x0->y, which
 ;;  satisfies the following conditions:
 ;;    1. (subset? y0 y)
 ;;    2. (forall i:xi intersects x0) (subset? yi y)
 ;;  The result of adding b' to bs0 will be wider than bs0.
 (let ((x-bar (abstract-environment-binding-abstract-values b))
       (y-bar0 (abstract-environment-binding-abstract-value b)))
  (let loop ((y-bar y-bar0) (bs bs0))
   (cond
    ((null? bs)
     (if (eq? y-bar y-bar0)
	 b
	 (make-abstract-environment-binding x-bar y-bar)))
    ;; needs work: to check that imprecision is sound
    ((abstract-environment-nondisjoint?
      x-bar (abstract-environment-binding-abstract-values (first bs)))
     (let ((yi-bar (abstract-environment-binding-abstract-value (first bs)))
	   (i (positionq (first bs) bs0)))
      (if (abstract-value-subset? yi-bar y-bar)
	  (loop y-bar (rest bs))
	  (loop (imprecise-abstract-value-union y-bar yi-bar) (rest bs)))))
    (else (loop y-bar (rest bs)))))))

(define (introduce-imprecision-to-abstract-mapping-in-flow i bs bs-old)
 (if (memq (list-ref bs i) bs-old)
     bs
     (let* ((b (list-ref bs i))
	    (all-vs-old
	     (reduce
	      append
	      (map (lambda (b)
		    (cons (abstract-environment-binding-abstract-value b)
			  (vector->list
			   (abstract-environment-binding-abstract-values b))))
		   bs-old)
	      '()))
	    (widen-abstract-value
	     (lambda (v) (if (memq v all-vs-old) v (widen-abstract-value v))))
	    (vs (abstract-environment-binding-abstract-values b))
	    (vs-new (map-vector widen-abstract-value vs))
	    (v (abstract-environment-binding-abstract-value
		(if (abstract-environment-proper-subset? vs vs-new)
		    (make-abstract-mapping-safe-to-add
		     (make-abstract-environment-binding
		      vs-new (abstract-environment-binding-abstract-value b))
		     bs)
		    b)))
	    (v-new (widen-abstract-value v)))
      (list-replace bs
		    (positionq b bs)
		    (make-abstract-environment-binding vs-new v-new)))))

(define (introduce-imprecision-by-restricting-abstract-function-size k bs)
 ;;    a. *Somehow* pick 2 flow elements b1 and b2 to replace with a new one.
 ;;    b. These two can be replaced with an abstract environment binding which
 ;;       maps Dom(b1) u Dom(b2) to a range AT LEAST as wide as
 ;;       Range(b1) u Range(b2).
 ;;    c. If still over the # of flow elements, repeat.
 (if (<= (length bs) k)
     bs
     (introduce-imprecision-by-restricting-abstract-function-size
      k (let* ((b1 (first bs))
	       (b2 (second bs))
	       (bs-rest (rest (rest bs)))
	       (vs1 (abstract-environment-binding-abstract-values b1))
	       (v1 (abstract-environment-binding-abstract-value b1))
	       (vs2 (abstract-environment-binding-abstract-values b2))
	       (v2 (abstract-environment-binding-abstract-value b2)))
	 (cons (make-abstract-mapping-safe-to-add
		(make-abstract-environment-binding
		 (imprecise-abstract-environment-union vs1 vs2)
		 (imprecise-abstract-value-union v1 v2))
		bs-rest)
	       bs-rest)))))

(define (introduce-imprecision-to-abstract-flow bs bs-old)
 ;; bs is the abstract flow from the current iteration
 ;; bs-old is the abstract flow from the previous iteration
 ;; If bs and bs-old are identical, there is no need to introduce imprecision.
 ;; (introduce-imprecision-to-abstract-mapping-in-flow checks individual
 ;;  abstract environment bindings to see if they need the imprecision
 ;;  introduction carried out on them.)
 (if (eq? bs bs-old)
     bs
     (let* ((bs-new
	     (if (eq? #f *l1*)
		 bs
		 (introduce-imprecision-by-restricting-abstract-function-size
		  *l1* bs)))
	    (result
	     ;; The remove-redundant-abstract-mappings in the starting value
	     ;; for bs has, in the past, sometimes incited a slowdown.
	     (let loop ((i 0) (bs (remove-redundant-abstract-mappings bs-new)))
	      (if (= i (length bs))
		  bs
		  (loop (+ i 1)
			(introduce-imprecision-to-abstract-mapping-in-flow
			 i bs bs-old))))))
      (remove-redundant-abstract-mappings result))))

;;; Flow Analysis

(define (lookup-expression-binding e bs)
 (find-if (lambda (b)
	   (expression=? e (abstract-expression-binding-expression b)))
	  bs))

(define (expression-abstract-flow2 e bs)
 (let ((b (lookup-expression-binding e bs)))
  (if (eq? b #f) #f (abstract-expression-binding-abstract-flow b))))

(define (expression-abstract-flow3 e bs)
 (let ((b (lookup-expression-binding e bs)))
  (if (eq? b #f) '() (abstract-expression-binding-abstract-flow b))))

(define (mapping-with-vs-in-flow? vs bs)
 (some (lambda (b) (eq? (abstract-environment-binding-abstract-values b) vs))
       bs))

(define (abstract-analysis-rooted-at e vs)
 (let ((xs (free-variables e)))
  (cond ((variable-access-expression? e)
	 (create-abstract-analysis e vs (vector-ref vs 0)))
	((lambda-expression? e)
	 (create-abstract-analysis e vs (new-nonrecursive-closure vs e)))
	((application? e)
	 (let ((e1 (application-callee e))
	       (e2 (application-argument e)))
	  (abstract-analysis-union
	   (create-abstract-analysis e vs (empty-abstract-value))
	   (abstract-analysis-union
	    (abstract-analysis-rooted-at
	     e1 (restrict-environment vs xs (free-variables e1)))
	    (abstract-analysis-rooted-at
	     e2 (restrict-environment vs xs (free-variables e2)))))))
	((letrec-expression? e)
	 (abstract-analysis-union
	  (create-abstract-analysis e vs (empty-abstract-value))
	  (let ((vs-e
		 (list->vector
		  (map
		   (lambda (x)
		    (if (memp variable=?
			      x
			      (letrec-expression-procedure-variables e))
			(new-recursive-closure
			 (letrec-expression-recursive-closure-variables e)
			 (list->vector
			  (map
			   (lambda (x) (vector-ref vs (positionp
						       variable=? x xs)))
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
			(vector-ref vs (positionp variable=? x xs))))
		   (free-variables (letrec-expression-body e))))))
	   (abstract-analysis-rooted-at (letrec-expression-body e) vs-e))))
	((cons-expression? e)
	 (let ((e1 (cons-expression-car e))
	       (e2 (cons-expression-cdr e)))
	  (abstract-analysis-union
	   (create-abstract-analysis e vs (empty-abstract-value))
	   (abstract-analysis-union
	    (abstract-analysis-rooted-at
	     e1 (restrict-environment vs xs (free-variables e1)))
	    (abstract-analysis-rooted-at
	     e2 (restrict-environment vs xs (free-variables e2)))))))
	(else (internal-error "Not a valid expression")))))

(define (initial-abstract-analysis e bs)
 (let ((vs (list->vector
	    (map (lambda (x)
		  (vlad-value->abstract-value
		   (value-binding-value
		    (find-if
		     (lambda (b) (variable=? x (value-binding-variable b)))
		     bs))))
		 (free-variables e)))))
  (abstract-analysis-rooted-at e vs)))

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
 (if (some-vector (lambda (v) (eq? v (empty-abstract-value))) vs)
     (empty-abstract-value)
     (let ((bs (minimal-elements
		(lambda (b1 b2)
		 (abstract-environment-proper-subset?
		  (abstract-environment-binding-abstract-values b1)
		  (abstract-environment-binding-abstract-values b2)))
		(remove-if-not
		 (lambda (b)
		  (abstract-environment-subset?
		   vs (abstract-environment-binding-abstract-values b)))
		 (expression-abstract-flow3 e bs)))))
      (if (null? bs)
	  (begin (set! *lookup-misses* (+ *lookup-misses* 1))
		 (empty-abstract-value))
	  (abstract-environment-binding-abstract-value (first bs))))))

(define (abstract-apply-nonrecursive-closure-to-u p u1 u2)
 (let ((xs (nonrecursive-closure-variables u1)))
  (p (nonrecursive-closure-body u1)
     (list->vector
      (map (lambda (x)
	    (if (variable=? x (nonrecursive-closure-variable u1))
		(list u2)
		(vector-ref (nonrecursive-closure-values u1)
			    (positionp variable=? x xs))))
	   (free-variables (nonrecursive-closure-body u1)))))))

(define (abstract-apply-recursive-closure-to-u p u1 u2)
 (let ((e (vector-ref (recursive-closure-procedure-lambda-expressions u1)
		      (recursive-closure-index u1)))
       (xs-procedures
	(vector->list (recursive-closure-procedure-variables u1)))
       (x-argument (vector-ref (recursive-closure-argument-variables u1)
			       (recursive-closure-index u1)))
       (xs (recursive-closure-variables u1)))
  (p (lambda-expression-body e)
     (list->vector
      (map (lambda (x)
	    (cond
	     ((variable=? x (lambda-expression-variable e)) (list u2))
	     ((memp variable=? x xs-procedures)
	      (new-recursive-closure
	       (recursive-closure-variables u1)
	       (recursive-closure-values u1)
	       (recursive-closure-procedure-variables u1)
	       (recursive-closure-argument-variables u1)
	       (recursive-closure-bodies u1)
	       (positionp variable=? x xs-procedures)))
	     (else (vector-ref (recursive-closure-values u1)
			       (positionp variable=? x xs)))))
	   (free-variables (lambda-expression-body e)))))))

(define (abstract-apply-closure-to-u p u1 u2)
 (cond ((nonrecursive-closure? u1)
	(abstract-apply-nonrecursive-closure-to-u p u1 u2))
       ((recursive-closure? u1)
	(abstract-apply-recursive-closure-to-u p u1 u2))
       (else (internal-error))))

(define (abstract-apply-nonrecursive-closure-to-v p u1 v2)
 (let ((xs (nonrecursive-closure-variables u1)))
  (p (nonrecursive-closure-body u1)
     (list->vector
      (map (lambda (x)
	    (if (variable=? x (nonrecursive-closure-variable u1))
		v2
		(vector-ref (nonrecursive-closure-values u1)
			    (positionp variable=? x xs))))
	   (free-variables (nonrecursive-closure-body u1)))))))

(define (abstract-apply-recursive-closure-to-v p u1 v2)
 (let ((e (vector-ref (recursive-closure-procedure-lambda-expressions u1)
		      (recursive-closure-index u1)))
       (xs-procedures
	(vector->list (recursive-closure-procedure-variables u1)))
       (x-argument (vector-ref (recursive-closure-argument-variables u1)
			       (recursive-closure-index u1)))
       (xs (recursive-closure-variables u1)))
  (p (lambda-expression-body e)
     (list->vector
      (map (lambda (x)
	    (cond
	     ((variable=? x (lambda-expression-variable e)) v2)
	     ((memp variable=? x xs-procedures)
	      (new-recursive-closure
	       (recursive-closure-variables u1)
	       (recursive-closure-values u1)
	       (recursive-closure-procedure-variables u1)
	       (recursive-closure-argument-variables u1)
	       (recursive-closure-bodies u1)
	       (positionp variable=? x xs-procedures)))
	     (else (vector-ref (recursive-closure-values u1)
			       (positionp variable=? x xs)))))
	   (free-variables (lambda-expression-body e)))))))

(define (abstract-apply-closure-to-v p u1 v2)
 (cond ((nonrecursive-closure? u1)
	(abstract-apply-nonrecursive-closure-to-v p u1 v2))
       ((recursive-closure? u1)
	(abstract-apply-recursive-closure-to-v p u1 v2))
       (else (internal-error))))

(define (abstract-apply v1 v2 bs)
 ;; bs is an analysis.
 (let ((lookup-in-analysis
	(lambda (e vs)
	 (abstract-value-in-matching-abstract-environment e vs bs))))
  (reduce
   abstract-value-union
   (map (lambda (u1)
	 (cond ((eq? v2 (empty-abstract-value)) (empty-abstract-value))
	       ((primitive-procedure? u1)
		(reduce abstract-value-union
			(map (lambda (u2)
			      ((primitive-procedure-abstract-procedure u1) u2))
			     (closed-proto-abstract-values v2))
			(empty-abstract-value)))
	       ((closure? u1)
		(abstract-apply-closure-to-v lookup-in-analysis u1 v2))
	       (else (compile-time-warning
		      "Application callee not a procedure: " u1))))
	(closed-proto-abstract-values v1))
   (empty-abstract-value))))

(define (abstract-apply-prime v1 v2)
 (reduce
  abstract-analysis-union
  (map (lambda (u1)
	(cond ((eq? v2 (empty-abstract-value)) (empty-abstract-analysis))
	      ((primitive-procedure? u1) (empty-abstract-analysis))
	      ((closure? u1)
	       (abstract-apply-closure-to-v abstract-analysis-rooted-at u1 v2))
	      (else (empty-abstract-analysis))))
       (closed-proto-abstract-values v1))
  (empty-abstract-analysis)))

;;; add-new-mappings-to-abstract-flow acts as a sort of abstract flow union--
;;; one that ensures that elements of bs-new are added in a monotonic manner.
(define (add-new-mappings-to-abstract-flow bs bs-new)
 (if (null? bs-new)
     bs
     (if (some (lambda (b1)
		(abstract-environment-subset?
		 (abstract-environment-binding-abstract-values (first bs-new))
		 (abstract-environment-binding-abstract-values b1)))
	       bs)
	 ;; Given b1,
	 ;; let b2       = (first bs-new)
	 ;;     x1 -> y1 = b1
	 ;;     x2 -> y2 = b2
	 ;; Now if (subset? x2 x1), in order to add b1 monotonicly, we would
	 ;; instead add b1' = x1 -> y1', such that (subset? y2 y1').
	 ;; However, this would make b1' redundant, so we skip the whole
	 ;; exercise and don't add b1.
	 (add-new-mappings-to-abstract-flow bs (rest bs-new))
	 (add-new-mappings-to-abstract-flow
	  (cons (make-abstract-mapping-safe-to-add (first bs-new) bs) bs)
	  (rest bs-new)))))

(define (update-abstract-analysis-ranges bs bs-old)
 ;; bs is the abstract analysis from some iteration i of flow-analysis
 ;; bs-old is the abstract analysis from iteration i-1 of flow-analysis
 (let* ((bs-unchanged?
	 (map (lambda (b)
	       (let* ((e (abstract-expression-binding-expression b))
		      (bs-e (abstract-expression-binding-abstract-flow b))
		      (bs-old-e (expression-abstract-flow3 e bs-old)))
		(cons e (or (eq? bs-e bs-old-e)
			    ;; to catch cases where flow was simply recreated
			    (set-equalq? bs-e bs-old-e)))))
	      bs))
	(bs-unchanged-for-e?
	 (lambda (e) (let ((result (assp expression=? e bs-unchanged?)))
		      (if result (cdr result) #f)))))
  (map
   (lambda (b)
    (let* ((e (abstract-expression-binding-expression b))
	   (xs (free-variables e)))
     (if (or (variable-access-expression? e) (lambda-expression? e))
	 b
	 (make-abstract-expression-binding
	  e
	  (let*
	    ((bs-e (abstract-expression-binding-abstract-flow b))
	     (result
	      (map
	       (lambda (b2)
		(let*
		  ((vs (abstract-environment-binding-abstract-values b2))
		   (v (abstract-environment-binding-abstract-value b2))
		   (v-new
		    (cond
		     ((variable-access-expression? e) (internal-error))
		     ((lambda-expression? e) (internal-error))
		     ((application? e)
		      ;; e: (e1 e2)
		      (let* ((e1 (application-callee e))
			     (e2 (application-argument e))
			     (xs1 (free-variables e1))
			     (xs2 (free-variables e2)))
		       ;; e can be safely left unupdated if:
		       ;;   1. exists vs->v' in (bs-old e)
		       ;;      (basically, vs same as last iter)
		       ;;      - NOTE: we don't say exists vs->v' in (bs e)
		       ;;      - This means that the same environment vs got
		       ;;        evaluated last iteration as we're trying to
		       ;;        evaluate now.
		       ;;   2. (bs e1) = (bs-old e1)
		       ;;   3. (bs e2) = (bs-old e2)
		       ;;   AND
		       ;;   4. forall u in (bs e1 vs)
		       ;;        u = <sigma,e'> => (bs e') = (bs-old e') AND
		       ;;        u = <sigma,xs,es',i> =>
		       ;;                       (bs es'[i]) = (bs-old es'[i])
		       (if (and
			    (mapping-with-vs-in-flow?
			     vs (expression-abstract-flow3 e bs-old))
			    (bs-unchanged-for-e? e1)
			    (bs-unchanged-for-e? e2)
			    (every
			     (lambda (u)
			      (cond
			       ((nonrecursive-closure? u)
				(bs-unchanged-for-e?
				 (nonrecursive-closure-body u)))
			       ((recursive-closure? u)
				(bs-unchanged-for-e?
				 (vector-ref (recursive-closure-bodies u)
					     (recursive-closure-index u))))
			       (else #t)))
			     (abstract-value-in-matching-abstract-environment
			      e1 (restrict-environment vs xs xs1) bs)))
			   v
			   (abstract-apply
			    (abstract-value-in-matching-abstract-environment
			     e1 (restrict-environment vs xs xs1) bs)
			    (abstract-value-in-matching-abstract-environment
			     e2 (restrict-environment vs xs xs2) bs)
			    bs))))
		     ((letrec-expression? e)
		      ;; e: (letrec x1 = e1, ..., xn = en in e-body)
		      (let ((es (letrec-expression-bodies e))
			    (e-body (letrec-expression-body e))
			    (xs1 (letrec-expression-procedure-variables e))
			    (xs2 (letrec-expression-argument-variables e))
			    (xs-closure
			     (letrec-expression-recursive-closure-variables
			      e)))
		       ;; e can be safely left un-updated if:
		       ;;   1. exists vs->v' in (bs-old e)
		       ;;      (basically, vs same as last iter)
		       ;;      - NOTE: we don't say exists vs->v' in (bs e)
		       ;;      - This means that the same environment vs got
		       ;;        evaluated last iteration as we're trying to
		       ;;        evaluate now.
		       ;;   2. (bs e-body) = (bs-old e-body)
		       (if (and (mapping-with-vs-in-flow?
				 vs (expression-abstract-flow3 e bs-old))
				(bs-unchanged-for-e? e-body))
			   v
			   (abstract-value-in-matching-abstract-environment
			    e-body
			    (list->vector
			     (map (lambda (x)
				   (if (memp variable=? x xs1)
				       (new-recursive-closure
					xs-closure
					(restrict-environment vs xs xs-closure)
					(list->vector xs1)
					(list->vector xs2)
					(list->vector es)
					(positionp variable=? x xs1))
				       (vector-ref vs (positionq x xs))))
				  (free-variables e-body)))
			    bs))))
		     ((cons-expression? e)
		      ;; e: (cons e1 e2)
		      ;; e can be safely left un-updated if:
		      ;;   1. exists vs->v' in (bs-old e)--vs same as last
		      ;;                                   iter
		      ;;      - NOTE: we don't say exists vs->v' in (bs e)
		      ;;      - This means that the same environment vs got
		      ;;        evaluated last iteration as we're trying to
		      ;;        evaluate now.
		      ;;   2. (bs e1) = (bs-old e1)
		      ;;   3. (bs e2) = (bs-old e2)
		      (let* ((e1 (cons-expression-car e))
			     (e2 (cons-expression-cdr e))
			     (xs1 (free-variables e1))
			     (xs2 (free-variables e2)))
		       (if (and (mapping-with-vs-in-flow?
				 vs (expression-abstract-flow3 e bs-old))
				(bs-unchanged-for-e? e1)
				(bs-unchanged-for-e? e2))
			   v
			   (let
			     ((v-car
			       (abstract-value-in-matching-abstract-environment
				e1 (restrict-environment vs xs xs1) bs))
			      (v-cdr
			       (abstract-value-in-matching-abstract-environment
				e2 (restrict-environment vs xs xs2) bs)))
			    (if (or (null? v-car) (null? v-cdr))
				(empty-abstract-value)
				(list
				 (make-tagged-pair
				  (cons-expression-tags e) v-car v-cdr)))))))
		     (else (internal-error)))))
		 (cond ((eq? v-new v) b2)
		       ((abstract-value-subset? v-new v) b2)
		       ((abstract-value-subset? v v-new)
			(make-abstract-environment-binding vs v-new))
		       (else (make-abstract-environment-binding
			      vs (abstract-value-union v v-new))))))
	       bs-e)))
	   (if (every-eq? result bs-e) bs-e result))))))
   bs)))

(define (update-abstract-analysis-domains bs bs-old)
 ;; bs is the abstract analysis from some iteration i of flow-analysis
 ;; bs-old is the abstract analysis from iteration i-1 of flow-analysis
 ;; There are two ways in which an abstract environment binding b in an abstract
 ;; flow for expression e can be introduced to the analysis:
 ;;   1. via update-abstract-analysis-domains.
 ;;      If this is how b was introduced, then the appropriate bindings were
 ;;      also introduced for any subexpression of e at the same time as was b.
 ;;   2. via introduce-imprecision-to-abstract-flow.
 ;;        If this is the case, then it is possible that appropriate bindings
 ;;      weren't introduced for subexpressions of e if e was an application,
 ;;      letrec expression, or cons expression.  In this case, we must introduce
 ;;      the appropriate bindings for subexpressions of e.
 ;;        Let's consider possible cases under which this might happen:
 ;;          An expression e which is a non-lambda expression with
 ;;         subexpressions has an entry vs1 -> v1 in its flow.
 ;;         It's children have appropriately derived entries in their flows.
 ;;          There are two main ways that vs1 can be widened:
 ;;           a. No violation of *l1*.  Just widen a value in vs1.
 ;;           b. *l1* violated for e.  Size of flow reduced.  This produces a
 ;;             new environment vs1'.
 ;;          In case (a), this widening will happen in the corresponding
 ;;         environment in the flow in the subexpression(s) of e. No issue here.
 ;;          In case (b), this widening will likely not happen in the same way
 ;;         (if at all) for the flow(s) belonging to the subexpression(s) of e.
 ;;         Here is where we must be careful to create a corresponding entry in
 ;;         each flow belonging to subexpressions of e.  bs-to-add is a
 ;;         conservative approximation of this.
 ;;  There is only one other reason that a new abstract environment binding
 ;; needs added to an abstract flow--because the abstract flows of the
 ;; subexpressions of an application are changed.  This is dealt with in the
 ;; second argument of the abstract-analysis-union in the body of this let*.
 (let*
   ((bs-to-add
     (reduce
      abstract-analysis-union
      (map
       (lambda (b)
	(let* ((e (abstract-expression-binding-expression b))
	       (xs (free-variables e))
	       (flow-old (expression-abstract-flow3 e bs-old)))
	 ;; This is a conservative approximation; it almost certainly a large
	 ;; overapproximation.
	 (cond ((variable-access-expression? e) (empty-abstract-analysis))
	       ((lambda-expression? e) (empty-abstract-analysis))
	       ((application? e)
		(let* ((e1 (application-callee e))
		       (e2 (application-argument e))
		       (xs1 (free-variables e1))
		       (xs2 (free-variables e2)))
		 (reduce
		  abstract-analysis-union
		  (map
		   (lambda (b)
		    (let ((vs (abstract-environment-binding-abstract-values
			       b)))
		     (if (mapping-with-vs-in-flow? vs flow-old)
			 '()
			 (abstract-analysis-union
			  (abstract-analysis-rooted-at e vs)
			  (abstract-apply-prime
			   (abstract-value-in-matching-abstract-environment
			    e1 (restrict-environment vs xs xs1) bs)
			   (abstract-value-in-matching-abstract-environment
			    e2 (restrict-environment vs xs xs2) bs))))))
		   (abstract-expression-binding-abstract-flow b))
		  (empty-abstract-analysis))))
	       ((or (letrec-expression? e) (cons-expression? e))
		(reduce
		 abstract-analysis-union
		 (map
		  (lambda (b)
		   (abstract-analysis-rooted-at
		    e (abstract-environment-binding-abstract-values b)))
		  (abstract-expression-binding-abstract-flow b))
		 (empty-abstract-analysis)))
	       (else (internal-error)))))
       bs)
      (empty-abstract-analysis)))
    (bs-unchanged?
     (map (lambda (b)
	   (let* ((e (abstract-expression-binding-expression b))
		  (bs-e (abstract-expression-binding-abstract-flow b))
		  (bs-old-e (expression-abstract-flow3 e bs-old)))
	    (cons e (or (eq? bs-e bs-old-e)
			;; to catch cases where flow was simply recreated
			(set-equalq? bs-e bs-old-e)))))
	  bs))
    (bs-unchanged-for-e?
     (lambda (e)
      (let ((result (assp expression=? e bs-unchanged?)))
       (if result (cdr result) (internal-error "result not found"))))))
  (abstract-analysis-union
   bs-to-add
   (reduce
    abstract-analysis-union
    (map
     (lambda (b)
      (let* ((e (abstract-expression-binding-expression b))
	     (xs (free-variables e)))
       (cond ((variable-access-expression? e) (empty-abstract-analysis))
	     ((lambda-expression? e) (empty-abstract-analysis))
	     ((application? e)
	      ;; e: (e1 e2)
	      (let* ((e1 (application-callee e))
		     (e2 (application-argument e))
		     (xs1 (free-variables e1))
		     (xs2 (free-variables e2)))
	       ;; No new mappings need to be added if:
	       ;;   1. exists vs->v' in (bs-old e)--vs same as last iter
	       ;;      - NOTE: we don't say exists vs->v' in (bs e)
	       ;;      - This means that the same environment vs gets
	       ;;        evaluated to form bs as we're trying to
	       ;;        evaluate now.
	       ;;      - A "column" (abstract environment binding, really)
	       ;;        vs->v' can only be introduced by:
	       ;;          a. update-abstract-analysis-domains
	       ;;             - If this is the case, then e1 and e2 have had
	       ;;               the appropriate columns added to them already.
	       ;;          b. introduce-imprecision-to-abstract-flow
	       ;;             - If this is the case, then e1 and e2 have NOT
	       ;;                had the appropriate columns added to them.
	       ;;   2. (bs e1) = (bs-old e1) AND
	       ;;   3. (bs e2) = (bs-old e2)
	       (if (or (null? bs)
		       (and (bs-unchanged-for-e? e1)
			    (bs-unchanged-for-e? e2)))
		   (empty-abstract-analysis)
		   (reduce
		    abstract-analysis-union
		    (map
		     (lambda (b)
		      (let ((vs (abstract-environment-binding-abstract-values
				 b)))
		       (abstract-apply-prime
			(abstract-value-in-matching-abstract-environment
			 e1 (restrict-environment vs xs xs1) bs)
			(abstract-value-in-matching-abstract-environment
			 e2 (restrict-environment vs xs xs2) bs))))
		     (abstract-expression-binding-abstract-flow b))
		    (empty-abstract-analysis)))))
	     ((letrec-expression? e) (empty-abstract-analysis))
	     ((cons-expression? e) (empty-abstract-analysis))
	     (else (internal-error)))))
     bs)
    (empty-abstract-analysis)))))

(define (update-abstract-analysis bs bs-old)
 ;; The abstract evaluator induces an abstract analysis. This updates the
 ;; abstract values of all of the abstract-environment bindings of all of the
 ;; abstract expression bindings in the abstract analysis. The updated abstract
 ;; value is calculated by abstract evaluation in the abstract environment of
 ;; the abstract-environment binding. Recursive calls to the abstract evaluator
 ;; are replaced with abstract-value-in-matching-abstract-environment.
 (let* ((bs1 (update-abstract-analysis-ranges bs bs-old))
	(bs2 (update-abstract-analysis-domains bs bs-old))
	;; abstract expression bindings whose expressions aren't yet entered in
	;; *expression-list*
	(bs-new-e (remove-if (lambda (b)
			      (memp expression=?
				    (abstract-expression-binding-expression b)
				    *expression-list*))
			     bs2))
	(bs2 (remove-if (lambda (b) (memq b bs-new-e)) bs2))
	(es-new (map abstract-expression-binding-expression bs-new-e)))
  (unless (null? es-new)
   (set! *expression-list* (append *expression-list* es-new)))
  (append
   ;; This whole map expression works to union bs1 and bs2 together while at
   ;; the same time enforcing monotonicity of the update operation.
   (map (lambda (b1)
	 (let* ((e (abstract-expression-binding-expression b1))
		(bs1 (abstract-expression-binding-abstract-flow b1))
		(bs2 (expression-abstract-flow3 e bs2))
		(bs-old (expression-abstract-flow3 e bs))
		;; abstract environments are unchanged in bs1
		;; abstract environments can only be "added" in bs2
		;;   - those "added" can be either:
		;;     1. truly distinct
		;;     2. repeated copies of an old environment
		;;   - for those fitting #1,
		;;     add-new-mappings-to-abstract-flow
		;;     ensures that the union of bs1 and bs2 is monotonic by
		;;     adjusting the values environments map to.
		;;   - those fitting #2 are discarded
		(bs-new (add-new-mappings-to-abstract-flow bs1 bs2))
		(bs-new2
		 (introduce-imprecision-to-abstract-flow bs-new bs-old)))
	  (make-abstract-expression-binding e bs-new2)))
	bs1)
   (map (lambda (b)
	 (let* ((e (abstract-expression-binding-expression b))
		(bs (abstract-expression-binding-abstract-flow b))
		(bs-new (introduce-imprecision-to-abstract-flow
			 bs (empty-abstract-flow))))
	  (make-abstract-expression-binding e bs-new)))
	bs-new-e))))

;;; Informational Procedures

(define (output-expression-statistics-for-analysis bs)
 (let ((num-expressions (length bs))
       (num-constant-expressions
	(count-if (lambda (b)
		   (constant-expression?
		    (abstract-expression-binding-expression b)))
		  bs))
       (num-variable-access-expressions
	(count-if (lambda (b)
		   (variable-access-expression?
		    (abstract-expression-binding-expression b)))
		  bs))
       (num-lambda-expressions
	(count-if (lambda (b)
		   (lambda-expression?
		    (abstract-expression-binding-expression b)))
		  bs))
       (num-applications
	(count-if (lambda (b)
		   (application? (abstract-expression-binding-expression b)))
		  bs))
       (num-letrec-expressions
	(count-if (lambda (b)
		   (letrec-expression?
		    (abstract-expression-binding-expression b)))
		  bs))
       (num-cons-expressions
	(count-if (lambda (b)
		   (cons-expression?
		    (abstract-expression-binding-expression b)))
		  bs)))
  (format #t "Number of expressions: ~s~%" num-expressions)
  (format #t "  constant expressions: ~s~%"
	  num-constant-expressions)
  (format #t "  variable-access expressions: ~s~%"
	  num-variable-access-expressions)
  (format #t "  lambda expressions: ~s~%" num-lambda-expressions)
  (format #t "  applications: ~s~%" num-applications)
  (format #t "  letrec expressions: ~s~%" num-letrec-expressions)
  (format #t "  cons expressions: ~s~%" num-cons-expressions)))

(define (abstract-value-size v)
 (if (up? v)
     (list 0 0)
     (let inner ((vs-to-explore
		  (reduce append
			  (map (lambda (u)
				(if (atomic-proto-abstract-value? u)
				    '()
				    (branching-value-values u)))
			       v)
			  '()))
		 (num-vs 1)
		 (num-us (length v)))
      (if (null? vs-to-explore)
	  (list num-vs num-us)
	  (let ((result (abstract-value-size (first vs-to-explore))))
	   (inner (rest vs-to-explore)
		  (+ num-vs (first result))
		  (+ num-us (second result))))))))

(define (flow-size bs)
 (reduce
  +
  (map (lambda (b)
	(+ (reduce-vector
	    +
	    (map-vector (lambda (v) (second (abstract-value-size v)))
			(abstract-environment-binding-abstract-values b))
	    0)
	   (second (abstract-value-size
		    (abstract-environment-binding-abstract-value b)))))
       bs)
  0))

(define (analysis-size bs)
 (reduce +
	 (map (lambda (b)
	       (flow-size (abstract-expression-binding-abstract-flow b)))
	      bs)
	 0))

(define (flow-analysis e bs0)
 (set! *num-updates* 0)
 (set! *start-time* (clock-sample))
 (unless *quiet?* (pp (abstract->concrete e)) (newline))
 (let ((result
	(let ((bs0 (initial-abstract-analysis e bs0)))
	 (set! *expression-list*
	       (map abstract-expression-binding-expression bs0))
	 (let loop ((bs bs0)
		    (bs-old (map (lambda (b)
				  (make-abstract-expression-binding
				   (abstract-expression-binding-expression b)
				   (empty-abstract-flow)))
				 bs0)))
	  (when (and (not *quiet?*) (= *num-updates* 0))
	   (pp (externalize-abstract-analysis bs)) (newline)
	   (output-expression-statistics-for-analysis bs))
	  (set! *num-updates* (+ *num-updates* 1))
	  (set! *lookup-misses* 0)
	  (unless *quiet?* (format #t "(Iteration ~s:~%" *num-updates*))
	  (let* ((bs-prime
		  (if *quiet?*
		      (update-abstract-analysis bs bs-old)
		      (time "update-time:~a~%"
			    (lambda () (update-abstract-analysis bs bs-old)))))
		 (total-time (- (clock-sample) *start-time*)))
	   (unless *quiet?*
	    (format #t "Total number of iterations: ~s~%" *num-updates*)
	    (format #t "|bs| = ~s~%" (length bs-prime))
	    (format #t "Total time since start: ~a~%"
		    (number->string-of-length-and-precision total-time 16 2))
	    (let* ((bs-updated
		    (remove-if
		     (lambda (b)
		      (let ((e (abstract-expression-binding-expression b)))
		       (eq? (expression-abstract-flow3 e bs)
			    (abstract-expression-binding-abstract-flow b))))
		     bs-prime))
		   (l8-violated? (lambda (v) (not (l8-met? v))))
		   (b-violating-l8
		    (find-if
		     (lambda (b)
		      (some
		       (lambda (b)
			(or (some-vector
			     l8-violated?
			     (abstract-environment-binding-abstract-values b))
			    (l8-violated?
			     (abstract-environment-binding-abstract-value b))))
		       (abstract-expression-binding-abstract-flow b)))
		     bs-updated)))
	     ;; Check to see if bundle nesting depth limit (*l8*) is violated
	     ;;   in any of the updated abstract enivoronment bindings.
	     ;; needs work
	     (unless (eq? b-violating-l8 #f)
	      (format #t "Bundle nesting depth limit of ~s exceeded~%" *l8*)
	      (pp (externalize-abstract-expression-binding b-violating-l8))
	      (newline)
	      (pp (externalize-abstract-analysis bs-updated)) (newline)
	      (pp (externalize-abstract-analysis bs-prime)) (newline)
	      (internal-error "Terminating because of error"))
	     (format #t "# flows updated: ~s~%" (length bs-updated))
	     (format #t "# of proto-abstract-values updated: ~s~%"
		     (analysis-size bs-updated))
	     (format #t "# of proto-abstract-value in analysis: ~s~%"
		     (analysis-size bs-prime))))
	   (let ((done? (if *quiet?*
			    (abstract-analysis=? bs bs-prime)
			    (time
			     "convergence-check-time:~a~%"
			     (lambda () (abstract-analysis=? bs bs-prime))))))
	    (unless *quiet?* (format #t "done?: ~s)~%" done?))
	    (if done? bs (loop bs-prime bs))))))))
  (format #t "# lookup misses in last iteration: ~s~%" *lookup-misses*)
  (format #t "Analysis reached after ~s updates.~%" *num-updates*)
  (format #t "Total time since start: ~a~%"
	  (number->string-of-length-and-precision
	   (- (clock-sample) *start-time*) 16 2))
  result))

;;; end needs work

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

;;; \AB{V} x \AB{V} -> \AB{V}
(define (abstract-vlad-cons v1 v2) (list (vlad-cons v1 v2)))

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
	  (list (make-tagged-pair tags (first vs) (loop (rest vs))))))))

(define (abstract-base-variables-v v)
 (when (and (list? v) (not (= (length v) 1)))
  (internal-error "How to handle abstract-base-variables-v for v?" v))
 (unless (list? v) (internal-error "Why isn't v a list?" v))
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
	(list (make-bundle-protected (abstract-zero-v (bundle-primal u))
				     (abstract-zero-v (bundle-tangent u)))))
       ((reverse-tagged-value? u)
	(list (make-reverse-tagged-value-protected
	       (abstract-zero-v (reverse-tagged-value-primal u)))))
       ((and (not *church-pairs?*) (tagged-pair? u))
	(list
	 (make-tagged-pair
	  (tagged-pair-tags u)
	  (abstract-zero-v (abstract-vlad-car-u u (tagged-pair-tags u)))
	  (abstract-zero-v (abstract-vlad-cdr-u u (tagged-pair-tags u))))))
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
		       (abstract-value=? (list u-forward)
					 (vlad-value->abstract-value
					  (primitive-procedure-forward
					   (value-binding-value b)))))
		      *value-bindings*)))
	     (if b
		 (vlad-value->abstract-value (value-binding-value b))
		 (let* ((e (forward-transform-inverse
			    (new-lambda-expression
			     (nonrecursive-closure-variable u-forward)
			     (nonrecursive-closure-body u-forward))))
			(x (lambda-expression-variable e))
			(xs (free-variables e)))
		  (list (make-nonrecursive-closure
			 xs
			 ;; We don't do add/remove-slots here.
			 (map-vector abstract-primal-v
				     (nonrecursive-closure-values u-forward))
			 x
			 (index x xs (lambda-expression-body e)))))))))
       ((recursive-closure? u-forward)
	(if (or (null? (recursive-closure-tags u-forward))
		(not (eq? (first (recursive-closure-tags u-forward))
			  'forward)))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)
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
		  (list (make-recursive-closure
			 xs
			 ;; We don't do add/remove-slots here.
			 (map-vector abstract-primal-v
				     (recursive-closure-values u-forward))
			 xs1
			 (list->vector (map lambda-expression-variable es))
			 (list->vector
			  (map (lambda (e)
				(index (lambda-expression-variable e)
				       (append (vector->list xs1) xs)
				       (lambda-expression-body e)))
			       es))
			 (recursive-closure-index u-forward))))))))
       ((bundle? u-forward) (bundle-primal u-forward))
       ((reverse-tagged-value? u-forward)
	(compile-time-warning
	 "Might attempt to take primal of a non-forward value" u-forward))
       ((and (not *church-pairs?*) (tagged-pair? u-forward))
	(if (or (null? (tagged-pair-tags u-forward))
		(not (eq? (first (tagged-pair-tags u-forward)) 'forward)))
	    (compile-time-warning
	     "Might attempt to take primal of a non-forward value" u-forward)
	    (list (make-tagged-pair
		   (rest (tagged-pair-tags u-forward))
		   (abstract-primal-v (tagged-pair-car u-forward))
		   (abstract-primal-v (tagged-pair-cdr u-forward))))))
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
	    (list (make-tagged-pair
		   (rest (tagged-pair-tags u-forward))
		   (abstract-tangent-v (tagged-pair-car u-forward))
		   (abstract-tangent-v (tagged-pair-cdr u-forward))))))
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
		(list (make-bundle (list u) (list u-perturbation))))
	       ((and (not *church-booleans?*)
		     (vlad-boolean? u)
		     (null? u-perturbation))
		(list (make-bundle (list u) (list u-perturbation))))
	       ((and (abstract-real? u) (abstract-real? u-perturbation))
		(list (make-bundle (list u) (list u-perturbation))))
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
		       (make-nonrecursive-closure
			xs
			;; This should use a generalized add/remove-slots here.
			(list->vector
			 (map (lambda (i v)
			       (if i (list-ref vs i) (abstract-j*-v v)))
			      is
			      (vector->list (nonrecursive-closure-values u))))
			x
			(index x xs (lambda-expression-body e))))
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
			(list->vector
			 (map (lambda (e)
			       (index (lambda-expression-variable e)
				      (append (vector->list xs1) xs)
				      (lambda-expression-body e)))
			      es))
			(recursive-closure-index u)))
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
		(list (make-bundle (list u) (list u-perturbation))))
	       ((and (reverse-tagged-value? u)
		     (reverse-tagged-value? u-perturbation)
		     (abstract-legitimate?
		      (reverse-tagged-value-primal u)
		      (reverse-tagged-value-primal u-perturbation)
		      (cons v-perturbation vs-above)
		      (cons (cons v v-perturbation) cs)))
		(list (make-bundle (list u) (list u-perturbation))))
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
		(list (make-tagged-pair (cons 'forward (tagged-pair-tags u))
					(abstract-bundle-internal
					 (tagged-pair-car u)
					 (tagged-pair-car u-perturbation)
					 (cons v-perturbation vs-above)
					 (cons (cons v v-perturbation) cs))
					(abstract-bundle-internal
					 (tagged-pair-cdr u)
					 (tagged-pair-cdr u-perturbation)
					 (cons v-perturbation vs-above)
					 (cons (cons v v-perturbation) cs)))))
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
  (cond ((vlad-pair? u '())
	 (f (closed-proto-abstract-values (abstract-vlad-car-u u '()))
	    (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
	(else (compile-time-warning
	       (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-binary-real f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
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
      (empty-abstract-value))))
   (else (compile-time-warning
	  (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-binary-real-predicate f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
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
      (empty-abstract-value))))
   (else (compile-time-warning
	  (format #f "Argument to ~a might be invalid" s) u)))))

(define (abstract-ternary f s)
 (lambda (u123)
  (cond
   ((vlad-pair? u123 '())
    (let ((v23 (closed-proto-abstract-values (abstract-vlad-cdr-u u123 '()))))
     (reduce
      abstract-value-union
      (map
       (lambda (u1)
	(reduce
	 abstract-value-union
	 (map
	  (lambda (u23)
	   (cond
	    ((vlad-pair? u23 '())
	     (let ((v3 (closed-proto-abstract-values
			(abstract-vlad-cdr-u u23 '()))))
	      (reduce
	       abstract-value-union
	       (map
		(lambda (u2)
		 (reduce abstract-value-union
			 (map (lambda (u3) (list (f u1 u2 u3))) v3)
			 (empty-abstract-value)))
		(closed-proto-abstract-values (abstract-vlad-car-u u23 '())))
	       (empty-abstract-value))))
	    (else (compile-time-warning
		   (format #f "Argument to ~a might be invalid" s) u123))))
	  v23)
	 (empty-abstract-value)))
       (closed-proto-abstract-values (abstract-vlad-car-u u123 '())))
      (empty-abstract-value))))
   (else (compile-time-warning
	  (format #f "Argument to ~a might be invalid" s) u123)))))

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
       (else (internal-error "Not a proto-abstract-value" u))))

(define (externalize-abstract-value v)
 (cond ((up? v) `(up ,(up-index v)))
       ((list? v)
	(cond ((null? v) `(bottom))
	      ((null? (rest v)) (externalize-proto-abstract-value (first v)))
	      (else `(union ,@(map externalize-proto-abstract-value v)))))
       (else (internal-error "Not an abstract value" v))))

(define (externalize-abstract-environment xs vs)
 (unless (and (vector? vs)
	      (every-vector (lambda (v) (or (list? v) (up? v))) vs)
	      (= (length xs) (vector-length vs)))
  (internal-error "Not an abstract environment"))
 (map (lambda (x v) (list x (externalize-abstract-value v)))
      xs (vector->list vs)))

(define (externalize-abstract-environment-binding xs b)
 (unless (abstract-environment-binding? b)
  (internal-error "Not an abstract environment binding"))
 (list (externalize-abstract-environment
	xs (abstract-environment-binding-abstract-values b))
       (externalize-abstract-value
	(abstract-environment-binding-abstract-value b))))

(define (externalize-abstract-flow xs bs)
 (unless (and (list? bs) (every abstract-environment-binding? bs))
  (internal-error "Not an abstract flow"))
 (map (lambda (b) (externalize-abstract-environment-binding xs b)) bs))

(define (externalize-abstract-expression-binding b)
 (unless (abstract-expression-binding? b)
  (internal-error "Not an abstract expression binding"))
 (list (abstract->concrete (abstract-expression-binding-expression b))
       (externalize-abstract-flow
	(free-variables (abstract-expression-binding-expression b))
	(abstract-expression-binding-abstract-flow b))))

(define (externalize-abstract-analysis bs)
 (unless (and (list? bs) (every abstract-expression-binding? bs))
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
	      (new-variable-access-expression 'x2))))
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
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write")
  (abstract-unary (lambda (x) x) "write")
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
 (unless *parse-abstract?* (initialize-forwards-and-reverses!)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
