(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah
;;; CVS version control block - do not edit manually
;;;  $RCSfile$
;;;  $Revision$
;;;  $Date$
;;;  $Source$

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

(define-structure forward-expression-cache-entry e e-forward)

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

(define *forward-expression-cache* '())

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

(define *cache-transformed-expressions?* #f)

(define *memoized?* #f)

(define *church-booleans?* #f)

(define *church-pairs?* #f)

(define *cfa0?* #f)

(define *l1* #f)

(define *l2* #f)

(define *l3* #f)

(define *l4* #f) ; closure depth

(define *depth-measure* #f)

(define *l5* #f) ; pairs in abstract value

(define *l6* #f) ; pair depth limit

(define *anf-convert?* #t)

(define *allow-only-single-concrete-real?* #f)

(define *track-flow-analysis?* #f)

(define *only-initialized-flows?* #f)
(define *only-updated-bindings?* #f)
(define *only-updated-bindings2?* #f)

(define *include-prior-values?* #t)

(define *exclude-prelude?* #f)

(define *debug?* #f)
(define *debug-level* 0)
(define *debug-new?* #f)
(define *debug-level-new* 0)

(define *warn?* #t)
(define *old-initial?* #f)
(define *expression-equality-using-identity?* #f)
(define *expression-equality-using-structural?* #t)
(define *expression-equality-using-alpha?* #f)
(define *use-alpha-equivalence?* #f)
(define *memoize-alpha-matching?* #f)
(define *memoize-nonrecursive-alpha-matching?* #f)

;;; Instrumentation
(define *num-updates* 0)
(define *start-time* #f)

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

(define *bucket-names*
 '(imprec l1 l-rest widen sub safe remove1 remove2 check
	  abstract-analysis=? update-ranges update-domains
	  recalc-unchanged? recalc-unchanged-e?
	  recalc-app? recalc-app
	  recalc-letrec? recalc-letrec
	  recalc-cons? recalc-cons
	  recalc-etc recalc-etc2 recalc-free-variables))
(define *time-buckets* (make-vector (length *bucket-names*) 0.))
(define *call-buckets* (make-vector (length *bucket-names*) 0))
(define *bucket-stack* '())

(define *test?* #f)
(define *new-subset?* #f)
(define *num-subset-times* 10)
(define *subset-times* '())
(define *subset-category-times* '())
(define *paranoid-widen?* #f)
(define *paranoid-update-range?* #f)
(define *paranoid-update?* #f)
(define *fast-letrec?* #t)
(define *fast-cons?* #t)
(define *fast-apply?* #t)
(define *fast-apply-prime?* #t)

(define *quiet?* #f)
(define *machine-style?* #f)
(define *report-all-times?* #f)
(define *widen-first?* #t)
(define *new-cyclicize?* #f)
(define *no-apply-multiply?* #f)
(define *new-widen?* #f)
(define *new-l4-depth?* #f)
(define *picky?* #f)
(define *imprec-no-unroll?* #t)
(define *correct-add-cols?* #t)
(define *aesthetic-reduce-depth?* #f)

(define *output-at-iterations?* #f)
(define *output-whole-analysis?* #f)
(define *output-iterations* '())

(define *value-list* '())
(define *expression-list* '())

;;; Procedures

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
 (or (and (nonrecursive-closure? v)
	  (not (null? (nonrecursive-closure-tags v)))
	  (eq? (first (nonrecursive-closure-tags v)) 'forward))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'forward))
     (bundle? v)
     (and (not *church-pairs?*)
	  (tagged-pair? v)
	  (not (null? (tagged-pair-tags v)))
	  (eq? (first (tagged-pair-tags v)) 'forward))))

(define (vlad-reverse? v)
 (or (and (nonrecursive-closure? v)
	  (not (null? (nonrecursive-closure-tags v)))
	  (eq? (first (nonrecursive-closure-tags v)) 'reverse))
     (and (recursive-closure? v)
	  (not (null? (recursive-closure-tags v)))
	  (eq? (first (recursive-closure-tags v)) 'reverse))
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
	  (else (fuck-up))))
     (and (tagged-pair? v) (equal? (tagged-pair-tags v) tags))))

(define (vlad-car v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take vlad-car of a non-pair" v))
 (if *church-pairs?*
     (cond ((null? tags) (vector-ref (nonrecursive-closure-values v) 0))
	   (else (case (first tags)
		  ((forward) (bundle (vlad-car (primal v) (rest tags))
				     (vlad-car (tangent v) (rest tags))))
		  ((reverse) (*j (vlad-car (*j-inverse v) (rest tags))))
		  (else (fuck-up)))))
     (tagged-pair-car v)))

(define (vlad-cdr v tags)
 (unless (vlad-pair? v tags)
  (run-time-error "Attempt to take vlad-cdr of a non-pair" v))
 (if *church-pairs?*
     (cond ((null? tags) (vector-ref (nonrecursive-closure-values v) 1))
	   (else (case (first tags)
		  ((forward) (bundle (vlad-cdr (primal v) (rest tags))
				     (vlad-cdr (tangent v) (rest tags))))
		  ((reverse) (*j (vlad-cdr (*j-inverse v) (rest tags))))
		  (else (fuck-up)))))
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

(define (cons*ify xs tags)
 (if *church-pairs?*
     (if (null? tags)
	 (let loop ((xs xs))
	  (cond ((null? xs) '())
		((null? (rest xs)) (first xs))
		(else (vlad-cons (first xs) (loop (rest xs))))))
	 (case (first tags)
	  ((forward) (bundle (cons*ify (map primal xs) (rest tags))
			     (cons*ify (map tangent xs) (rest tags))))
	  ((reverse) (*j (cons*ify (map *j-inverse xs) (rest tags))))
	  (else (fuck-up))))
     (if (null? xs)
	 (let loop ((tags tags))
	  (if (null? tags)
	      '()
	      ((case (first tags)
		((forward) j*)
		((reverse) *j)
		(else (fuck-up)))
	       (loop (rest tags)))))
	 (let loop ((xs xs))
	  (if (null? (rest xs))
	      (first xs)
	      (make-tagged-pair tags (first xs) (loop (rest xs))))))))

(define (vlad-procedure? v)
 (and (or (primitive-procedure? v)
	  (nonrecursive-closure? v)
	  (recursive-closure? v))
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
	 (else (fuck-up))))
       (else (fuck-up))))

(define (variable=? x1 x2) (equalq? x1 x2))

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
  e1
  e2
  (sort-variables (union-variables (free-variables e1) (free-variables e2)))))

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
 (for-each (lambda (d)
	    (unless (definition? d)
	     (panic (format #f "Invalid definition: ~s" d))))
	   ds)
 (if *exclude-prelude?*
     `(letrec ,(map (lambda (d)
		     `(,(definens-name (second d))
		       ,(definens-expression (second d) (third d))))
		    ds)
       ,e)
     (standard-prelude
      `(letrec ,(map (lambda (d)
		      `(,(definens-name (second d))
			,(definens-expression (second d) (third d))))
		     ds)
	,e))))

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
	 ((cons-expression? e)
	  (union-variables (loop (cons-expression-car e))
			   (loop (cons-expression-cdr e))))
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
       ((cons-expression? e) (free-variables-old e))
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
  ((cons-expression? e)
   (make-cons-expression (cons-expression-tags e)
			 (index x xs (cons-expression-car e))
			 (index x xs (cons-expression-cdr e))))
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
  ((cons-expression? e)
   (max (anf-max (cons-expression-car e)) (anf-max (cons-expression-cdr e))))
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
       ((cons-expression? e)
	(make-cons-expression (cons-expression-tags e)
			      (substitute x1 x2 (cons-expression-car e))
			      (substitute x1 x2 (cons-expression-cdr e))))
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
	  ((cons-expression? e1)
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
       ((cons-expression? e)
	(unionp vlad-equal?
		(constants-in (cons-expression-car e))
		(constants-in (cons-expression-cdr e))))
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
       ((cons-expression? e)
	(make-cons-expression (cons-expression-tags e)
			      (constant-convert bs (cons-expression-car e))
			      (constant-convert bs (cons-expression-cdr e))))
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
   (if *church-booleans?*
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
     ((cons) (cond (*church-pairs?* (loop (macro-expand e) xs))
		   (else (unless (= (length e) 3)
			  (panic (format #f "Invalid expression: ~s" e)))
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
 (cond ((null? x) '())
       ((and (not *church-booleans?*) (vlad-boolean? x)) '())
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
       ((and (not *church-pairs?*) (tagged-pair? x))
	(make-tagged-pair (tagged-pair-tags x)
			  (zero (vlad-car x (tagged-pair-tags x)))
			  (zero (vlad-cdr x (tagged-pair-tags x)))))
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
 (let ((cache-entry (find-if (lambda (entry)
			      (eq? (forward-expression-cache-entry-e entry) e))
			     *forward-expression-cache*)))
  (if (and *cache-transformed-expressions?* cache-entry)
      (forward-expression-cache-entry-e-forward cache-entry)
      (let* ((e-forward
	      (cond ((variable-access-expression? e) (forwardify-access e))
		    ((lambda-expression? e)
		     (new-lambda-expression
		      (forwardify (lambda-expression-variable e))
		      (forward-transform (lambda-expression-body e))))
		    ((application? e)
		     (new-application
		      (forward-transform (application-callee e))
		      (forward-transform (application-argument e))))
		    ((letrec-expression? e)
		     (new-letrec-expression
		      (map forwardify
			   (letrec-expression-procedure-variables e))
		      (map forwardify (letrec-expression-argument-variables e))
		      (map forward-transform (letrec-expression-bodies e))
		      (forward-transform (letrec-expression-body e))))
		    ((cons-expression? e)
		     (make-cons-expression
		      (cons 'forward (cons-expression-tags e))
		      (forward-transform (cons-expression-car e))
		      (forward-transform (cons-expression-cdr e))))
		    (else (fuck-up))))
	     (expression-cache-entry
	      (make-forward-expression-cache-entry e e-forward)))
       (when *cache-transformed-expressions?*
	(set! *forward-expression-cache*
	      (cons expression-cache-entry *forward-expression-cache*)))
       e-forward))))

(define (forward-transform-inverse e)
 (let ((cache-entry
	(find-if (lambda (entry)
		  (eq? (forward-expression-cache-entry-e-forward entry) e))
		 *forward-expression-cache*)))
  (cond ((and *cache-transformed-expressions?* cache-entry)
	 (forward-expression-cache-entry-e cache-entry))
	(*cache-transformed-expressions?*
	 (panic "Expression not found in cache...and SHOULD be!"))
	((variable-access-expression? e) (unforwardify-access e))
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
	((cons-expression? e)
	 (unless (and (not (null? (cons-expression-tags e)))
		      (eq? (first (cons-expression-tags e)) 'forward))
	  (fuck-up))
	 (make-cons-expression
	  (rest (cons-expression-tags e))
	  (forward-transform-inverse (cons-expression-car e))
	  (forward-transform-inverse (cons-expression-cdr e))))
	(else (fuck-up)))))

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
	       ((and (not *church-pairs?*) (tagged-pair? x-forward))
		(unless (and
			 (not (null? (tagged-pair-tags x-forward)))
			 (eq? (first (tagged-pair-tags x-forward)) 'forward))
		 (run-time-error
		  "Attempt to take tangent of a non-forward value" x-forward))
		(make-tagged-pair (rest (tagged-pair-tags x-forward))
				  (tangent (tagged-pair-car x-forward))
				  (tangent (tagged-pair-cdr x-forward))))
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
  (or (and (null? x) (null? x-perturbation))
      (and (not *church-booleans?*) (vlad-boolean? x) (null? x-perturbation))
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
			(reverse-tagged-value-primal x-perturbation)))
      (and (not *church-pairs?*)
	   (tagged-pair? x)
	   (tagged-pair? x-perturbation)
	   (equal? (tagged-pair-tags x) (tagged-pair-tags x-perturbation))
	   (legitimate? (tagged-pair-car x) (tagged-pair-car x-perturbation))
	   (legitimate? (tagged-pair-cdr x)
			(tagged-pair-cdr x-perturbation)))))
 (define (bundle* xs x-perturbations tags)
  ;; XS is a list, X-PERTURBATIONS is a tuple, the result is a list.
  (cond
   ((null? xs) '())
   ((null? (rest xs)) (list (bundle (first xs) x-perturbations)))
   (else (cons (bundle (first xs) (vlad-car x-perturbations tags))
	       (bundle* (rest xs) (vlad-cdr x-perturbations tags) tags)))))
 (define (bundle x x-perturbation)
  (cond
   ((null? x) (make-bundle x x-perturbation))
   ((and (not *church-booleans?*) (vlad-boolean? x))
    (make-bundle x x-perturbation))
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
   ((and (not *church-pairs?*) (tagged-pair? x))
    (make-tagged-pair
     (cons 'forward (tagged-pair-tags x))
     (bundle (tagged-pair-car x) (tagged-pair-car x-perturbation))
     (bundle (tagged-pair-cdr x) (tagged-pair-cdr x-perturbation))))
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
 ;; needs work: direct tags
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
      (else (fuck-up)))))

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
      (else (fuck-up)))))

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
	  (else (fuck-up))))
     (make-cons-expression tags e1 e2)))

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
	      ((cons-expression? e)
	       (list (make-variable-binding
		      (reverseify x)
		      (make-cons-expression
		       (cons 'reverse (cons-expression-tags e))
		       (reverseify-access (cons-expression-car e))
		       (reverseify-access (cons-expression-cdr e))))))
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
 (unless (let*? e) (fuck-up))
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
   (else (fuck-up)))))

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
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *church-pairs?*) (tagged-pair? v)))
		(vlad-forward? v))
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  `(bundle ,(loop (primal v) quote?)
			   ,(loop (tangent v) quote?)))
		 (else `(forward ,(loop (primal v) quote?)
				 ,(loop (tangent v) quote?)))))
	  ((and (or (not *unabbreviate-transformed?*)
		    (and (not *church-pairs?*) (tagged-pair? v)))
		(vlad-reverse? v))
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
 (let ((m (write-length)))
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
       (else (fuck-up))))

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

;;; Command-line Options

(define (set-l4-depth-measure-from-string! s)
 (cond ((string=? s "abstract-value")
	(set! *depth-measure* abstract-value-depth))
       ((string=? s "matching-nonrecursive-closure")
	(set! *depth-measure* matching-nonrecursive-closure-depth))
       (else (panic "Not a valid depth measure!"))))

;;; \Command-line Options

;;; Instrumentation

(define (instrument-reset)
 (set! *num-calls-abstract-value-union* 0)
 (set! *num-paths-looked-at* 0)
 (set! *total-size-paths-looked-at* 0)
 (set! *num-calls-limit-depth-to* 0)
 (set! *num-calls-reduce-depth!* 0)
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
	 *num-calls-create-abstract-analysis*))

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
 (let ((total-time (- (clock-sample) *start-time*))
       (bucket-time
	(reduce-vector
	 + (map-vector (lambda (x) (if (positive? x) x 0)) *time-buckets*) 0)))
  (format #t "Total number of iterations: ~s~%" *num-updates*)
  (format #t "Total time since start: ~a~%"
	  (number->string-of-length-and-precision total-time 16 2))
  (format #t "Total time in all buckets: ~a~%"
	  (number->string-of-length-and-precision bucket-time 16 2))
  (for-each
   (lambda (bucket-name bucket calls)
    (format
     #t "  time in ~s=~a (~a% total) (~s calls)~%"
     bucket-name
     (number->string-of-length-and-precision bucket 16 2)
     (if (and (positive? bucket) (positive? total-time))
	 (number->string-of-length-and-precision
	  (* 100 (/ bucket total-time)) 6 2)
	 #f)
     calls))
   *bucket-names*
   (vector->list *time-buckets*)
   (vector->list *call-buckets*))))

(define (report-bucket-times2)
 (let ((total-time (- (clock-sample) *start-time*))
       (bucket-time
	(reduce-vector
	 + (map-vector (lambda (x) (if (positive? x) x 0)) *time-buckets*) 0)))
  (format #t "Total number of iterations: ~s~%" *num-updates*)
  (format #t "Total time since start: ~a~%"
	  (number->string-of-length-and-precision total-time 16 2))
  (format #t "Total time in all buckets: ~a~%"
	  (number->string-of-length-and-precision bucket-time 16 2))
  (for-each
   (lambda (bucket-name bucket calls)
    (format
     #t "  time in ~s=~a (~a% total) (~s calls)~%"
     bucket-name
     (number->string-of-length-and-precision bucket 16 2)
     (if (and (positive? bucket) (positive? total-time))
	 (number->string-of-length-and-precision
	  (* 100 (/ bucket total-time)) 6 2)
	 #f)
     calls))
   *bucket-names*
   (vector->list *time-buckets*)
   (vector->list *call-buckets*))))

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

;;; \Instrumentation

(define (recursive-closure-procedure-lambda-expressions v)
 (map-vector (lambda (x e) (new-lambda-expression x e))
	     (recursive-closure-argument-variables v)
	     (recursive-closure-bodies v)))

;;; Expression Alpha Equivalence
;;;
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
			   (letrec-expression-body e2)))
     (and (cons-expression? e1) (cons-expression? e2)
	  (expression-eqv? (cons-expression-car e1)
			   (cons-expression-car e2))
	  (expression-eqv? (cons-expression-cdr e1)
			   (cons-expression-cdr e2)))))

;;;(define *time-true* 0)
;;;(define *time-false* 0)

(define (expression=? e1 e2)
 (cond (*expression-equality-using-identity?* (eq? e1 e2))
       (*expression-equality-using-structural?* (expression-eqv? e1 e2))
       (*expression-equality-using-alpha?*
	(panic "Not yet implemented!"))
       (else (fuck-up))))

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
  ;; needs work: do tags need to be equal?
  ((and (cons-expression? e1)
	(cons-expression? e2)
	(equal? (cons-expression-tags e1) (cons-expression-tags e2)))
   (merge-bindings
    (alpha-match-memoized (cons-expression-car e1) (cons-expression-car e2))
    (alpha-match-memoized (cons-expression-cdr e1) (cons-expression-cdr e2))))
  (else #f)))

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
       ((cons-expression? e) 5)
       (else (panic "Invalid expression!"))))

(define (swap-alpha-bindings bs)
 (if (eq? #f bs)
     #f
     (map (lambda (b) (make-alpha-binding (alpha-binding-variable2 b)
					  (alpha-binding-variable1 b)))
	  bs)))

(define alpha-match-memoized
 (let ((cache (make-vector 6 '())))
  ;; an implicit assumption is that e1 and e2 must be of same type
  (define (cache-lookup e1 e2)
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
	#f)))
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
  ;; needs work: do tags need to be equal?
  ((and (cons-expression? e1)
	(cons-expression? e2)
	(equal? (cons-expression-tags e1) (cons-expression-tags e2)))
   (merge-bindings (alpha-match-not-memoized (cons-expression-car e1)
					     (cons-expression-car e2))
		   (alpha-match-not-memoized (cons-expression-cdr e1)
					     (cons-expression-cdr e2))))
  (else #f)))

(define (alpha-match e1 e2)
 (if *memoize-alpha-matching?*
     (alpha-match-memoized e1 e2)
     (alpha-match-not-memoized e1 e2)))

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
 (if *memoize-nonrecursive-alpha-matching?*
     (nonrecursive-closure-alpha-bindings-memoized u1 u2)
     (nonrecursive-closure-alpha-bindings-not-memoized u1 u2)))

(define (recursive-closure-alpha-bindings u1 u2)
 (define (make-letrec-expression-from-recursive-closure u)
  (new-letrec-expression
   (vector->list (recursive-closure-procedure-variables u))
   (vector->list (recursive-closure-argument-variables u))
   (vector->list (recursive-closure-bodies u))
   (new-variable-access-expression
    (vector-ref (recursive-closure-procedure-variables u)
		(recursive-closure-index u)))))
 (alpha-match (make-letrec-expression-from-recursive-closure u1)
	      (make-letrec-expression-from-recursive-closure u2)))

(define (recursive-closure-alpha-bindings-memoized u1 u2)
 (define (make-letrec-expression-from-recursive-closure u)
  (new-letrec-expression
   (vector->list (recursive-closure-procedure-variables u))
   (vector->list (recursive-closure-argument-variables u))
   (vector->list (recursive-closure-bodies u))
   (new-variable-access-expression
    (vector-ref (recursive-closure-procedure-variables u)
		(recursive-closure-index u)))))
 (alpha-match (make-letrec-expression-from-recursive-closure u1)
	      (make-letrec-expression-from-recursive-closure u2)))

;;; \Expression Alpha Equivalence

;;; Abstract-Analysis Access

(define (lookup-expression-binding e bs)
 (find-if
  (lambda (b) (expression=? e (abstract-expression-binding-expression b)))
  bs))

(define (expression-abstract-flow2 e bs)
 (let ((b (lookup-expression-binding e bs)))
  (if (eq? b #f) #f (abstract-expression-binding-abstract-flow b))))

(define (expression-abstract-flow3 e bs)
 (let ((b (lookup-expression-binding e bs)))
  (if (eq? b #f) '() (abstract-expression-binding-abstract-flow b))))

(define (expression-abstract-flow e bs)
 (abstract-expression-binding-abstract-flow
  ;; needs work: Can make abstract-analysis access O(1) instead of O(n).
  ;; needs work: Do we need identity or alpha equivalence here?
  (let ((aeb (find-if (lambda (b)
		       (expression=? (abstract-expression-binding-expression b)
				     e))
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
       ((branching-value? u)
	(make-branching-value-with-new-values
	 u (map (lambda (v) (cyclicize-abstract-value-internal v vs))
		(branching-value-values u))))
       (else (fuck-up))))

(define (cyclicize-abstract-value-internal v vs)
 (cond ((up? v) (list-ref vs (up-index v)))
       ((null? v) v)
       (else (let ((v1 (cons #f #f)))
	      (let loop ((us v) (v2 v1))
	       (set-car! v2
			 (cyclicize-proto-abstract-value-internal
			  (first us) (cons v1 vs)))
	       (cond ((null? (rest us))
		      (set-cdr! v2 '())
		      (if (every-eq? v v1) v v1))
		     (else (set-cdr! v2 (cons #f #f))
			   (loop (rest us) (cdr v2)))))))))

(define (cyclicize-proto-abstract-value u)
 (cyclicize-proto-abstract-value-internal u '()))

(define (cyclicize-abstract-value v)
 (cyclicize-abstract-value-internal v '()))

(define (cyclicize-proto-abstract-value2 u vs vs-memoized)
 (cond ((null? u) (list u vs-memoized))
       ((eq? u #t) (list u vs-memoized))
       ((eq? u #f) (list u vs-memoized))
       ((real? u) (list u vs-memoized))
       ((eq? u 'real) (list u vs-memoized))
       ((primitive-procedure? u) (list u vs-memoized))
       ((branching-value? u)
	(let loop ((u-vs (branching-value-values u))
		   (u-vs-new '())
		   (vs-memoized vs-memoized))
	 (if (null? u-vs)
	     (list (make-branching-value-with-new-values u (reverse u-vs-new))
		   vs-memoized)
	     (let ((result
		    (cyclicize-abstract-value2 (first u-vs) vs vs-memoized)))
	      (loop (rest u-vs)
		    (cons (first result) u-vs-new)
		    (second result))))))
       (else (fuck-up))))

(define (cyclicize-abstract-value2 v vs vs-memoized)
 (cond ((up? v) (list (list-ref vs (up-index v)) vs-memoized))
       ((null? v) (list v vs-memoized))
       ((assq v vs-memoized) (list (cdr (assq v vs-memoized)) vs-memoized))
       (else (let ((v1 (cons #f #f)))
	      (let loop ((us v) (v2 v1) (vs-memoized vs-memoized))
	       (let* ((result (cyclicize-proto-abstract-value2
			       (first us) (cons v1 vs) vs-memoized))
		      (u (first result))
		      (vs-memoized (second result)))
		(set-car! v2 u)
		(cond ((null? (rest us))
		       (set-cdr! v2 '())
		       (if (every-eq? v v1)
			   (list v (cons (cons v v) vs-memoized))
			   (list v1 (cons (cons v v1) vs-memoized))))
		      (else (set-cdr! v2 (cons #f #f))
			    (loop (rest us) (cdr v2) vs-memoized)))))))))

;;; Uncyclicization of (Proto) Abstact Values

(define (uncyclicize-proto-abstract-value-internal u vs)
 (cond ((null? u) u)
       ((eq? u #t) u)
       ((eq? u #f) u)
       ((real? u) u)
       ((eq? u 'real) u)
       ((primitive-procedure? u) u)
       ((branching-value? u)
	(make-branching-value-with-new-values
	 u (map (lambda (v) (uncyclicize-abstract-value-internal v vs))
		(branching-value-values u))))
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
 (or (eq? v1 v2)
     (and (abstract-value-subset? v1 v2) (abstract-value-subset? v2 v1))))

(define (empty-abstract-value) '())

;;; Abstract Value Union

;;; Variables

;;; \Variables

;;; General

(define (replaceq x x-prime l) (list-replace l (positionq x l) x-prime))

(define (minimal-elements <? s)
 ;; belongs in QobiScheme
 (remove-if (lambda (e) (some (lambda (e-prime) (<? e-prime e)) s)) s))

(define (rest* l k) (if (zero? k) l (rest* (rest l) (- k 1))))

(define (cross-product . &vs)
 (if (null? &vs)
     '()
     ;; (LIST (LIST* (LIST* u))) x (LIST* u) -> (LIST (LIST* (LIST* u)))
     (reduce (lambda (vss v)
	      (reduce append
		      (map (lambda (vs)
			    (map (lambda (u) (append vs `((,u))))
				 v))
			   vss)
		      '()))
	     (cons (map (compose list list) (first &vs)) (rest &vs))
	     '())))

(define (is-cyclic? v)
 (let loop? ((v v) (v-context '()))
  (or (not (eq? (memq v v-context) #f))
      (and (not (up? v))
	   (let ((u-context (cons v v-context)))
	    (some (lambda (u)
		   (and (or (nonrecursive-closure? u) (recursive-closure? u))
			(some-vector (lambda (v) (loop? v u-context))
				     (closure-values u))))
		  v))))))

(define (equalq? x y)
 (cond ((eq? x y) #t)
       ((pair? x)
	(and (pair? y) (equalq? (car x) (car y)) (equalq? (cdr x) (cdr y))))
       ((vector? x)
	(let ((lx (vector-length x)))
	 (and (vector? y)
	      (= (vector-length y) lx)
	      (let test ((i (- lx 1)))
	       (or (= i -1)
		   (and (equalq? (vector-ref x i) (vector-ref y i))
			(test (- i 1))))))))
       ((string? x)
	(and (string? y) (string=? x y)))
       ((%record? x)
	((%record-lookup-method x '%to-equal?) x y))
       (else (eqv? x y))))

(define (remove-duplicates-circular-safe l)
 (when (and #t (is-cyclic? l))
  (format #t "v=") (pp (externalize-abstract-value l)) (newline)
  (panic "v is cyclic!!!"))
 (let loop ((i 0) (l l))
  (cond ((= i (length l)) l)
	((memp equalq? (list-ref l i) (sublist l 0 i))
	 (loop i (list-remove l i)))
	(else (loop (+ i 1) l)))))

(define (abstract-value-size v)
 (if (up? v)
     (list 0 0)
     (let inner
       ((vs-to-explore
	 (reduce
	  append
	  (map (lambda (u)
		(if (branching-value? u) (branching-value-values u) '()))
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

(define (abstract-environment-binding-values b)
 (cons (abstract-environment-binding-abstract-value b)
       (vector->list (abstract-environment-binding-abstract-values b))))

(define (abstract-flow-values bs)
 (reduce append (map abstract-environment-binding-values bs) '()))

(define (abstract-expression-binding-values b)
 (abstract-flow-values (abstract-expression-binding-abstract-flow b)))

(define (abstract-analysis-values bs)
 (reduce append (map abstract-expression-binding-values bs) '()))

(define (process-nodes-in-abstract-value-tree f v v-context)
 (if (up? v)
     v
     (let ((v-new (f v v-context)))
      (let loop ((us v-new) (us-new '()))
       (if (null? us)
	   (let ((us-new (reverse us-new))) (if (every-eq? v us-new) v us-new))
	   (let ((u (first us)))
	    (cond ((or (null? u)
		       (boolean? u)
		       (abstract-real? u)
		       (primitive-procedure? u))
		   (loop (rest us) (cons u us-new)))
		  ((branching-value? u)
		   (let ((u-context (cons v v-context)))
		    (loop (rest us)
			  (cons (make-branching-value-with-new-values
				 u (map (lambda (v)
					 (process-nodes-in-abstract-value-tree
					  f v u-context))
					(branching-value-values u)))
				us-new))))
		  (else (panic "Not a proto-abstract-value")))))))))

;;; Perhaps the first eq? check is a slowdown...
(define (every-eq? l1 l2)
 (or (eq? l1 l2) (and (= (length l1) (length l2)) (every eq? l1 l2))))

(define (every-vector-eq? v1 v2)
 (and (= (vector-length v1) (vector-length v2)) (every-vector eq? v1 v2)))

;;; \General

;;; Closure Procedures

(define (closure? u)
 (or (nonrecursive-closure? u) (recursive-closure? u)))

(define (closure-tags u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-tags u))
       ((recursive-closure? u) (recursive-closure-tags u))
       (else (fuck-up))))

(define (closure-values u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-values u))
       ((recursive-closure? u) (recursive-closure-values u))
       (else (panic "Not a closure!"))))

(define (closure-match? u1 u2)
 (when (not (and (closure? u1) (closure? u2)))
  (panic "u1 and u2 should both be closures!"))
 (cond ((and (nonrecursive-closure? u1) (nonrecursive-closure? u2))
	(nonrecursive-closure-match? u1 u2))
       ((and (recursive-closure? u1) (recursive-closure? u2))
	(recursive-closure-match? u1 u2))
       (else #f)))

(define (closure-values-matching u1 u2)
 (cond ((and (nonrecursive-closure? u1) (nonrecursive-closure? u2))
	(nonrecursive-closure-values-matching u1 u2))
       ((and (recursive-closure? u1) (recursive-closure? u2))
	(recursive-closure-values-matching u1 u2))
       (else (panic "u1 and u2 should be the same type of closure!"))))

(define (make-closure-with-new-values u vs)
 (cond ((nonrecursive-closure? u)
	(make-nonrecursive-closure
	 (nonrecursive-closure-variables u)
	 vs
	 (nonrecursive-closure-variable u)
	 (nonrecursive-closure-body u)))
       ((recursive-closure? u)
	(make-recursive-closure
	 (recursive-closure-variables u)
	 vs
	 (recursive-closure-procedure-variables u)
	 (recursive-closure-argument-variables u)
	 (recursive-closure-bodies u)
	 (recursive-closure-index u)))
       (else (panic "Not a closure!"))))

(define (pick-closures-to-coalesce us)
 (cond ((nonrecursive-closure? (first us))
	(pick-nonrecursive-closures-to-coalesce us))
       ((recursive-closure? (first us))
	(pick-recursive-closures-to-coalesce us))
       (else (panic "us must be a list of {non,}recursive-closures!"))))

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
	  (every-vector-eq?
			(recursive-closure-argument-variables u1)
			(recursive-closure-argument-variables u2))
	  (every-vector-eq?
			(recursive-closure-procedure-variables u1)
			(recursive-closure-procedure-variables u2))
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

;;; \Closure Procedures

;;; Pair Procedures

(define (tagged-pair-match? u1 u2)
 (equal? (tagged-pair-tags u1) (tagged-pair-tags u2)))

(define (tagged-pair-values u) (list (tagged-pair-car u) (tagged-pair-cdr u)))

(define (make-tagged-pair-with-new-values u vs)
 (make-tagged-pair (tagged-pair-tags u) (first vs) (second vs)))

(define (pick-pairs-to-coalesce us)
 (sublist us 0 2))

;;; \Pair Procedures

;;; Bundle Procedures

(define (bundle-match? u1 u2)
 ;; do we really want to check for non-bundle u1, u2?
 (and (bundle? u1) (bundle? u2)))

(define (bundle-values u) (list (bundle-primal u) (bundle-tangent u)))

(define (make-bundle-with-new-values u vs)
 ;; should we do a check here and preserve eq?-ness if possible?
 (make-bundle (first vs) (second vs)))

;;; \Bundle Procedures

;;; Branching Value Procedures

;;; Should we restrict closures with no free variables from being considered
;;; branching values?  They would then be atomic values...
(define (branching-value? u) (or (closure? u) (tagged-pair? u) (bundle? u)))

(define (branching-value-match? u1 u2)
 (cond ((and (closure? u1) (closure? u2)) (closure-match? u1 u2))
       ((and (tagged-pair? u1) (tagged-pair? u2)) (tagged-pair-match? u1 u2))
       ((and (bundle? u1) (bundle? u2)) (bundle-match? u1 u2))
       (else #f)))

(define (branching-value-values u)
 ;; In order to preserve the type of this function, we require that closures
 ;; return a list of values.
 (cond ((closure? u) (vector->list (closure-values u)))
       ((tagged-pair? u) (tagged-pair-values u))
       ((bundle? u) (bundle-values u))
       (else (fuck-up))))

(define (branching-value-values-matching u1 u2)
 (if (and (closure? u1) (closure? u2))
     (vector->list (closure-values-matching u1 u2))
     (branching-value-values u2)))

(define (make-branching-value-with-new-values u vs)
 ;; In order to preserve the type of this function, we require that closures
 ;;   take a list of values instead of a vector of them.
 ;; In addition, we preserve eq?-ness of u if vs are identical to
 ;;   (branching-value-values u).
 (cond ((every-eq? vs (branching-value-values u)) u)
       ((closure? u) (make-closure-with-new-values u (list->vector vs)))
       ((tagged-pair? u) (make-tagged-pair-with-new-values u vs))
       ((bundle? u) (make-bundle-with-new-values u vs))
       (else (fuck-up))))

;;; \Branching Value Procedures

;;; Widen

;;; Widen->General

;;; to-do: Consider ditching (LIST addition) for a list of lists.
(define-structure addition index values)

(define (create-addition-to v v-add)
 ;; v is expected to be an up
 ;; v-add may either be and up or a value
 (when (< (up-index v) 0)
  (format #t "create~%")
  (pp (externalize-addition (make-addition (up-index v) (list v-add))))
  (newline)
  (panic "We should never have negative ups!"))
 (make-addition (up-index v) (list v-add)))

(define (merge-additions as1 as2)
 (cond ((null? as1) as2)
       ((null? as2) as1)
       (else (let* ((a1 (first as1))
		    (a2 (find-if (lambda (a2)
				  (= (addition-index a1) (addition-index a2)))
				 as2)))
	      (if (not (eq? #f a2))
		  (merge-additions
		   (rest as1)
		   (cons
		    (make-addition
		     (addition-index a1)
		     (append (addition-values a1) (addition-values a2)))
		    (removeq a2 as2)))
		  (merge-additions (rest as1) (cons a1 as2)))))))

(define (some-proto-abstract-value?-internal p u u-context)
 (cond ((or (null? u)
	    (boolean? u)
	    (abstract-real? u)
	    (primitive-procedure? u))
	#f)
       ((branching-value? u)
	(some (lambda (v) (some-abstract-value?-internal p v u-context))
	      (branching-value-values u)))
       (else (panic (format #f "Not a handled proto-abstract-value: ~s"
			    (externalize-proto-abstract-value u))))))

(define (some-abstract-value?-internal p v v-context)
 (cond ((p v v-context) #t)
       ((up? v) #f)
       (else (some (lambda (u) (some-proto-abstract-value?-internal
				p u (cons v v-context)))
		   v))))

(define (some-proto-abstract-value? p u)
 (some-proto-abstract-value?-internal p u '()))

(define (some-abstract-value? p v)
 (some-abstract-value?-internal p v '()))

(define (proto-process-free-ups-internal f u u-context)
 (cond ((or (null? u)
	    (boolean? u)
	    (abstract-real? u)
	    (primitive-procedure? u))
	u)
       ((branching-value? u)
	(make-branching-value-with-new-values
	 u (map (lambda (v) (process-free-ups-internal f v u-context))
		(branching-value-values u))))
;;;       ((or (nonrecursive-closure? u) (recursive-closure? u))
;;;	(make-closure-with-new-values
;;;	 u (map-vector (lambda (v) (process-free-ups-internal f v u-context))
;;;		       (closure-values u))))
;;;       ((tagged-pair? u)
;;;	(make-tagged-pair-with-new-values
;;;	 u (map (lambda (v) (process-free-ups-internal f v u-context))
;;;		(tagged-pair-values u))))
       (else (fuck-up))))

(define (process-free-ups-internal f v v-context)
 (cond ((free-up? v v-context) (f v v-context))
       ((up? v) v)
       (else (map (lambda (u)
		   (proto-process-free-ups-internal f u (cons v v-context)))
		  v))))

(define (proto-process-free-ups f u)
 (proto-process-free-ups-internal f u '()))

(define (process-free-ups f v) (process-free-ups-internal f v '()))

(define (decrement-free-ups-by k v)
 (process-free-ups (lambda (up up-context) (make-up (- (up-index up) k))) v))

(define (decrement-free-ups v) (decrement-free-ups-by 1 v))

(define (proto-decrement-free-ups-by k u)
 (proto-process-free-ups
  (lambda (up up-context) (make-up (- (up-index up) k))) u))

(define (proto-decrement-free-ups u) (proto-decrement-free-ups-by 1 u))

(define (increment-free-ups-by k v)
 (process-free-ups (lambda (up up-context) (make-up (+ (up-index up) k))) v))

(define (increment-free-ups v) (increment-free-ups-by 1 v))

(define (free-up? v v-context)
 (and (up? v) (>= (up-index v) (length v-context))))

(define (free-up-reference-level up up-context)
 (let ((l (- (up-index up) (length up-context))))
  (if (negative? l) #f l)))

(define (make-free-up-referencing index up-context)
 (make-up (+ index (length up-context))))

(define (process-additions-for-shifting-past-value as v-new)
 ;; returns: (LIST addition)
 (if #f
     ;; old, possibly increasing-depth way
     (map
      (lambda (a)
       (make-addition
	(- (addition-index a) 1)
	(map (lambda (v)
	      (decrement-free-ups
	       (process-free-ups
		v
		(lambda (up up-depth)
		 (= (free-up-reference-level up up-depth) 0))
		(lambda (up up-depth)
		 (increment-free-ups-by v-new (+ up-depth 1))))))
	     (addition-values a))))
      as)
     ;; new way:
     ;;  a. all top-level additions referencing v-new (which would all be
     ;;     (up 0)'s) are replaced with v-new
     ;;  b. all additions (i (v-i1 ...)) which have references to v-new in one
     ;;     of the trees v-i1, ... (but not at the root of any of the trees)
     ;;     should have these references to v-new replaced with a reference
     ;;     (up i), and v-new should be added to the addition to i:
     ;;       (i (v-i1[v-new \ (up i)] ...[v-new \ (up i)] v-new))
     ;;  - this is conservative; sometimes references to v-new might be able to
     ;;    be safely expanded, but you never know...
     (map
      ;; decrement ups in all additions
      (lambda (a)
       (make-addition
	(- (addition-index a) 1)
	(map (lambda (v) (decrement-free-ups v)) (addition-values a))))
      (merge-additions
       (map
	(lambda (a)
	 (make-addition
	  (addition-index a)
	  (map (lambda (v)
		(process-free-ups
		 (lambda (up up-context)
		  (cond ((and (= (free-up-reference-level up up-context) 0)
			      (= (length up-context) 0))
			 v-new)
			((= (free-up-reference-level up up-context) 0)
			 (make-free-up-referencing (addition-index a)
						   up-context))
			(else up)))
		 v))
	       (addition-values a))))
	as)
       (reduce
	merge-additions
	(map
	 (lambda (a)
	  (if (some (lambda (v)
		     (some-abstract-value?
		      (lambda (v v-context)
		       (and (free-up? v v-context)
			    (= (free-up-reference-level v v-context) 0)))
		      v))
		    (addition-values a))
	      (list (make-addition (addition-index a) (list v-new)))
	      '()))
	 as)
	'())))))

(define (shift-additions-up-in-context as v-context)
 ;; returns: (LIST addition)
 ;; 1. all additions with top-level (UP 0) need to have the
 ;;    proto-abstract-values from (first v-context) added to them.
 ;; 2. all additions referencing (first v-context) need to have (a) the
 ;;    proto-abstract-values from (first v-context) added to them, as well as
 ;;    (b) changing the reference to point to the value the addition is going.
 ;; 3. every addition needs its index, as well as each free-up, decremented.
 ;; This breaks testing on v3.  This is b/c (first v-context) has a free (UP 0)
 ;; and it's added in b/c an addition is referencing it.  Well, the (UP 0) is
 ;; decremented, and that's a problem...
 (map
  ;;3
  (lambda (a)
   (make-addition
    (- (addition-index a) 1)
    (map (lambda (u-or-up)
	  (cond ((and (up? u-or-up) (= (up-index u-or-up) 0))
		 (panic "This should already have been replaced!"))
		((up? u-or-up) (make-up (- (up-index u-or-up) 1)))
		(else (proto-decrement-free-ups u-or-up))))
	 (addition-values a))))
  (merge-additions
   (map
    (lambda (a)
     (make-addition
      (addition-index a)
      ;;2b
      (reduce
       append
       (map (lambda (u-or-up)
	     (cond ((and (up? u-or-up) (= (up-index u-or-up) 0)) ;1
		    (first v-context))
		   ((up? u-or-up) (list u-or-up))
		   (else
		    (list
		     (proto-process-free-ups
		      (lambda (up up-context)
		       (if (= (free-up-reference-level up up-context) 0)
			   (make-free-up-referencing (addition-index a)
						     up-context)
			   up))
		      u-or-up)))))
	    (addition-values a))
       '())))
    as)
   ;;2a
   (reduce
    merge-additions
    (map
     (lambda (a)
      (if (some (lambda (u-or-up)
		 (and (not (up? u-or-up))
		      (some-proto-abstract-value?
		       (lambda (v v-context)
			(and (free-up? v v-context)
			     (= (free-up-reference-level v v-context) 0)))
		       u-or-up)))
		(addition-values a))
	  (list (make-addition
		 (addition-index a)
		 (map
		  (lambda (u)
		   (proto-process-free-ups
		    (lambda (up up-context)
		     (if (= (free-up-reference-level up up-context) 0)
			 (make-free-up-referencing (addition-index a)
						   up-context)
			 up))
		    u))
		  (first v-context))))
	  '()))
     as)
    '()))))

(define (widen-over-abstract-value-tree widen-node v v-context)
 ;; needs work:
 ;; Can we write a general function to walk the tree for reals, closures, and
 ;; depth?
 v)

;;; \Widen->General

;;; Widen->Flows

;;; \Widen->Flows

;;; Widen->Reals

(define (widen-abstract-value-by-coalescing-reals v)
 (if (eq? *l2* #f)
     v
     (process-nodes-in-abstract-value-tree
      (lambda (v v-context) (if (> (count-if abstract-real? v) *l2*)
				(cons 'real (remove-if abstract-real? v))
				v))
      v
      '())))

;;; \Widen->Reals

;;; Widen->Closures
;;; to-do: deal with recursive closures, too

(define (pick-nonrecursive-closures-to-coalesce us)
 (sublist us 0 2))

(define (pick-recursive-closures-to-coalesce us)
 (sublist us 0 2))

;;; needs work: this only deals with the most trivial of duplicate
;;;             proto-abstract values
(define (union-for-widening v1 v2)
 ;; assumed: v1 and v2 share the same context.  In other words, all
 ;;          free-up-reference-levels which are the same refer to the same
 ;;          values.
 (cond ((and (up? v1) (up? v2))
	(cond ((> (up-index v1) (up-index v2))
	       (cons v1 (list (create-addition-to v1 v2))))
	      ((< (up-index v1) (up-index v2))
	       (cons v2 (list (create-addition-to v2 v1))))
	      (else ; (= (up-index v1) (up-index v2))
	       (cons v1 '()))))
       ((up? v1) (cons v1 (list (create-addition-to v1 v2))))
       ((up? v2) (cons v2 (list (create-addition-to v2 v1))))
       ;; needs work: there can still be duplicate proto-abstract values here;
       ;;             to really remove all (or more) duplicates is much more
       ;;             work, though.
       (else (cons (remove-duplicates-circular-safe (append v1 v2)) '()))))

(define (widen-single-abstract-value v)
 ;; assumes: *l3* is active
 ;; returns: value x (LIST additions-to-value)
 (let outer ((closure-uss (transitive-equivalence-classesp
			   closure-match?
			   (remove-if-not closure? v)))
	     (us (remove-if closure? v))
	     (changed? #f))
  (cond ((null? closure-uss) (if changed? (cons us '()) (cons v '())))
	((<= (length (first closure-uss)) *l3*)
	 (outer (rest closure-uss) (append us (first closure-uss)) changed?))
	(else				; *l3* violated
	 (let* ((u1-u2 (pick-closures-to-coalesce (first closure-uss)))
		(u1 (first u1-u2))
		(u2 (second u1-u2)))
	  (let inner ((vs1 (vector->list (closure-values u1)))
		      (vs2 (vector->list (closure-values-matching u1 u2)))
		      (vs '())
		      (additions '()))
	   (if (null? vs1)
	       (let* ((u-new (make-closure-with-new-values
			      u1 (list->vector (reverse vs))))
		      (closure-uss-new
		       (cons (cons u-new (removeq
					  u2 (removeq u1 (first closure-uss))))
			     (rest closure-uss))))
		(if (null? additions)
		    (outer closure-uss-new us #t)
		    (cons (append us (reduce append closure-uss-new '()))
			  additions)))
	       (let ((v-additions
		      (union-for-widening (first vs1) (first vs2))))
		(inner (rest vs1)
		       (rest vs2)
		       (cons (car v-additions) vs)
		       (merge-additions (cdr v-additions) additions))))))))))

(define (apply-additions-to v additions)
 ;; returns: value x (LIST additions-to-value)
 (when (up? v) (panic "How can v be an up???"))
 (let* ((additions-to-v (find-if (lambda (a) (= (addition-index a) 0))
				 additions))
	(additions-rest (removeq additions-to-v additions)))
  (if (or (eq? #f additions-to-v)
	  ;; needs work: is this needed???
	  (null? (addition-values additions-to-v)))
      ;; nothing here...move along
      (cons v (process-additions-for-shifting-past-value additions v))
      (let* ((v-additions-new
	      (let loop
		((v-new v)
		 ;; note that we sort vs-to-add to favor links referencing
		 ;; values further up the tree
		 (vs-to-add (sort (map decrement-free-ups
				       (addition-values additions-to-v))
				  (lambda (v1 v2)
				   ;; here I am: this condition doesn't happen
				   (when (or (up? v1) (up? v2))
				    (panic "***vs-to-add contains raw ups!"))
				   (cond ((and (up? v1) (up? v2))
					  (> (up-index v1) (up-index v2)))
					 ((up? v1) #t)
					 ((up? v2) #f)
					 (else #t)))
				  identity)))
	       (if (null? vs-to-add)
		   (cons v-new '())
		   (let* ((v-add (first vs-to-add))
			  (v-additions-new (union-for-widening v-new v-add))
			  (v-new (car v-additions-new))
			  (additions-new (cdr v-additions-new)))
		    (if (null? additions-new)
			(loop v-new (rest vs-to-add))
			;; v-add is a link
			(cons
			 v-new
			 ;; to-do: is this wrong?
			 (merge-additions
			  (map
			   (lambda (v) (create-addition-to v-new v))
			   (rest vs-to-add))
			  additions-new)))))))
	     (v-new (car v-additions-new))
	     (additions-new
	      (process-additions-for-shifting-past-value
	       (merge-additions additions-rest (cdr v-additions-new))
	       v-new)))
       ;; if after applying the addition to v there are no additions left,
       ;; perform another widen-abstract-value-tree-internal on v-new
       (if (null? additions-new)
	   (widen-abstract-value-tree-internal v-new)
	   (cons v-new additions-new))))))

(define (widen-abstract-value-tree-internal-old v)
 ;; returns: value x (LIST additions-to-value)
 (if (up? v)
     (cons v '())
     (let* ((v-additions (widen-single-abstract-value v))
	    (v-new (car v-additions))
	    (additions (cdr v-additions))
	    (changed? (not (eq? v-new v))))
      (cond ((and (null? additions) (up? v-new))
	     (cons v-new '()))
	    ((null? additions)
	     ;; recursively widen each abstract value below v-new
	     (let outer ((us v-new) (us-new '()) (changed? changed?))
	      (if (null? us)
		  (if changed? (cons us-new '()) (cons v '()))
		  (let ((u (first us)))
		   (define (do-branching-value vs make-branching-value)
		    (define (continue-with-outer vs-new)
		     (if (every-eq? vs vs-new)
			 (outer (rest us) (cons u us-new) changed?)
			 (outer (rest us)
				(cons (make-branching-value vs-new) us-new)
				#t)))
		    (define (exit-outer vs additions)
		     (apply-additions-to
		      (append (rest us)
			      (cons (make-branching-value vs) us-new))
		      additions))
		    (let inner ((vs vs) (vs-new '()))
		     (if (null? vs)
			 (continue-with-outer (reverse vs-new))
			 (let* ((v-additions
				 (widen-abstract-value-tree-internal
				  (first vs)))
				(v-new (car v-additions))
				(additions (cdr v-additions)))
			  (if (null? additions)
			      (inner (rest vs) (cons v-new vs-new))
			      (exit-outer
			       (append (reverse (cons v-new vs-new))
				       (rest vs))
			       additions))))))
		   (cond ((or (null? u)
			      (boolean? u)
			      (abstract-real? u)
			      (primitive-procedure? u))
			  (outer (rest us) (cons u us-new) changed?))
			 ((closure? u)
			  (do-branching-value
			   (vector->list (closure-values u))
			   (lambda (vs) (make-closure-with-new-values
					 u (list->vector vs)))))
			 ((tagged-pair? u)
			  (do-branching-value
			   (list (tagged-pair-car u) (tagged-pair-cdr u))
			   (lambda (vs) (make-tagged-pair (tagged-pair-tags u)
							  (first vs)
							  (second vs)))))
			 (else (panic "Not (yet) implemented!")))))))
	    (else (apply-additions-to v-new additions))))))

(define (widen-abstract-value-tree-internal v)
 ;; returns: value x (LIST additions-to-value)
 (if (up? v)
     (cons v '())
     (let* ((v-additions (widen-single-abstract-value v))
	    (v-new (car v-additions))
	    (additions (cdr v-additions))
	    (changed? (not (eq? v-new v))))
      (cond ((and (null? additions) (up? v-new))
	     (cons v-new '()))
	    ((null? additions)
	     ;; recursively widen each abstract value below v-new
	     (let outer ((us v-new) (us-new '()))
	      (if (null? us)
		  (let ((us-new (reverse us-new)))
		   (if (every-eq? us-new v) (cons v '()) (cons us-new '())))
		  (let ((u (first us)))
		   (cond ((or (null? u)
			      (boolean? u)
			      (abstract-real? u)
			      (primitive-procedure? u))
			  (outer (rest us) (cons u us-new)))
			 ((branching-value? u)
			  (let inner ((vs (branching-value-values u))
				      (vs-new '()))
			   (if (null? vs)
			       (outer (rest us)
				      (make-branching-value-with-new-values
				       u (reverse vs-new)))
			       (let* ((v-additions
				       (widen-abstract-value-tree-internal
					(first vs)))
				      (v-new (car v-additions))
				      (additions (cdr v-additions)))
				(if (null? additions)
				    (inner (rest vs) (cons v-new vs-new))
				    (let*
				      ((vs1 (append
					     (reverse (cons v-new vs-new))
					     (rest vs)))
				       (u-new
					(make-branching-value-with-new-values
					 u vs1)))
				     ;; I reverse the order of the proto-
				     ;;  abstract values here from the previous
				     ;;  version b/c I don't want to change
				     ;;  the order.  This *could* impact
				     ;;  perfomance.
				     (apply-additions-to
				      (append (reverse (cons u-new us-new))
					      (rest us))
				      additions)))))))
			 (else (fuck-up)))))))
	    (else (apply-additions-to v-new additions))))))

(define (widen-abstract-value-by-coalescing-matching-closures v)
 (if (eq? *l3* #f)
     v
     (let ((result (widen-abstract-value-tree-internal v)))
      (when (not (null? (cdr result))) (panic "additions not made!"))
      (car result))))

;;; \Widen->Closures

;;; Widen->Depth

(define (abstract-value-depth path)
 (cond ((null? path) 0)
       ((and (list? (first path))
	     ;; () makes list? true, so guard against it
	     (not (null? (first path))))
	(+ 1 (abstract-value-depth (rest path))))
       (else (abstract-value-depth (rest path)))))

;;; needs work: This isn't exactly the depth measure I described in writeup.
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
	 (else ; u-or-v is a proto-abstract value...
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
	   (cond ((or (null? u)
		      (boolean? u)
		      (abstract-real? u)
		      (primitive-procedure? u))
		  (if (> (depth (add-to-path u)) k)
		      (add-to-path u)
		      #f))
		 ((branching-value? u)
		  (let inner ((vs (branching-value-values u)))
		   (if (null? vs)
		       (if (> (depth (add-to-path u)) k)
			   (add-to-path u)
			   #f)
		       (let ((result (loop (first vs) (add-to-path u))))
			(if (eq? #f result)
			    (inner (rest vs))
			    result)))))
		 (else (panic "This part not (yet) implemented!")))))))))

;;; to-do: See if this and widen-abstract-value-tree-internal can be made
;;;        special cases of a generalized procedure somehow.
(define (reduce-depth path v-to-add-to v-add)
 ;; path is a list alternating between abstract and proto-abstract values.
 ;; It is assumed to begin with an abstract value at each call of reduce-depth.
 ;; loop returns (LIST v additions)
 (let
   ((result
     (let loop ((path path) (v-context '()))
      (when (null? path) (panic "This should never happen!"))
      (let ((v (first path)))
       (if (eq? v v-add)
	   (let* ((index (positionq v-to-add-to v-context))
		  (addition (make-addition (+ index 1) v-add)))
	    ;; to-do: Does this need process-additions-for-shifting-past-value?
	    (list (make-up index)
		  (shift-additions-up-in-context (list addition)
						 (cons v v-context))))
	   (let* ((v-and-additions
		   (loop (rest (rest path)) (cons v v-context)))
		  (v-new (first v-and-additions))
		  (additions (second v-and-additions))
		  (u (second path))
		  (v-down (third path))
		  (u-new
		   (if (or (nonrecursive-closure? u) (recursive-closure? u))
		       (make-closure-with-new-values
			u (map-vector (lambda (v) (if (eq? v v-down) v-new v))
				      (closure-values u)))
		       (panic "This shouldn't happen!")))
		  (addition (find-if (lambda (a) (= (addition-index a) 0))
				     additions))
		  (additions-rest (removeq addition additions)))
	    (if (eq? v v-to-add-to)
		(let ((v-new (append (replaceq u u-new v)
				     (addition-values addition))))
		 (when (some up? (addition-values addition))
		  (panic "This shouldn't have any ups!"))
		 (list v-new (shift-additions-up-in-context
			      additions-rest (cons v-new v-context))))
		(let ((v-new (replaceq u u-new v)))
		 (list v-new
		       (shift-additions-up-in-context
			additions (cons v-new v-context)))))))))))
  (when (not (null? (second result)))
   (panic "Addition not made!"))
  (first result)))

(define (get-values-to-merge k depth path)
 ;; not quite general: expects v u v u ... order
 (let loop ((i 0) (last-depth -1) (va #f) (vb #f))
  (cond
   ((not (or (eq? va #f) (eq? vb #f))) (list va vb))
   ((> (* 2 i) (length path)) (fuck-up))
   (else
    (let ((d (depth (sublist path 0 (* 2 i)))))
     (cond ((and (= d k) (> d last-depth))
	    (loop (+ i 1) d (list-ref path (* 2 (- i 1))) vb))
	   ((and (= d (+ k 1)) (= last-depth k))
	    (loop (+ i 1) d va (list-ref path (* 2 (- i 1)))))
	   (else (loop (+ i 1) d va vb))))))))

(define (widen-abstract-value-by-limiting-depth v)
 (if (eq? *l5* #f)
     v
     (let loop ((path (path-of-depth-greater-than-k *l5* *depth-measure* v))
		(v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge *l5* *depth-measure* path))
		 (v-new (reduce-depth path (first va-vb) (second va-vb))))
	   (loop (path-of-depth-greater-than-k *l5* *depth-measure* v-new)
		 v-new))))))

;;; \Widen->Depth

;;; Widen->all

;;; \Widen->all

;;; Widen New

(define (make-free-up index up-context)
 (make-up (+ index (length up-context))))

(define (free-up-index up up-context)
 (let ((l (- (up-index up) (length up-context))))
  (if (negative? l) #f l)))

(define (make-list length fill) (map-n (lambda (i) fill) length))

(define (merge-additions2 vss1 vss2)
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
  (cond ((< l1 l2) (merge-additions2 (append vss1 (make-list (- l2 l1) '()))
				     vss2))
	((< l2 l1) (merge-additions2 vss1
				     (append vss2 (make-list (- l1 l2) '()))))
	(else (map append vss1 vss2)))))

(define (create-addition i vs) (append (make-list i '()) (list vs)))

(define (union-for-widening2 v1 v2)
 ;; assumed: v1 and v2 share the same context.  In other words, all
 ;;          free-up-reference-levels which are the same refer to the same
 ;;          values.
 (cond ((and (up? v1) (up? v2))
	(cond ((> (up-index v1) (up-index v2))
	       (list v1 (create-addition (up-index v1) (list v2))))
	      ((< (up-index v1) (up-index v2))
	       (list v2 (create-addition (up-index v2) (list v1))))
	      (else ; (= (up-index v1) (up-index v2))
	       (list v1 '()))))
       ((up? v1) (list v1 (create-addition (up-index v1) (list v2))))
       ((up? v2) (list v2 (create-addition (up-index v2) (list v1))))
       ;; needs work: there can still be duplicate proto-abstract values here;
       ;;             to really remove all (or more) duplicates is much more
       ;;             work, though.
       (else (list (remove-duplicates-circular-safe (append v1 v2)) '()))))

(define (externalize-additions vss)
 (map (lambda (vs) (map externalize-abstract-value vs)) vss))

(define (move-values-up-tree v additions)
 ;; returns (LIST value additions)
 (when (null? additions)
  (panic "Shouldn't we NOT do this if (null? additions)?"))
 (let* ((vs-to-add (first additions))
	(paranoid (when (some up? vs-to-add)
		   (panic "No additions should be UPs...should they?")))
	(v-new (remove-duplicates-circular-safe
		(reduce append
			(cons v (map decrement-free-ups vs-to-add))
			'())))
	(additions-new (move-additions-up v-new (rest additions))))
  (list v-new additions-new)))

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
		      (lambda (v v-context)
		       (and (free-up? v v-context)
			    (= (free-up-index v v-context) 0)))
		      v)))
	       vs))
	     (vs-new
	      (append (map (lambda (v)
			    (if (and (up? v) (= (up-index v) 0))
				v-new
				(process-free-ups
				 (lambda (v v-context)
				  (if (= (free-up-index v v-context) 0)
				      (make-free-up i v-context)
				      (make-up (- (up-index v) 1))))
				 v)))
			   vs)
		      (if add-in-v-new? (list v-new) '()))))
       (loop (list-replace vss i vs-new) (+ i 1))))))

(define (limit-matching-branching-values-at-one-level
	 v k target-branching-value? branching-value-match?
	 pick-us-to-coalesce
	 branching-value-children
	 branching-value-children-matching
	 make-new-branching-value)
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
	  (let inner ((vs1 (branching-value-children u1))
		      (vs2 (branching-value-children-matching u1 u2))
		      (vs '())
		      (additions additions))
;;;		      (additions '()))
	   (if (null? vs1)
	       (let* ((u-new (make-new-branching-value u1 (reverse vs)))
		      (branching-uss-new
		       (cons
			(cons u-new
			      (removeq u2 (removeq u1 (first branching-uss))))
			(rest branching-uss))))
		(outer branching-uss-new us additions #t))
	       (let ((v-additions
		      (union-for-widening2 (first vs1) (first vs2))))
		(inner (rest vs1)
		       (rest vs2)
		       (cons (first v-additions) vs)
		       (merge-additions2 (second v-additions)
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
	    (changed? (not (eq? v-new v))))
      (cond ((and (null? additions) (up? v-new)) (list v-new '()))
	    ((null? additions)
	     ;; recursively widen each abstract value below v-new
	     (let outer ((us v-new) (us-new '()) (additions '()))
	      (if (null? us)
		  (let ((us-new (reverse us-new)))
		   (if (null? additions)
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
		   (cond
		    ((or (null? u)
			 (boolean? u)
			 (abstract-real? u)
			 (primitive-procedure? u))
		     (outer (rest us) (cons u us-new) additions))
		    ((branching-value? u)
		     (let inner ((vs (branching-value-values u))
				 (vs-new '())
				 (additions additions))
		      (if
		       (null? vs)
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
			(inner (rest vs)
			       (cons v-new vs-new)
			       (merge-additions2 additions additions-new))))))
;;;		    ((closure? u)
;;;		     (do-branching-value
;;;		      (vector->list (closure-values u))
;;;		      (lambda (vs) (make-closure-with-new-values
;;;				    u (list->vector vs)))))
;;;		    ((tagged-pair? u)
;;;		     (do-branching-value
;;;		      (tagged-pair-values u)
;;;		      (lambda (vs)
;;;		       (make-tagged-pair-with-new-values u vs))))
		    (else (panic "Not (yet) implemented!")))))))
	    (else
	     (let* ((v-additions (move-values-up-tree v-new additions))
		    (v-new (first v-additions))
		    (additions-new (second v-additions)))
	      (if (null? additions-new)
		  (limit-matching-branching-values-over-tree-internal
		   limit-at-one-level v-new)
		  v-additions)))))))

(define (limit-matching-closures v)
 (if (eq? *l3* #f)
     v
     (let* ((limit-matching-closures-at-one-level
	     (lambda (v)
	      (limit-matching-branching-values-at-one-level
	       v *l3* closure? closure-match?
	       pick-closures-to-coalesce
	       (lambda (u) (vector->list (closure-values u)))
	       (lambda (u1 u2) (vector->list (closure-values-matching u1 u2)))
	       (lambda (u vs)
		(make-closure-with-new-values u (list->vector vs))))))
	    (result (limit-matching-branching-values-over-tree-internal
		     limit-matching-closures-at-one-level v)))
      (when (not (null? (second result)))
       (panic "Some addition wasn't applied!"))
      (first result))))

(define (limit-matching-pairs v)
 (if (eq? *l5* #f)
     v
     (let* ((limit-matching-pairs-at-one-level
	     (lambda (v)
	      (limit-matching-branching-values-at-one-level
	       v *l5* tagged-pair? tagged-pair-match?
	       pick-pairs-to-coalesce
	       tagged-pair-values
	       (lambda (u1 u2) (tagged-pair-values u2))
	       make-tagged-pair-with-new-values)))
	    (result (limit-matching-branching-values-over-tree-internal
		     limit-matching-pairs-at-one-level v)))
      (when (not (null? (second result)))
       (panic "Some addition wasn't applied!"))
      (first result))))

;;; Depth...

(define (reduce-depth2 path v-target v-add)
 ;; path = [] | [v u] ++ path
 (let ((result
	(let loop ((path path) (v-context '()))
	 (when (null? path) (panic "This should never happen!"))
	 (let ((v (first path)))
	  (if (eq? v v-add)
	      (let ((index (positionq v-target v-context)))
	       (list (make-up index) (create-addition index (list v))))
	      (let* ((v-and-additions
		      (loop (rest (rest path)) (cons v v-context)))
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
  (when (not (null? (second result)))
   (panic "Addition(s) not processed in reduce-depth!"))
  (first result)))

(define (pair-depth path)
 (count-if (lambda (u-or-v) (tagged-pair? u-or-v)) path))

(define (limit-l4-depth v)
 (if (eq? *l4* #f)
     v
     (let loop ((path (path-of-depth-greater-than-k *l4* *depth-measure* v))
		(v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge *l4* *depth-measure* path))
		 (v-new (reduce-depth2 path (first va-vb) (second va-vb))))
	   (loop (path-of-depth-greater-than-k *l4* *depth-measure* v-new)
		 v-new))))))

(define (limit-l4-depth2 v)
 (if (eq? *l4* #f)
     ;;(or (eq? *l4* #f)
     ;; (eq? (path-of-depth-greater-than-k *l4* *depth-measure* v) #f))
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
		       (reduce-depth2 path (first va-vb) (second va-vb))))
		(loop (append v-tmp (rest v)) v-new))))))))

(define (limit-l6-depth v)
 (if (eq? *l6* #f)
     v
     (let loop ((path (path-of-depth-greater-than-k *l6* pair-depth v)) (v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge *l6* pair-depth path))
		 (v-new (reduce-depth2 path (first va-vb) (second va-vb))))
	   (loop (path-of-depth-greater-than-k *l6* pair-depth v-new)
		 v-new))))))

(define (aesthetic-reduce-l6-depth v)
 (if (eq? *l6* #f)
     v
     (let outer ((limit (- *l6* 1)) (v-old v))
      (if (<= limit 1)
	  v-old
	  (let ((v-new
		 (let inner ((path (path-of-depth-greater-than-k
				    limit pair-depth v))
			     (v v))
		  (if (eq? path #f)
		      v
		      (let* ((va-vb (get-values-to-merge
				     limit pair-depth path))
			     (v-new (reduce-depth2
				     path (first va-vb) (second va-vb))))
		       (inner (path-of-depth-greater-than-k
			       limit pair-depth v-new)
			      v-new))))))
	   (if (abstract-value=? v-new v-old)
	       (outer (- limit 1) v-new)
	       v-old))))))

(define (syntactic-constraints-met-on-flow? ei bs)
 (let ((l1? (l1-met? bs))
       (vs-met? (map (lambda (b)
		      (and (every-vector
			    syntactic-constraints-met-on-value?
			    (abstract-environment-binding-abstract-values b))
			   (syntactic-constraints-met-on-value?
			    (abstract-environment-binding-abstract-value b))))
		     bs)))
  (when (not (and l1? (every (lambda (x) (eq? x #t)) vs-met?)))
   (format #t "*** I=~s SYNTACTIC CONSTRAINTS NOT MET ON FLOW! ***~%"
	   *num-updates*)
   (format #t "*** ei=~s, l1?=~s~%" ei l1?)
   (for-each-n
    (lambda (i) (format #t "*** met(~s) => ~s~%" i (list-ref vs-met? i)))
    (length vs-met?)))
  (and l1? (every (lambda (x) (eq? x #t)) vs-met?))))

(define (syntactic-constraints-met-on-value? v)
 (let* ((l2? (l2-met? v))
	(l3? (l3-met? v))
	(l4? (l4-met? v))
	(l4-careful? (if *picky?* (l4-met?-careful v) l4?))
	(l5? (l5-met? v))
	(l6? (l6-met? v)))
  (when (and (not l4-careful?) l4?)
   (format #t "*** l4 and l4-careful differ! ***~%"))
  (when (not (and l2? l3? l4? l5? l6? l4-careful?))
   (format #t "*** SYNTACTIC CONSTRAINTS NOT MET! ***~%")
   (format #t "*** (l2?=~s, l3?=~s, l4?=~s, l5?=~s, l6?=~s, l4?-careful=~s~%"
	   l2? l3? l4? l5? l6? l4-careful?))
  (and l2? l3? l4? l5? l6? l4-careful?)))

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

(define (l4-met?-careful v)
 (or (not *l4*)
     (eq? (path-of-depth-greater-than-k *l4* matching-closure-depth-careful v)
	  #f)))

(define (l5-met? v)
 (or (not *l5*)
     (not (some-abstract-value?
	   (lambda (v vs) (if (up? v) #f (> (count-if tagged-pair? v) *l5*)))
	   v))))

(define (l6-met? v)
 (or (not *l6*)
     (eq? (path-of-depth-greater-than-k *l6* pair-depth v) #f)))

(define (widen-abstract-value v)
 (define (syntactic-constraints-met? v)
  (and (l2-met? v)
       (l3-met? v)
       (l4-met? v)
       (or (not *picky?*) (l4-met?-careful v))
       (l5-met? v)
       (l6-met? v)))
 (report-time-for
  'widen #f #f v
  (lambda ()
   (let loop ((v v))
    (if (syntactic-constraints-met? v)
	v
	(loop
	 (let ((limit-l4-depth
		(if *new-l4-depth?* limit-l4-depth2 limit-l4-depth)))
	  (if *new-widen?*
	      (let* ((v1 (remove-duplicate-proto-abstract-values v))
		     (v2a (limit-matching-closures v1))
		     (v3a (limit-matching-pairs v2a))
		     (v4a (limit-l4-depth v3a))
		     (v5a (limit-l6-depth v4a))
		     (v5b (if *aesthetic-reduce-depth?*
			      (aesthetic-reduce-l6-depth v5a)
			      v5a))
		     (v6a (limit-matching-closures v5b))
		     (v7a (limit-matching-pairs v6a))
		     (v8a (remove-duplicate-proto-abstract-values v7a))
		     (v9a (widen-abstract-value-by-coalescing-reals v8a))
		     (v10a (remove-duplicate-proto-abstract-values v9a)))
	       v10a)
	      (let* ((v1 (remove-duplicate-proto-abstract-values v))
		     (v2 (limit-l4-depth v1))
		     (v3 (limit-l6-depth v2))
		     (v3a (if *aesthetic-reduce-depth?*
			      (aesthetic-reduce-l6-depth v3)
			      v3))
		     (v4 (limit-matching-closures v3a))
		     (v5 (limit-matching-pairs v4))
		     (v6 (remove-duplicate-proto-abstract-values v5))
		     (v7 (widen-abstract-value-by-coalescing-reals v6))
		     (v8 (remove-duplicate-proto-abstract-values v7)))
	       v8)))))))))

;;; \Widen New

;;; \Widen

;;; Duplicate removal

(define (remove-duplicate-proto-abstract-values v)
 (process-nodes-in-abstract-value-tree
  (lambda (v v-context) (remove-duplicates-circular-safe v))
  v '()))

;;; \Duplicate removal

;;; Subset?

(define (atomic-proto-abstract-value? u)
 (or (null? u)
     (eq? #t u)
     (eq? #f u)
     (abstract-real? u)
     (primitive-procedure? u)
     (and (closure? u) (zero? (vector-length (closure-values u))))))

(define (atomic-proto-abstract-value-subset? u1 u2)
 (or (eq? u1 u2)
     (and (real? u1) (eq? 'real u2))
     (and (nonrecursive-closure? u1)
	  (nonrecursive-closure? u2)
	  (nonrecursive-closure-match? u1 u2))
     (and (recursive-closure? u1)
	  (recursive-closure? u2)
	  (recursive-closure-match? u1 u2))))

(define (possible-abstract-value-subset? v1 v2)
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
	  (some (lambda (u2)
		 (and (primitive-procedure? u2) (eq? u1 u2)))
		v2))
	 ((branching-value? u1)
	  ;; Do we need to do (and (branching-value? u1) ...) here?
	  ;; branching-value-match? will check for this possiblity
	  (some (lambda (u2) (and (branching-value? u2)
				  (branching-value-match? u1 u2)))
			v2))
;;;	 ((nonrecursive-closure? u1)
;;;	  (some (lambda (u2)
;;;		 (and (nonrecursive-closure? u2)
;;;		      (nonrecursive-closure-match? u1 u2)))
;;;		v2))
;;;	 ((recursive-closure? u1)
;;;	  (some (lambda (u2)
;;;		 (and (recursive-closure? u2)
;;;		      (recursive-closure-match? u1 u2)))
;;;		v2))
;;;	 ;; needs work: do I need to do anything with tags?
;;;	 ((tagged-pair? u1)
;;;	  (some (lambda (u2)
;;;		 (and (tagged-pair? u2)
;;;		      (equal? (tagged-pair-tags u1) (tagged-pair-tags u2))))
;;;		v2))
	 (else (panic (format #f "Not a known proto-abstract value: ~s" u1)))))
  v1))

(define (abstract-value-subset?-cyclic v1 v2)
 (let loop? ((v1 v1) (v2 v2) (cs '()))
  (set! *num-calls-abstract-value-subset-loop?*
	(+ *num-calls-abstract-value-subset-loop?* 1))
  (cond
   ((eq? v1 v2))
   ((null? v1) #t)
   ((null? v2) #f)
   ((some (lambda (c)
	   (and (set-equalp? eq? v1 (car c)) (set-equalp? eq? v2 (cdr c))))
	  cs)
    #t)
   (else
    (let ((cs (cons (cons v1 v2) cs))
	  ;	  (us1-atomic (remove-if-not atomic-proto-abstract-value? v1))
	  ;	  (us1-branching (remove-if atomic-proto-abstract-value? v1))
	  ;	  (us2-atomic (remove-if-not atomic-proto-abstract-value? v2)))
	  (us1-branching (remove-if atomic-proto-abstract-value? v1))
	  (us2-branching (remove-if atomic-proto-abstract-value? v2)))
     (and
      (possible-abstract-value-subset? v1 v2)
      (every
       (if
	*new-subset?*
	(lambda (u1)
	 (cond
	  ((memq u1 v2) #t)
	  ((branching-value? u1)
	   (let* ((vs1 (branching-value-values u1))
		  (k (length vs1))
		  (us2-matching (remove-if-not
				 (lambda (u2) (branching-value-match? u1 u2))
				 us2-branching))
		  (vs2s-matching (map (lambda (u2)
				       (branching-value-values-matching u1 u2))
				      us2-matching)))
	    (let outer ((vs2s vs2s-matching) (results '()))
	     (if (null? vs2s)
		 (if (= k 1)
		     #f
		     (let ((results (reverse results)))
		      (some-n
		       (lambda (i)
			(let ((vs2s-matching-all-but-i
			       (remove-if-not
				(lambda (vs2)
				 (let ((result
					(list-ref
					 results
					 (positionq vs2 vs2s-matching))))
				  (every-n
				   (lambda (j)
				    (if (= i j) #t (list-ref result j)))
				   k)))
				vs2s-matching)))
			 (if (<= (length vs2s-matching-all-but-i) 1)
			     #f
			     (loop? (list-ref vs1 i)
				    (reduce abstract-value-union-cyclic
					    (map
					     (lambda (vs2) (list-ref vs2 i))
					     vs2s-matching-all-but-i)
					    (empty-abstract-value))
				    cs))))
		       k)))
		 (let ((result (map (lambda (v1 v2) (loop? v1 v2 cs))
				    vs1
				    (first vs2s))))
		  (if (every (lambda (b) (eq? b #t)) result)
		      #t
		      (outer (rest vs2s) (cons result results))))))))
	  ((reverse-tagged-value? u1)
	   (panic (string-append "abstract-value-subset? not defined "
				 " (yet) for reverse-tagged-values!")))
	  (else #f)))
	(lambda (u1)
	 (cond
	  ((memq u1 v2) #t)
	  ((branching-value? u1)
	   (let ((vs1 (branching-value-values u1))
		 (us2-matching (remove-if-not
				(lambda (u2) (branching-value-match? u1 u2))
				us2-branching)))
	    (some-n
	     (lambda (i)
	      (let ((us-matching-all-but-u1_i
		     (remove-if-not
		      (lambda (u2)
		       (let ((vs2-matching
			      (branching-value-values-matching u1 u2)))
			(every-n
			 (lambda (j)
			  (if (= i j)
			      #t
			      (loop? (list-ref vs1 j)
				     (list-ref vs2-matching j)
				     cs)))
			 (length vs1))))
		      us2-matching)))
	       (loop? (list-ref vs1 i)
		      (reduce abstract-value-union-cyclic
			      (map (lambda (u)
				    (list-ref
				     (branching-value-values-matching u1 u)
				     i))
				   us-matching-all-but-u1_i)
			      (empty-abstract-value))
		      cs)))
	     (length vs1))))
	  ((reverse-tagged-value? u1)
	   (panic (string-append "abstract-value-subset? not defined "
				 " (yet) for reverse-tagged-values!")))
	  (else #f))))
       us1-branching)))))))

(define (insert-in-subset-times! t v1 v2)
 (define (insert-sorted t v1 v2 ts)
  (cond ((null? ts) (cons (list t v1 v2) '()))
	((<= t (first (first ts))) (cons (list t v1 v2) ts))
	(else (cons (first ts) (insert-sorted t v1 v2 (rest ts))))))
 (let ((result (insert-sorted t v1 v2 *subset-times*)))
  (cond ((= (length result) (+ *num-subset-times* 1))
	 (set! *subset-times* (rest result)))
	((<= (length result) *num-subset-times*)
	 (set! *subset-times* result))
	(else
	 (begin
	  (format #t "HUH=~s~%" result)
	  (panic "How in the hey???"))))))

(define (collect-subset-times! t v1 v2)
 (define (add-time t l1 l2 ts)
  (let* ((index (cons l1 l2))
	 (a (assp equal? index ts)))
   (if (eq? a #f)
       (cons (list index t 1) ts)
       (list-replace
	ts (positionq a ts) (cons (car a) (map + (rest a) (list t 1)))))))
 (set! *subset-category-times*
       (add-time t (length v1) (length v2) *subset-category-times*)))

(define (abstract-value-subset? v1 v2)
 (or (eq? v1 v2)
     (and (possible-abstract-value-subset? v1 v2)
	  (if *new-cyclicize?*
	      (let* ((sanity-check
		      ;; re-enable this check?? ... nah...
		      (when (and #t *debug?* (or (is-cyclic? v1)
						 (is-cyclic? v2)))
		       (panic "v1 or v2 is already cyclic!")))
		     (result (cyclicize-abstract-value2 v1 '() '()))
		     (v1c (first result))
		     (result
		      (cyclicize-abstract-value2 v2 '() (second result)))
		     (v2c (first result)))
	       (abstract-value-subset?-cyclic v1c v2c))
	      (let* ((sanity-check
		      ;; re-enable this check?? ... nah...
		      (when (and #t *debug?* (or (is-cyclic? v1)
						 (is-cyclic? v2)))
		       (panic "v1 or v2 is already cyclic!")))
		     (v1c (cyclicize-abstract-value v1))
		     (v2c (cyclicize-abstract-value v2)))
	       (abstract-value-subset?-cyclic v1c v2c))))))

;;; \Subset?

;;; Union

;;; question: Should this procedure preserve eq?ness if the top-level v has no
;;;           links pointing to it?
(define (unroll-once v vs-above)
 (cond ((and (up? v) (= (up-index v) (- (length vs-above) 1)))
	(let* ((vs-above (cons v vs-above))
	       (make-up-if-needed
		(lambda (v) (if (memq v vs-above)
				(make-up (positionq v vs-above))
				v))))
	 (map (lambda (u)
	       (cond ((or (null? u)
			  (boolean? u)
			  (abstract-real? u)
			  (primitive-procedure? u))
		      u)
		     ((branching-value? u)
		      (make-branching-value-with-new-values
		       u (map make-up-if-needed (branching-value-values u))))
		     (else (panic "Not (yet) implemented!"))))
	      (last vs-above))))
       ((up? v) v)
       (else
	(let* ((vs-above (cons v vs-above))
	       (unroll (lambda (v) (unroll-once v vs-above)))
	       (result
		(map
		 (lambda (u)
		  (cond ((or (null? u)
			     (boolean? u)
			     (abstract-real? u)
			     (primitive-procedure? u))
			 u)
			((branching-value? u)
			 (make-branching-value-with-new-values
			  u (map unroll (branching-value-values u))))
			(else (panic "Not (yet) implemented!"))))
		 v)))
	 (if (every-eq? v result) v result)))))

(define (closed-proto-abstract-values v)
 (unroll-once v '()))

;;; to-do: The way this works sometimes doesn't mesh properly with
;;;          abstract-value-subset?-with-context, i.e. it leads to
;;;          nonterminating subset queries.  I believe that the problem lies
;;;          somewhere in the unrolling process--generating new proto-abstract
;;;          values, but this is *NEEDED* to keep from "capture".
;;;        In addition, how do we really deal with the fact we have two
;;;          (potentially) different contexts?
(define (generic-abstract-value-union-noncyclic v1 v2 v1-context v2-context)
 (cond
  ((null? v1) v2)
  ((null? v2) v1)
  ((eq? v1 v2) v1)
  ((up? v1) (generic-abstract-value-union-noncyclic
	     (list-ref v1-context (up-index v1))
	     v2
	     (rest* v1-context (+ (up-index v1) 1))
	     v2-context))
  ((up? v2) (generic-abstract-value-union-noncyclic
	     v1
	     (list-ref v2-context (up-index v2))
	     v1-context
	     (rest* v2-context (+ (up-index v2) 1))))
  (else (append (unroll-once v1 v1-context) (unroll-once v2 v2-context)))))

(define (abstract-value-union v1 v2)
 (remove-duplicates-circular-safe
  (generic-abstract-value-union-noncyclic v1 v2 '() '())))

;;; to-do: What if either v1 or v2 is (UP k)?
(define (abstract-value-union-without-unroll v1 v2)
 (remove-duplicates-circular-safe (append v1 v2)))

(define (abstract-value-union-cyclic v1 v2)
 (remove-duplicatesq (append v1 v2)))

;;; \Union

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

(define (abstract-environment-union-without-unroll vs1 vs2)
 (map-vector abstract-value-union-without-unroll vs1 vs2))

;;; Abstract-Flow Equivalence and Union

(define (empty-abstract-flow) '())

(define (abstract-flow=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (or
  (eq? bs1 bs2)
  (set-equalp?
   (lambda (b1 b2)
    (and (abstract-environment=?
	  (abstract-environment-binding-abstract-values b1)
	  (abstract-environment-binding-abstract-values b2))
	 (abstract-value=? (abstract-environment-binding-abstract-value b1)
			   (abstract-environment-binding-abstract-value b2))))
   bs1
   bs2)))

(define (abstract-flow-union e bs1 bs2)
 (define (abstract-flow-union bs1 bs2)
  ;; This is one place where imprecision can be introduced.
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
	   (cons (first bs1) (abstract-flow-union (rest bs1) bs2))))))
 (define (abstract-flow-union2 bs1 bs2)
  ;; This is one place where imprecision can be introduced.
  (if (null? bs1)
      bs2
      (let* ((b1 (first bs1))
	     (b2 (find-if
		  (lambda (b2)
		   (abstract-environment=?
		    (abstract-environment-binding-abstract-values b1)
		    (abstract-environment-binding-abstract-values b2)))
		  bs2)))
       (if b2
	   (let* ((v1 (abstract-environment-binding-abstract-value b1))
		  (v2 (abstract-environment-binding-abstract-value b2))
		  (vs2 (abstract-environment-binding-abstract-values b2))
		  (v-new (abstract-value-union v1 v2))
		  (bs2-new (cond ((eq? v-new v2) bs2)
				 ((eq? v-new v1) (replaceq b2 b1 bs2))
				 (else (cons (make-abstract-environment-binding
					      vs2 v-new)
					     (removeq b2 bs2))))))
	    (abstract-flow-union2 (rest bs1) bs2-new))
	   (cons (first bs1) (abstract-flow-union2 (rest bs1) bs2))))))
 (abstract-flow-union bs1 bs2))

;;; Abstract-Analysis Equivalence and Union

(define (empty-abstract-analysis) '())

(define (abstract-analysis=? bs1 bs2)
 ;; Only used for fixpoint convergence check.
 ;; needs work: Can make O(n) instead of O(n^2).
 (when (and #f (some (lambda (b1 b2)
		      (not (eq? (abstract-expression-binding-expression b1)
				(abstract-expression-binding-expression b2))))
		     bs1 bs2))
  (format #t "(")
  (pp (externalize-abstract-analysis bs1)) (newline)
  (pp (externalize-abstract-analysis bs2)) (format #t ")~%")
  (panic "Expressions reordered!"))
 (set-equalp?
  (lambda (b1 b2)
   (and (expression=? (abstract-expression-binding-expression b1)
		      (abstract-expression-binding-expression b2))
	(abstract-flow=? (abstract-expression-binding-abstract-flow b1)
			 (abstract-expression-binding-abstract-flow b2))))
  bs1
  bs2))

(define (abstract-analysis-union bs1 bs2)
 (set! *num-calls-abstract-analysis-union*
       (+ *num-calls-abstract-analysis-union* 1))
 (set! *num-abstract-expression-bindings-in-analysis-unions*
       (+ *num-abstract-expression-bindings-in-analysis-unions*
	  (length bs1) (length bs2)))
 (define (abstract-analysis-union bs1 bs2)
  (if (null? bs1)
      bs2
      (let* ((b1 (first bs1))
	     (e (abstract-expression-binding-expression b1))
	     (b2 (find-if
		  (lambda (b2) (expression=?
				e (abstract-expression-binding-expression b2)))
		  bs2)))
       (if b2
	   (let* ((flow1 (abstract-expression-binding-abstract-flow b1))
		  (flow2 (abstract-expression-binding-abstract-flow b2))
		  (flow-new (abstract-flow-union e flow1 flow2))
		  (bs2-new (cond ((eq? flow-new flow2) bs2)
				 ((eq? flow-new flow1) (replaceq b2 b1 bs2))
				 (else (cons (make-abstract-expression-binding
					      e flow-new)
					     (removeq b2 bs2))))))
	    (abstract-analysis-union (rest bs1) bs2-new))
	   (cons (first bs1) (abstract-analysis-union (rest bs1) bs2))))))
 (abstract-analysis-union bs1 bs2))

;;; Flow Analysis

(define (letrec-expression-recursive-closure-variables e)
 (letrec-recursive-closure-variables
  (letrec-expression-procedure-variables e)
  (letrec-expression-argument-variables e)
  (letrec-expression-bodies e)))

(define (create-flow vs v) (list (make-abstract-environment-binding vs v)))

(define (create-abstract-analysis e vs v)
 (set! *num-calls-create-abstract-analysis*
       (+ *num-calls-create-abstract-analysis* 1))
 (let ((xs (free-variables e)))
  (when (not (= (vector-length vs) (length (free-variables e))))
   (format #t "xs=~s~%" xs)
   (format #t "vs=~s~%" (map-vector externalize-abstract-value vs))
   (panic "create-abstract-analysis: xs and vs should be of same length!")))
 (list (make-abstract-expression-binding e (create-flow vs v))))

(define (restrict-environment vs xs xs-new)
 (list->vector
  (map (lambda (x) (vector-ref vs (position-if (lambda (y) (variable=? x y))
					       xs)))
       xs-new)))

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
	(else (panic "Not a valid expression")))))

(define (vlad-value->abstract-value v)
 (cond ((null? v) (list v))
       ((boolean? v) (list v))
       ((abstract-real? v) (list v))
       ((primitive-procedure? v) (list v))
       ((branching-value? v)
	(list (make-branching-value-with-new-values
	       v (map vlad-value->abstract-value (branching-value-values v)))))
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
	     ((cons-expression? e)
	      (append (empty-analysis-for-expression (cons-expression-car e))
		      (empty-analysis-for-expression (cons-expression-cdr e))))
	     (else (fuck-up)))))

(define (initial-abstract-analysis e bs)
 (if (not *old-initial?*)
     (let ((vs (list->vector
		(map (lambda (x)
		      ;; here I am
		      (vlad-value->abstract-value
		       (value-binding-value
			(find-if
			 (lambda (b) (variable=? x (value-binding-variable b)))
			 bs))))
		     (free-variables e)))))
      (abstract-analysis-rooted-at e vs))
     (abstract-analysis-union
      (if *church-booleans?*
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
	;; Do we even need to create an abstract expression binding for each value
	;; right now?  What if we delay doing so until needed?
	(abstract-analysis-union
	 (abstract-analysis-rooted-at e vs)
	 (rest		 ; rest isn't necessary but saves a LITTLE comp effort
	  (let loop ((e e))
	   (cons (make-abstract-expression-binding e (empty-abstract-flow))
		 (cond ((variable-access-expression? e)
			(empty-abstract-analysis))
		       ((lambda-expression? e)
			(loop (lambda-expression-body e)))
		       ((application? e)
			(append (loop (application-callee e))
				(loop (application-argument e))))
		       ((letrec-expression? e)
			(append (loop (letrec-expression-body e))
				(reduce append
					(map loop (letrec-expression-bodies e))
					(empty-abstract-flow))))
		       ((cons-expression? e)
			(append (loop (cons-expression-car e))
				(loop (cons-expression-cdr e))))
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
			 ((tagged-pair? u) (empty-abstract-analysis))
			 ;; Should never have a bundle here, so let error happen
			 ;; ((bundle? u) (empty-abstract-analysis))
			 (else (format #t "u=~s~%" u) (panic "error3"))))
		  v)
	     (empty-abstract-analysis)))
	   vs))
	 (empty-abstract-analysis)))))))

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
		  (when (not (vector? vs)) (panic "vs not a vector!"))
		  (when (not
			 (vector? (abstract-environment-binding-abstract-values
				   b)))
		   (panic "aeb-abstract-values not a vector!"))
		  (abstract-environment-subset?
		   vs (abstract-environment-binding-abstract-values b)))
		 (if #t
		     (expression-abstract-flow3 e bs)
		     (expression-abstract-flow e bs))))))
      (if (null? bs)
	  (empty-abstract-value)
	  (abstract-environment-binding-abstract-value (first bs))))))

(define (new-nonrecursive-closure vs e)
 (let ((xs (free-variables e))
       (x (lambda-expression-variable e))
       (e (lambda-expression-body e)))
  (list (make-nonrecursive-closure xs vs x e))))

(define (new-recursive-closure xs vs xs-procedures xs-arguments es i)
 (list (make-recursive-closure xs vs xs-procedures xs-arguments es i)))

(define (abstract-apply-nonrecursive-closure p u1 u2)
 (let ((xs (nonrecursive-closure-variables u1)))
  (p (nonrecursive-closure-body u1)
     (list->vector
      (map (lambda (x)
	    (if (variable=? x (nonrecursive-closure-variable u1))
		(list u2)
		(vector-ref (nonrecursive-closure-values u1)
			    (positionq x xs))))
	   (free-variables (nonrecursive-closure-body u1)))))))

(define (abstract-apply-recursive-closure p u1 u2)
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
	       (positionq x xs-procedures)))
	     (else (vector-ref (recursive-closure-values u1)
			       (positionq x xs)))))
	   (free-variables (lambda-expression-body e)))))))

(define (abstract-apply-closure p u1 u2)
 (cond ((nonrecursive-closure? u1)
	(abstract-apply-nonrecursive-closure p u1 u2))
       ((recursive-closure? u1) (abstract-apply-recursive-closure p u1 u2))
       (else (fuck-up))))

(define (abstract-apply v1 v2 bs)
 ;; bs is an analysis.
 (let ((lookup-in-analysis
	(lambda (e vs)
	 (abstract-value-in-matching-abstract-environment e vs bs))))
  (reduce
   abstract-value-union
   (map
    (lambda (u1)
     (if *no-apply-multiply?*
	 (cond ((eq? v2 (empty-abstract-value)) (empty-abstract-value))
	       ((primitive-procedure? u1)
		(reduce abstract-value-union
			(map (lambda (u2)
			      ((primitive-procedure-abstract-procedure u1) u2))
			     (closed-proto-abstract-values v2))
			(empty-abstract-value)))
	       ((closure? u1)
		(abstract-apply-closure2 lookup-in-analysis u1 v2))
	       ;; needs work: The target might not be a procedure. Need to
	       ;;             return concrete bottom in this case.
	       ;;             This calls for a compile-time-warning!
	       (else (empty-abstract-value)))
	 (reduce
	  abstract-value-union
	  (map
	   (lambda (u2)
	    (cond ((primitive-procedure? u1)
		   ((primitive-procedure-abstract-procedure u1) u2))
		  ((closure? u1)
		   (abstract-apply-closure lookup-in-analysis u1 u2))
		  ;; needs work: The target might not be a procedure. Need to
		  ;;             return concrete bottom in this case.
		  ;;             This calls for a compile-time-warning!
		  (else (empty-abstract-value))))
	   (closed-proto-abstract-values v2))
	  (empty-abstract-value))))
    (closed-proto-abstract-values v1))
   (empty-abstract-value))))

;;; tmp

(define (abstract-apply-nonrecursive-closure2 p u1 v2)
 (let ((xs (nonrecursive-closure-variables u1)))
  (p (nonrecursive-closure-body u1)
     (list->vector
      (map (lambda (x)
	    (if (variable=? x (nonrecursive-closure-variable u1))
		v2
		(vector-ref (nonrecursive-closure-values u1)
			    (positionq x xs))))
	   (free-variables (nonrecursive-closure-body u1)))))))

(define (abstract-apply-recursive-closure2 p u1 v2)
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
	       (positionq x xs-procedures)))
	     (else (vector-ref (recursive-closure-values u1)
			       (positionq x xs)))))
	   (free-variables (lambda-expression-body e)))))))

(define (abstract-apply-closure2 p u1 v2)
 (cond ((nonrecursive-closure? u1)
	(abstract-apply-nonrecursive-closure2 p u1 v2))
       ((recursive-closure? u1) (abstract-apply-recursive-closure2 p u1 v2))
       (else (fuck-up))))

(define (abstract-apply-prime v1 v2)
 (if *no-apply-multiply?*
     (reduce
      abstract-analysis-union
      (map
       (lambda (u1)
	(cond ((eq? v2 (empty-abstract-value)) (empty-abstract-analysis))
	      ((primitive-procedure? u1) (empty-abstract-analysis))
	      ((nonrecursive-closure? u1)
	       (abstract-apply-nonrecursive-closure2
		abstract-analysis-rooted-at u1 v2))
	      ((recursive-closure? u1)
	       (abstract-apply-recursive-closure2
		abstract-analysis-rooted-at u1 v2))
	      (else (empty-abstract-analysis))))
       (closed-proto-abstract-values v1))
      (empty-abstract-analysis))
     (reduce
      abstract-analysis-union
      (map
       (lambda (u1)
	(reduce abstract-analysis-union
		(map (lambda (u2)
		      (cond ((primitive-procedure? u1)
			     (empty-abstract-analysis))
			    ((nonrecursive-closure? u1)
			     (abstract-apply-nonrecursive-closure
			      abstract-analysis-rooted-at u1 u2))
			    ((recursive-closure? u1)
			     (abstract-apply-recursive-closure
			      abstract-analysis-rooted-at u1 u2))
			    (else (empty-abstract-analysis))))
		     (closed-proto-abstract-values v2))
		(empty-abstract-analysis)))
       (closed-proto-abstract-values v1))
      (empty-abstract-analysis))))

(define (calculate-all-value-sizes bs)
 (let ((v-size (lambda (v) (second (abstract-value-size v)))))
  (map
   (lambda (b)
    (map (lambda (b)
	  (list (map-vector v-size
			    (abstract-environment-binding-abstract-values b))
		(v-size (abstract-environment-binding-abstract-value b))))
	 (abstract-expression-binding-abstract-flow b)))
   bs)))

(define (mapping-with-vs-in-flow? vs bs)
 (some (lambda (b) (eq? (abstract-environment-binding-abstract-values b) vs))
       bs))

(define (e-type e)
 (cond ((constant-expression? e) 'const)
       ((variable-access-expression? e) 'var)
       ((lambda-expression? e) 'lambda)
       ((application? e) 'app)
       ((letrec-expression? e) 'letrec)
       ((cons-expression? e) 'cons)
       (else (fuck-up))))

(define (report-time-for activity e-index vs-index v-old thunk)
 (let* ((e (if (eq? e-index #f) #f (list-ref *expression-list* e-index)))
	(e-type (if (eq? e #f) #f (e-type e)))
	(time-start (clock-sample))
	(result (thunk))
	(time-end (clock-sample))
	(changed? (not (eq? result v-old)))
	(time (- time-end time-start))
	(i (positionq activity *bucket-names*))
	(num (if (eq? #f i) #f (vector-ref *call-buckets* i))))
  (when (not (eq? #f i))
   (vector-set! *time-buckets* i (+ (vector-ref *time-buckets* i) time))
   (vector-set! *call-buckets* i (+ num 1)))
  (when *report-all-times?*
   (if *machine-style?*
       (format #t "~s ~s ~s ~s ~s ~s ~s ~s~%"
	       *num-updates* activity e-index e-type vs-index
	       changed? num time)
       (format #t "I=~s ~s: e=~s ~s vs=~s changed?=~s num=~s time=~s~%"
	       *num-updates* activity e-index e-type vs-index
	       changed? num time))
   (when (eq? activity 'widen)
    (let ((size-old (abstract-value-size v-old))
	  (size-new (abstract-value-size result)))
     (format #t "I=~s STATS: |v-old|= ~s ~s |v-new|= ~s ~s num=~s~%"
	     *num-updates*
	     (first size-old) (second size-old)
	     (first size-new) (second size-new)
	     num))))
  result))

(define (report-time-for-lite activity thunk)
 (let* ((time-start (clock-sample))
	(result (thunk))
	(time-end (clock-sample))
	(time (- time-end time-start))
	(i (positionq activity *bucket-names*)))
  (when (not (eq? #f i))
   (vector-set! *time-buckets* i (+ (vector-ref *time-buckets* i) time)))
  result))

(define (update-abstract-analysis-ranges bs bs-old)
 ;; bs is the abstract analysis from some iteration i of flow-analysis
 ;; bs-old is the abstract analysis from iteration i-1 of flow-analysis
 (let* ((bs-unchanged?
	 (report-time-for
	  'recalc-unchanged? #f #f #f
	  (lambda ()
	   (map
	    (lambda (b)
	     (let* ((e (abstract-expression-binding-expression b))
		    (bs-e (abstract-expression-binding-abstract-flow b))
		    (bs-old-e (expression-abstract-flow2 e bs-old)))
	      (cons e (and (not (eq? bs-old-e #f))
			   ;; does eq? work well enough?
			   (or (eq? bs-e bs-old-e)
			       (set-equalq? bs-e bs-old-e))))))
	    bs))))
	(bs-unchanged-for-e?
	 (lambda (e)
	  (report-time-for
	   'recalc-unchanged-e? #f #f #f
	   (lambda ()
	    (let ((result (assp expression=? e bs-unchanged?)))
	     (if result (cdr result) #f)))))))
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
		   (vsi (positionq b2 bs-e))
		   (v (abstract-environment-binding-abstract-value b2))
		   (v-new
		    (cond
		     ((variable-access-expression? e) (fuck-up))
		     ((lambda-expression? e) (fuck-up))
		     ((application? e)
		      ;; e: (e1 e2)
		      (let* ((e1 (application-callee e))
			     (e2 (application-argument e))
			     (xs1 (free-variables e1))
			     (xs2 (free-variables e2)))
		       ;; e can be safely left un-updated if:
		       ;;   1. exists vs->v' in (bs-old e)
		       ;;      (basically, vs same as last iter)
		       ;;      - NOTE: we don't say exists vs->v' in (bs e)
		       ;;      - This means that the same environment vs gets
		       ;;        evaluated to form bs as we're trying to
		       ;;        evaluate now.
		       ;;   2. (bs e1) = (bs-old e1)
		       ;;   3. (bs e2) = (bs-old e2)
		       ;;   AND
		       ;;   4. forall u in (bs e1 vs)
		       ;;        u = <sigma,e'> => (bs e') = (bs-old e') AND
		       ;;        u = <sigma,xs,es',i> =>
		       ;;                       (bs es'[i]) = (bs-old es'[i])
		       (if
			(report-time-for
			 'recalc-app? #f #f #f
			 (lambda ()
			  (and
			   *fast-apply?*
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
			     e1 (restrict-environment vs xs xs1) bs)))))
			   v
			   (report-time-for
			    'recalc-app #f #f #f
			    (lambda ()
			     (abstract-apply
			      (abstract-value-in-matching-abstract-environment
			       e1 (restrict-environment vs xs xs1) bs)
			      (abstract-value-in-matching-abstract-environment
			       e2 (restrict-environment vs xs xs2) bs)
			      bs))))))
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
		       ;;      - This means that the same environment vs gets
		       ;;        evaluated to form bs as we're trying to
		       ;;        evaluate now.
		       ;;   2. (bs e-body) = (bs-old e-body)
		       (if (report-time-for
			    'recalc-letrec? #f #f #f
			    (lambda ()
			     (and *fast-letrec?*
				  (mapping-with-vs-in-flow?
				   vs (expression-abstract-flow3 e bs-old))
				  (bs-unchanged-for-e? e-body))))
			   v
			   (report-time-for
			    'recalc-letrec #f #f #f
			    (lambda ()
			     (abstract-value-in-matching-abstract-environment
			      e-body
			      ;; tag 1
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
			      bs))))))
		     ((cons-expression? e)
		      ;; e: (cons e1 e2)
		      ;; e can be safely left un-updated if:
		      ;;   1. exists vs->v' in (bs-old e)--vs same as last
		      ;;                                   iter
		      ;;      - NOTE: we don't say exists vs->v' in (bs e)
		      ;;      - This means that the same environment vs gets
		      ;;        evaluated to form bs as we're trying to
		      ;;        evaluate now.
		      ;;   2. (bs e1) = (bs-old e1)
		      ;;   3. (bs e2) = (bs-old e2)
		      ;; ? - should we multiply out cons?
		      (let* ((e1 (cons-expression-car e))
			     (e2 (cons-expression-cdr e))
			     (xs1 (free-variables e1))
			     (xs2 (free-variables e2)))
		       (if (report-time-for
			    'recalc-cons? #f #f #f
			    (lambda ()
			     (and *fast-cons?*
				  (mapping-with-vs-in-flow?
				   vs (expression-abstract-flow3 e bs-old))
				  (bs-unchanged-for-e? e1)
				  (bs-unchanged-for-e? e2))))
			   v
			   (report-time-for
			    'recalc-cons #f #f #f
			    (lambda ()
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
				    (cons-expression-tags e) v-car v-cdr)))))))))
		     (else (fuck-up)))))
		 (report-time-for
		  'recalc-etc #f #f #f
		  (lambda ()
		   (if *include-prior-values?*
		       (if (or (eq? v-new v) (abstract-value-subset? v-new v))
			   b2
			   (make-abstract-environment-binding
			    vs (abstract-value-union v v-new)))
		       (make-abstract-environment-binding vs v-new))))))
	       bs-e)))
	   (report-time-for
	    'recalc-etc2 #f #f #f
	    (lambda () (if (every-eq? result bs-e) bs-e result))))))))
   bs)))

(define (update-abstract-analysis-domains bs bs-old)
 (let* ((bs-to-add
	 (if *correct-add-cols?*
	     (reduce
	      abstract-analysis-union
	      (map
	       (lambda (b)
		(let* ((e (abstract-expression-binding-expression b))
		       (flow-old (expression-abstract-flow3 e bs-old)))
		 (if (application? e)
		     (reduce
		      abstract-analysis-union
		      (map
		       (lambda (b)
			(let ((vs (abstract-environment-binding-abstract-values
				   b)))
			 (if (mapping-with-vs-in-flow? vs flow-old)
			     '()
			     (abstract-analysis-rooted-at e vs))))
		       (abstract-expression-binding-abstract-flow b))
		      '())
		     '())))
	       bs)
	      '())
	     '()))
	;; This is meant to handle cases whenever a new column occurs for an
	;; application due to widening.
	(bs (abstract-analysis-union bs bs-to-add))
	;; to-do: if *correct-add-cols?*, there are sometimes bindings in bs
	;;        which aren't in the original bs, and these need added to the
	;;        final result.  But how???
	(bs-unchanged?
	 (map (lambda (b)
	       (let* ((e (abstract-expression-binding-expression b))
		      (bs-e (abstract-expression-binding-abstract-flow b))
		      (bs-old-e (expression-abstract-flow2 e bs-old)))
		(cons e (and (not (eq? bs-old-e #f))
			     ;; does eq? work well enough?
			     (or (eq? bs-e bs-old-e)
				 (set-equalq? bs-e bs-old-e))))))
	      bs))
	(bs-unchanged-for-e?
	 (lambda (e) (cdr (assp expression=? e bs-unchanged?)))))
  (abstract-analysis-union
   bs-to-add
   (reduce
    abstract-analysis-union
    (map
     (lambda (b)
      (let* ((e (abstract-expression-binding-expression b))
	     (ei (positionp expression=? e *expression-list*))
	     (xs (free-variables e)))
       (cond ((variable-access-expression? e) (empty-abstract-analysis))
	     ((lambda-expression? e) (empty-abstract-analysis))
	     ((application? e)
	      ;; e: (e1 e2)
	      (let ((e1 (application-callee e))
		    (e2 (application-argument e))
		    (bs-e (abstract-expression-binding-abstract-flow b)))
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
	       (reduce
		abstract-analysis-union
		(map
		 (lambda (b)
		  (let ((vs (abstract-environment-binding-abstract-values b))
			(vsi (positionq b bs-e)))
		   (if (and *fast-apply-prime?*
			    (bs-unchanged-for-e? e1)
			    (bs-unchanged-for-e? e2)
			    (mapping-with-vs-in-flow?
			     vs (expression-abstract-flow3 e bs-old)))
		       (empty-abstract-analysis)
		       (abstract-apply-prime
			(abstract-value-in-matching-abstract-environment
			 e1
			 (restrict-environment vs xs (free-variables e1))
			 bs)
			(abstract-value-in-matching-abstract-environment
			 e2
			 (restrict-environment vs xs (free-variables e2))
			 bs)))))
		 bs-e)
		(empty-abstract-analysis))))
	     ((letrec-expression? e) (empty-abstract-analysis))
	     ((cons-expression? e) (empty-abstract-analysis))
	     (else (fuck-up)))))
     bs)
    (empty-abstract-analysis)))))

(define (update-abstract-analysis bs bs-old)
 ;; The abstract evaluator induces an abstract analysis. This updates the
 ;; abstract values of all of the abstract-environment bindings of all of the
 ;; abstract expression bindings in the abstract analysis. The updated abstract
 ;; value is calculated by abstract evaluation in the abstract environment of
 ;; the abstract-environment binding. Recursive calls to the abstract evaluator
 ;; are replaced with abstract-value-in-matching-abstract-environment.
 (let* ((bs1 (report-time-for
	      'update-ranges #f #f #f
	      (lambda () (update-abstract-analysis-ranges bs bs-old))))
	(bs2 (report-time-for
	      'update-domains #f #f #f
	      (lambda () (update-abstract-analysis-domains bs bs-old))))
	(bs-new-e (remove-if (lambda (b)
			      (memp expression=?
				    (abstract-expression-binding-expression b)
				    *expression-list*))
		   bs2))
	(bs2 (remove-if (lambda (b) (memq b bs-new-e)) bs2))
	(es-new (map abstract-expression-binding-expression bs-new-e)))
  (when (not (null? es-new))
   (set! *expression-list* (append *expression-list* es-new)))
  ;; This whole map expression is acting as a sort of abstract-analysis union--
  ;;   one that enforces monotonicity.
  (append
   (map (lambda (b1)
	 (let* ((e (abstract-expression-binding-expression b1))
		(bs1 (abstract-expression-binding-abstract-flow b1))
		(b2 (lookup-expression-binding e bs2))
		(bs2 (if (eq? b2 #f)
			 '()
			 (abstract-expression-binding-abstract-flow b2)))
		(b-old (lookup-expression-binding e bs))
		(bs-old (if (eq? b-old #f)
			    '()
			    (abstract-expression-binding-abstract-flow b-old)))
		(ei (positionp expression=? e *expression-list*))
		;; abstract environments are unchanged in bs1
		;; abstract environments can only be "added" in bs2
		;;   - those "added" can be either:
		;;     1. truly distinct
		;;     2. repeated copies of an old environment
		;;   - for those fitting #2,
		;;     add-new-abstract-environments-to-abstract-flow
		(bs-new
		 (add-new-abstract-environments-to-abstract-flow ei bs1 bs2))
		(bs-new2
		 (introduce-imprecision-to-abstract-flow ei bs-new bs-old)))
	  (make-abstract-expression-binding e bs-new2)))
	bs1)
   bs-new-e)))

(define (flow-analysis e bs0)
 (set! *num-updates* 0)
 (set! *start-time* (clock-sample))
 (when (not *quiet?*)
  (pp (abstract->concrete e)) (newline))
 (time
  "Total flow analysis time: ~a~%"
  (lambda ()
   (let
     ((result
       (let ((bs0 (initial-abstract-analysis e bs0)))
	(set! *expression-list*
	      (map abstract-expression-binding-expression bs0))
	(when *output-at-iterations?*
	 (write-object-to-file (serialize-expressions *expression-list*)
			       "exps-i0"))
	(let loop ((bs bs0)
		   (bs-old (map (lambda (b)
				 (make-abstract-expression-binding
				  (abstract-expression-binding-expression b)
				  (empty-abstract-flow)))
				bs0)))
	 (when (not *quiet?*)
	  (when (= *num-updates* 0)
	   (let ((num-expressions (length bs))
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
		   bs))
		 (num-cons-expressions
		  (count-if
		   (lambda (b)
		    (cons-expression?
		     (abstract-expression-binding-expression b)))
		   bs)))
	    (pp (externalize-abstract-analysis bs)) (newline)
	    (format #t "Number of expressions: ~s~%" num-expressions)
	    (format #t "  constant expressions: ~s~%"
		    num-constant-expressions)
	    (format #t "  variable-access expressions: ~s~%"
		    num-variable-access-expressions)
	    (format #t "  lambda expressions: ~s~%" num-lambda-expressions)
	    (format #t "  applications: ~s~%" num-applications)
	    (format #t "  letrec expressions: ~s~%" num-letrec-expressions)
	    (format #t "  cons expressions: ~s~%" num-cons-expressions))))
	 (set! *num-updates* (+ *num-updates* 1))
	 (when (not *quiet?*) (format #t "(Iteration ~s:~%" *num-updates*))
	 (let* ((bs-prime
		 (if *quiet?*
		     (if #f
			 (update-abstract-analysis bs bs-old)
			 (report-time-for
			  #f #f #f bs
			  (lambda () (update-abstract-analysis bs bs-old))))
		     (time "update-time:~a~%"
			   (lambda () (update-abstract-analysis bs bs-old)))))
		(total-time (- (clock-sample) *start-time*)))
	  (when (not *quiet?*)
	   (format #t "Total number of iterations: ~s~%" *num-updates*)
	   (format #t "Total time since start: ~a~%"
		   (number->string-of-length-and-precision total-time 16 2)))
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
		    (let* ((e (abstract-expression-binding-expression b))
			   (flow (expression-abstract-flow e bs)))
		     (and flow
			  (abstract-flow=?
			   flow
			   (abstract-expression-binding-abstract-flow b)))))
		   bs-prime))
		 (*only-updated-bindings2?*
		  (remove-if
		   (lambda (b)
		    (let* ((e (abstract-expression-binding-expression b)))
		     (eq? (expression-abstract-flow2 e bs)
			  (abstract-expression-binding-abstract-flow b))))
		   bs-prime))
		 (else bs-prime))))
	   (newline))
	  (let ((done?
		 (if *quiet?*
		     (report-time-for
		      'abstract-analysis=? #f #f #f
		      (lambda () (abstract-analysis=? bs bs-prime)))
		     (time "convergence-check-time:~a~%"
			   (lambda () (abstract-analysis=? bs bs-prime))))))
	   (when (not *quiet?*)
	    (format #t "done?: ~s)~%" done?))
	   (if done?
	       (if *quiet?*
		   bs
		   (begin
		    (format #t "Analysis reached after ~s updates.~%"
			    *num-updates*)
		    bs))
	       (loop bs-prime bs))))))))
;;;    (format #t "*** time-true =  ~s~%*** time-false = ~s ~%"
;;;	    *time-true* *time-false*)
    (if *quiet?*
	(report-bucket-times2)
	(report-bucket-times))
    result))))

;;; needs work: do we need to do more than just this?
(define (compile-time-warning message . us)
 (when *warn?*
  ((if *pp?* pp write) message) (newline)
  (for-each
   (lambda (u)
    ((if *pp?* pp write) (externalize-proto-abstract-value u)) (newline))
   us))
 '())

;;; Abstract basis

;;; \AB{V} -> \AB{V}
(define (abstract-vlad-car-v v tags)
 (reduce abstract-value-union
	 (map (lambda (u) (abstract-vlad-car-u u tags)) v)
;;;	      (closed-proto-abstract-values v))
	 (empty-abstract-value)))

;;; \AB{U} -> \AB{V}
(define (abstract-vlad-car-u u tags)
 (if (vlad-pair? u tags)
     (if *church-pairs?*
	 (cond ((null? tags) (vector-ref (nonrecursive-closure-values u) 0))
	       (else (case (first tags)
		      ((forward)
		       (abstract-bundle-v
			(abstract-vlad-car-v (abstract-primal-u u) (rest tags))
			(abstract-vlad-car-v (abstract-tangent-u u)
					     (rest tags))))
		      ((reverse)
		       (abstract-*j-v
			(abstract-vlad-car-v (abstract-*j-inverse-u u)
					     (rest tags))))
		      (else (fuck-up)))))
	 (tagged-pair-car u))
     (compile-time-warning
      "Attempt to take abstract-vlad-car-u of a non-pair")))

;;; \AB{V} -> \AB{V}
(define (abstract-vlad-cdr-v v tags)
 (reduce abstract-value-union
	 (map (lambda (u) (abstract-vlad-cdr-u u tags)) v)
;;;	      (closed-proto-abstract-values v))
	 (empty-abstract-value)))

;;; \AB{U} -> \AB{V}
(define (abstract-vlad-cdr-u u tags)
 (if (vlad-pair? u tags)
     (if *church-pairs?*
	 (cond ((null? tags) (vector-ref (nonrecursive-closure-values u) 1))
	       (else (case (first tags)
		      ((forward)
		       (abstract-bundle-v
			(abstract-vlad-cdr-v (abstract-primal-u u) (rest tags))
			(abstract-vlad-cdr-v (abstract-tangent-u u)
					     (rest tags))))
		      ((reverse)
		       (abstract-*j-v
			(abstract-vlad-cdr-v (abstract-*j-inverse-u u)
					     (rest tags))))
		      (else (fuck-up)))))
	 (tagged-pair-cdr u))
     (compile-time-warning
      "Attempt to take abstract-vlad-cdr-u of a non-pair")))

;;; \AB{V} x \AB{V} -> \AB{V}
(define (abstract-vlad-cons v1 v2) (list (vlad-cons v1 v2)))

(define (abstract-vlad-pair? v tags) (some (lambda (u) (vlad-pair? u tags)) v))

;;; [\AB{V}]^m x [tag]^n -> \AB{V}
(define (abstract-cons*ify vs tags)
 (if *church-pairs?*
     (if (null? tags)
	 (let loop ((vs vs))
	  (cond ((null? vs) '(()))
		((null? (rest vs)) (first vs))
		(else (abstract-vlad-cons (first vs) (loop (rest vs))))))
	 (case (first tags)
	  ((forward) (abstract-bundle-v
		      (abstract-cons*ify (map abstract-primal-v vs)
					 (rest tags))
		      (abstract-cons*ify (map abstract-tangent-v vs)
					 (rest tags))))
	  ((reverse) (abstract-*j-v
		      (abstract-cons*ify (map abstract-*j-inverse-v vs)
					 (rest tags))))
	  (else (fuck-up))))
     (if (null? vs)
	 (let loop ((tags tags))
	  (if (null? tags)
	      '(())
	      ((case (first tags)
		((forward) abstract-j*-v)
		((reverse) abstract-*j-v)
		(else (fuck-up)))
	       (loop (rest tags)))))
	 (let loop ((vs vs))
	  (if (null? (rest vs))
	      (first vs)
	      (list (make-tagged-pair tags (first vs) (loop (rest vs)))))))))

(define (abstract-base-variables-v v)
 (when (and (list? v) (not (= (length v) 1)))
  (run-time-error "How to handle abstract-base-variables-v for v?: " v))
 (if (not (list? v))
     (compile-time-warning "How can it be that v isn't a list?  v: " v)
     (abstract-base-variables-u (first v))))

;;; \AB{U} -> [variable]
(define (abstract-base-variables-u u)
 (cond
  ((primitive-procedure? u) '())
  ((nonrecursive-closure? u)
   (let ((xs (nonrecursive-closure-variables u)))
    (if (null? (nonrecursive-closure-tags u))
	xs
	(case (first (nonrecursive-closure-tags u))
	 ((forward) (forward-uptag-variables
		     (abstract-base-variables-v (abstract-primal-u u)) xs))
	 ((reverse) (reverse-uptag-variables
		     (abstract-base-variables-v (abstract-*j-inverse-u u)) xs))
	 (else (fuck-up))))))
  ((recursive-closure? u)
   (let ((xs (recursive-closure-variables u)))
    (if (null? (recursive-closure-tags u))
	xs
	(case (first (recursive-closure-tags u))
	 ((forward) (forward-uptag-variables
		     (abstract-base-variables-v (abstract-primal-u u)) xs))
	 ((reverse) (reverse-uptag-variables
		     (abstract-base-variables-v (abstract-*j-inverse-u u)) xs))
	 (else (fuck-up))))))
  (else (fuck-up))))

(define (abstract-base-values-u u)
 (let ((xs1 (abstract-base-variables-u u))
       (xs2 (cond
	     ((nonrecursive-closure? u) (nonrecursive-closure-variables u))
	     ((recursive-closure? u) (recursive-closure-variables u))
	     (else (fuck-up))))
       (vs2 (cond ((nonrecursive-closure? u) (nonrecursive-closure-values u))
		  ((recursive-closure? u) (recursive-closure-values u))
		  (else (fuck-up)))))
  (map (lambda (x1) (vector-ref vs2 (positionp variable=? x1 xs2))) xs1)))

(define (abstract-real? u) (or (real? u) (eq? u 'real)))

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
	(abstract-cons*ify (map abstract-zero-v (abstract-base-values-u u))
			   (closure-tags u)))
       ((bundle? u) (list (make-bundle (abstract-zero-v (bundle-primal u))
				       (abstract-zero-v (bundle-tangent u)))))
       ((reverse-tagged-value? u)
	(list (make-reverse-tagged-value
	       (abstract-zero-v (reverse-tagged-value-primal u)))))
       ((and (not *church-pairs?*) (tagged-pair? u))
	(list (make-tagged-pair (tagged-pair-tags u)
				(abstract-zero-v (abstract-vlad-car-u
						  u (tagged-pair-tags u)))
				(abstract-zero-v (abstract-vlad-cdr-u
						  u (tagged-pair-tags u))))))
       (else (fuck-up))))

(define (abstract-plus u) (panic "abstract-plus not implemented!"))

(define (abstract-primal-v v-forward)
 (if (up? v-forward)
     v-forward
     (reduce abstract-value-union-without-unroll
	     (map abstract-primal-u v-forward)
	     (empty-abstract-value))))

(define (abstract-primal-u u-forward)
 (let* ((result
	 (cond
	  ((null? u-forward)
	   (compile-time-warning
	    "Attempt to take primal of a non-forward value" u-forward))
	  ((and (not *church-booleans?*) (vlad-boolean? u-forward))
	   (compile-time-warning
	    "Attempt to take primal of a non-forward value" u-forward))
	  ((abstract-real? u-forward)
	   (compile-time-warning
	    "Attempt to take primal of a non-forward value" u-forward))
	  ((primitive-procedure? u-forward)
	   (compile-time-warning
	    "Attempt to take primal of a non-forward value" u-forward))
	  ((nonrecursive-closure? u-forward)
	   (unless (and
		    (not (null? (nonrecursive-closure-tags u-forward)))
		    (eq? (first (nonrecursive-closure-tags u-forward))
			 'forward))
	    (compile-time-warning
	     "Attempt to take primal of a non-forward value" u-forward))
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
			(index x xs (lambda-expression-body e))))))))
	  ((recursive-closure? u-forward)
	   (unless (and (not (null? (recursive-closure-tags u-forward)))
			(eq? (first (recursive-closure-tags u-forward))
			     'forward))
	    (compile-time-warning
	     "Attempt to take primal of a non-forward value" u-forward))
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
			     (recursive-closure-argument-variables
			      u-forward)
			     (recursive-closure-bodies u-forward))))
		       (xs1 (map-vector
			     unforwardify
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
			(recursive-closure-index u-forward)))))))
	  ((bundle? u-forward) (bundle-primal u-forward))
	  ((reverse-tagged-value? u-forward)
	   (compile-time-warning
	    "Attempt to take primal of a non-forward value" u-forward))
	  ((and (not *church-pairs?*) (tagged-pair? u-forward))
	   (unless (and
		    (not (null? (tagged-pair-tags u-forward)))
		    (eq? (first (tagged-pair-tags u-forward)) 'forward))
	    (compile-time-warning
	     "Attempt to take primal of a non-forward value" u-forward))
	   (list (make-tagged-pair
		  (rest (tagged-pair-tags u-forward))
		  (abstract-primal-v (tagged-pair-car u-forward))
		  (abstract-primal-v (tagged-pair-cdr u-forward)))))
	  (else (fuck-up)))))
  result))

(define (abstract-tangent-v v)
 (if (up? v)
     v
     (reduce abstract-value-union-without-unroll
	     (map abstract-tangent-u v)
	     (empty-abstract-value))))

(define (abstract-tangent-u u-forward)
 (let* ((result
	 (cond
	  ((null? u-forward)
	   (compile-time-warning
	    "Attempt to take tangent of a non-forward value" u-forward))
	  ((and (not *church-booleans?*) (vlad-boolean? u-forward))
	   (compile-time-warning
	    "Attempt to take tangent of a non-forward value" u-forward))
	  ((abstract-real? u-forward)
	   (compile-time-warning
	    "Attempt to take tangent of a non-forward value" u-forward))
	  ((primitive-procedure? u-forward)
	   (compile-time-warning
	    "Attempt to take tangent of a non-forward value" u-forward))
	  ((nonrecursive-closure? u-forward)
	   (unless (and (not (null? (nonrecursive-closure-tags u-forward)))
			(eq? (first (nonrecursive-closure-tags u-forward))
			     'forward))
	    (compile-time-warning
	     "Attempt to take tangent of a non-forward value" u-forward))
	   (if (some (lambda (b)
		      (abstract-value=? (list u-forward)
					(vlad-value->abstract-value
					 (primitive-procedure-forward
					  (value-binding-value b)))))
		     *value-bindings*)
	       '()
	       (abstract-cons*ify
		(map abstract-tangent-v (abstract-base-values-u u-forward))
		(rest (nonrecursive-closure-tags u-forward)))))
	  ((recursive-closure? u-forward)
	   (unless (and (not (null? (recursive-closure-tags u-forward)))
			(eq? (first (recursive-closure-tags u-forward))
			     'forward))
	    (compile-time-warning
	     "Attempt to take tangent of a non-forward value" u-forward))
	   (if (some (lambda (b)
		      (abstract-value=? (list u-forward)
					(vlad-value->abstract-value
					 (primitive-procedure-forward
					  (value-binding-value b)))))
		     *value-bindings*)
	       '()
	       (abstract-cons*ify
		(map abstract-tangent-v (abstract-base-values-u u-forward))
		(rest (recursive-closure-tags u-forward)))))
	  ((bundle? u-forward) (bundle-tangent u-forward))
	  ((reverse-tagged-value? u-forward)
	   (compile-time-warning
	    "Attempt to take tangent of a non-forward value" u-forward))
	  ((and (not *church-pairs?*) (tagged-pair? u-forward))
	   (unless (and (not (null? (tagged-pair-tags u-forward)))
			(eq? (first (tagged-pair-tags u-forward)) 'forward))
	    (compile-time-warning
	     "Attempt to take tangent of a non-forward value" u-forward))
	   (list (make-tagged-pair
		  (rest (tagged-pair-tags u-forward))
		  (abstract-tangent-v (tagged-pair-car u-forward))
		  (abstract-tangent-v (tagged-pair-cdr u-forward)))))
	  (else (fuck-up))))
	(forward-cache-entry
	 (find-if (lambda (forward-cache-entry)
		   (vlad-equal?
		    (forward-cache-entry-forward forward-cache-entry)
		    u-forward))
		  *forward-cache*)))
  result))

;;; \AB{V} x \AB{V} -> \AB{V}
(define (abstract-bundle-v v v-perturbation)
 (abstract-bundle-v-internal v v-perturbation '()))
			    
(define (abstract-bundle-v-internal v v-perturbation cs)
 (cond ((and (up? v) (up? v-perturbation)
	     (= (up-index v) (up-index v-perturbation)))
	v)
       ((up? v) (abstract-bundle-v-internal
		 (car (list-ref cs (up-index v))) v-perturbation cs))
       ((up? v-perturbation)
	(abstract-bundle-v-internal
	 v (cdr (list-ref cs (up-index v-perturbation))) cs))
       (else (let ((i (position-if
		       (lambda (c) (and (eq? (car c) v)
					(eq? (cdr c) v-perturbation)))
		       cs))
		   (cs-new (cons (cons v v-perturbation) cs)))
	      (if (not (eq? i #f))
		  (make-up i)
		  (reduce
		   abstract-value-union-without-unroll
		   (map
		    (lambda (u)
		     (reduce
		      abstract-value-union-without-unroll
		      (map
		       (lambda (u-perturbation)
			(abstract-bundle-u-internal u u-perturbation cs-new))
		       v-perturbation)
		      (empty-abstract-value)))
		    v)
		   (empty-abstract-value)))))))

;;; \AB{U} x \AB{U} -> \AB{V}
(define (abstract-bundle-u u u-perturbation)
 (abstract-bundle-u-internal u u-perturbation '()))

(define (abstract-bundle-u-internal u u-perturbation cs)
 ;; Does tagged-null? need any modifications to handle backlinks???
 (define (tagged-null?-v tags v) (some (lambda (u) (tagged-null?-u tags u)) v))
 (define (tagged-null?-u tags u)
  (if (null? tags)
      (null? u)
      (case (first tags)
       ((forward) (and (bundle? u)
		       (tagged-null?-v (rest tags) (bundle-primal u))
		       (tagged-null?-v (rest tags) (bundle-tangent u))))
       ((reverse)
	(and (reverse-tagged-value? u)
	     (tagged-null?-v (rest tags) (reverse-tagged-value-primal u))))
       (else (fuck-up)))))
 (define (legitimate*? vs v-perturbations tags cs)
  ;; VS is a list, V-PERTURBATIONS is an abstract tuple.
  (or (and (null? vs) (tagged-null?-v tags v-perturbations))
      (and (not (null? vs))
	   (null? (rest vs))
	   (legitimate?-v (first vs) v-perturbations cs))
      (and (not (null? vs))
	   (not (null? (rest vs)))
	   (abstract-vlad-pair? v-perturbations tags)
	   (legitimate?-v
	    (first vs) (abstract-vlad-car-v v-perturbations tags) cs)
	   (legitimate*?
	    (rest vs) (abstract-vlad-cdr-v v-perturbations tags) tags cs))))
 (define (legitimate?-v v v-perturbation cs)
  (cond ((and (up? v) (up? v-perturbation)
	      (= (up-index v) (up-index v-perturbation)))
	 #t)
	((up? v)
	 (legitimate?-v (car (list-ref cs (up-index v))) v-perturbation cs))
	((up? v-perturbation)
	 (legitimate?-v v (cdr (list-ref cs (up-index v-perturbation))) cs))
	(else
	 (let ((i (position-if (lambda (c) (and (eq? (car c) v)
						(eq? (cdr c) v-perturbation)))
			       cs))
	       (cs-new (cons (cons v v-perturbation) cs)))
	  (or (not (eq? i #f))
	      (some (lambda (u) (some (lambda (u-perturbation)
				       (legitimate?-u u u-perturbation cs-new))
				      v-perturbation))
		    v))))))
 (define (legitimate?-u u u-perturbation cs)
  (or (and (null? u) (null? u-perturbation))
      (and (not *church-booleans?*) (vlad-boolean? u) (null? u-perturbation))
      (and (abstract-real? u) (abstract-real? u-perturbation))
      (and (primitive-procedure? u) (null? u-perturbation))
      (and (nonrecursive-closure? u)
	   (legitimate*? (abstract-base-values-u u)
			 (list u-perturbation)
			 (nonrecursive-closure-tags u)
			 cs))
      (and (recursive-closure? u)
	   (legitimate*? (abstract-base-values-u u)
			 (list u-perturbation)
			 (recursive-closure-tags u)
			 cs))
      (and (bundle? u)
	   (bundle? u-perturbation)
	   (legitimate?-v (bundle-primal u) (bundle-primal u-perturbation) cs)
	   (legitimate?-v
	    (bundle-tangent u) (bundle-tangent u-perturbation) cs))
      (and (reverse-tagged-value? u)
	   (reverse-tagged-value? u-perturbation)
	   (legitimate?-v (reverse-tagged-value-primal u)
			  (reverse-tagged-value-primal u-perturbation)
			  cs))
      (and (not *church-pairs?*)
	   (tagged-pair? u)
	   (tagged-pair? u-perturbation)
	   (equal? (tagged-pair-tags u) (tagged-pair-tags u-perturbation))
	   (legitimate?-v
	    (tagged-pair-car u) (tagged-pair-car u-perturbation) cs)
	   (legitimate?-v
	    (tagged-pair-cdr u) (tagged-pair-cdr u-perturbation) cs))))
 (define (bundle* vs v-perturbations tags)
  ;; VS is a list of abstract values,
  ;; V-PERTURBATIONS is an abstract vlad tuple of abstract values,
  ;; the result is a list of abstract values.
  (cond
   ((null? vs) '())
   ((null? (rest vs)) (list (bundle-v (first vs) v-perturbations)))
   (else (cons (bundle-v (first vs) (abstract-vlad-car-v v-perturbations tags))
	       (bundle* (rest vs)
			(abstract-vlad-cdr-v v-perturbations tags)
			tags)))))
 ;; \AB{V} x \AB{V} -> \AB{V}
 (define (bundle-v v v-perturbation)
  (abstract-bundle-v-internal v v-perturbation cs))
 ;; \AB{U} x \AB{U} -> \AB{V}
 (cond
  ((not (legitimate?-u u u-perturbation cs))
   (compile-time-warning "Mismatch!" u u-perturbation))
  ((null? u) (list (make-bundle (list u) (list u-perturbation))))
  ((and (not *church-booleans?*) (vlad-boolean? u))
   (list (make-bundle (list u) (list u-perturbation))))
  ((abstract-real? u) (list (make-bundle (list u) (list u-perturbation))))
  ((primitive-procedure? u)
   (unless (null? u-perturbation) (fuck-up))
   (vlad-value->abstract-value (primitive-procedure-forward u)))
  ((nonrecursive-closure? u)
   (let* ((e (forward-transform
	      (new-lambda-expression (nonrecursive-closure-variable u)
				     (nonrecursive-closure-body u))))
	  (x (lambda-expression-variable e))
	  (xs (free-variables e)))
    (list (make-nonrecursive-closure
	   xs
	   ;; This should use a generalized add/remove-slots here.
	   (list->vector
	    ;; Is there any case where abstract-base-variables-u would need
	    ;; to keep track of cs (in case of backlinks)???
	    (let ((xs (abstract-base-variables-u u))
		  ;; needs work: change bundle*
		  (vs (bundle* (abstract-base-values-u u)
			       (list u-perturbation)
			       (nonrecursive-closure-tags u))))
	     (map (lambda (x v)
		   (let ((i (positionp variable=? x xs)))
		    (if i (list-ref vs i) (abstract-j*-v v))))
		  (nonrecursive-closure-variables u)
		  (vector->list (nonrecursive-closure-values u)))))
	   x
	   (index x xs (lambda-expression-body e))))))
  ((recursive-closure? u)
   (let* ((es (vector->list
	       (map-vector (lambda (x e)
			    (forward-transform (new-lambda-expression x e)))
			   (recursive-closure-argument-variables u)
			   (recursive-closure-bodies u))))
	  (xs1 (map-vector forwardify
			   (recursive-closure-procedure-variables u)))
	  (xs (letrec-recursive-closure-variables
	       (vector->list xs1)
	       (map lambda-expression-variable es)
	       (map lambda-expression-body es))))
    (list (make-recursive-closure
	   xs
	   ;; This should use a generalized add/remove-slots here.
	   (list->vector
	    (let ((xs (abstract-base-variables-u u))
		  (vs (bundle* (abstract-base-values-u u)
			       (list u-perturbation)
			       (recursive-closure-tags x))))
	     (map (lambda (x v)
		   (let ((i (positionp variable=? x xs)))
		    (if i (list-ref vs i) (abstract-j*-v v))))
		  (recursive-closure-variables x)
		  (vector->list (recursive-closure-values x)))))
	   xs1
	   (list->vector (map lambda-expression-variable es))
	   (list->vector (map (lambda (e)
			       (index (lambda-expression-variable e)
				      (append (vector->list xs1) xs)
				      (lambda-expression-body e)))
			      es))
	   (recursive-closure-index u)))))
  ((bundle? u) (list (make-bundle (list u) (list u-perturbation))))
  ((reverse-tagged-value? u)
   (list (make-bundle (list u) (list u-perturbation))))
  ((and (not *church-pairs?*) (tagged-pair? u))
   (list (make-tagged-pair
	  (cons 'forward (tagged-pair-tags u))
	  (bundle-v (tagged-pair-car u) (tagged-pair-car u-perturbation))
	  (bundle-v (tagged-pair-cdr u) (tagged-pair-cdr u-perturbation)))))
  (else (fuck-up))))

;;; \AB{V} -> \AB{V}
(define (abstract-j*-v v)
 (abstract-bundle-v v (abstract-zero-v v)))

;;; \AB{U} -> \AB{V}
(define (abstract-j*-u u)
 (abstract-bundle-v (list u) (abstract-zero-u u)))

(define (abstract-*j-v v) (panic "abstract-*j-v not implemented!"))

(define (abstract-*j-u u) (panic "abstract-*j-u not implemented!"))

(define (abstract-*j-inverse-v v)
 (panic "abstract-*j-inverse-v not implemented!"))

(define (abstract-*j-inverse-u u)
 (panic "abstract-*j-inverse-v not implemented!"))

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
    (let ((v1 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	  (v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
     (reduce abstract-value-union
	     (map (lambda (u1)
		   (reduce abstract-value-union
			   (map (lambda (u2) (list (f u1 u2))) v2)
			   (empty-abstract-value)))
		  v1)
	     (empty-abstract-value))))
   (else (compile-time-warning (format #f "Argument to ~a is not a pair" s) u)
	 '()))))

(define (abstract-binary-u->v f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v1 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	  (v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
     (reduce abstract-value-union
	     (map (lambda (u1)
		   (reduce abstract-value-union
			   (map (lambda (u2) (f u1 u2)) v2)
			   (empty-abstract-value)))
		  v1)
	     (empty-abstract-value))))
   (else (compile-time-warning (format #f "Argument to ~a is not a pair" s) u)
	 '()))))

(define (abstract-binary-real f s)
 (lambda (u)
  (cond
   ((vlad-pair? u '())
    (let ((v1 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	  (v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
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
    (let ((v1 (closed-proto-abstract-values (abstract-vlad-car-u u '())))
	  (v2 (closed-proto-abstract-values (abstract-vlad-cdr-u u '()))))
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
	 (let ((v1 (closed-proto-abstract-values
		    (abstract-vlad-car-u u123 '())))
	       (v23 (closed-proto-abstract-values
		     (abstract-vlad-cdr-u u123 '()))))
	  (reduce
	   abstract-value-union
	   (map
	    (lambda (u1)
	     (reduce
	      abstract-value-union
	      (map
	       (lambda (u23)
		(cond ((vlad-pair? u23 '())
		       (let ((v2 (closed-proto-abstract-values
				  (abstract-vlad-car-u u23 '())))
			     (v3 (closed-proto-abstract-values
				  (abstract-vlad-cdr-u u23 '()))))
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
			(format #f "Argument to ~a might not be a triple" s)
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
 (cond ((and (or (not *unabbreviate-transformed?*)
		 (and (not *church-pairs?*) (tagged-pair? u)))
	     (vlad-forward? u))
	(if *unabbreviate-executably?*
	    (list 'bundle
		  (externalize-abstract-value (abstract-primal-u u))
		  (externalize-abstract-value (abstract-tangent-u u)))
	    (list 'forward
		  (externalize-abstract-value (abstract-primal-u u))
		  (externalize-abstract-value (abstract-tangent-u u)))))
       ((vlad-true? u) #t)
       ((vlad-false? u) #f)
       ((abstract-real? u) u)
       ;; needs work: How to properly distinguish between abstract lists/tuples
       ;; v = (cons v1 v2)
       ((vlad-pair? u '())
	(let ((v1 (abstract-vlad-car-u u '()))
	      (v2 (abstract-vlad-cdr-u u '())))
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
       ((bundle? u)
	(let ((primal (bundle-primal u))
	      (tangent (bundle-tangent u)))
	 (if *unabbreviate-executably?*
	     (list 'bundle
		   (externalize-abstract-value primal)
		   (externalize-abstract-value tangent))
	     (list 'forward
		   (externalize-abstract-value primal)
		   (externalize-abstract-value tangent)))))
       ((list? u)
	(run-time-error (format #f "Not a proto-abstract-value: ~a" u)))
       (else (externalize u))))

(define (externalize-abstract-value v)
 (when (not (or (list? v) (up? v)))
  (panic "Not an abstract value!"))
 (let ((v (if (is-cyclic? v) (uncyclicize-abstract-value v) v)))
  (cond ((up? v) v)
	((list? v)
	 (cond ((null? v) (list->vector v))
	       ((= (length v) 1) (externalize-proto-abstract-value (first v)))
	       (else (make-union (map externalize-proto-abstract-value v)))))
	(else (panic (format #f "Not an abstract value: ~s" v))))))

(define (externalize-abstract-environment xs vs)
 (when (not (and (vector? vs)
		 (every-vector (lambda (v) (or (list? v) (up? v))) vs)))
  (panic "Not an abstract environment!"))
 ;; debugging
 (when (not (= (length xs) (vector-length vs)))
  (format #t "xs=~s~%" xs)
  (format #t "vs=~s~%" (map-vector externalize-abstract-value vs))
  (panic "xs and vs should be of same length!"))
 (map (lambda (x v) (list x (externalize-abstract-value v)))
      xs (vector->list vs)))

(define (externalize-abstract-environment-binding xs b)
 (when (not (abstract-environment-binding? b))
  (panic "Not an abstract-environment-binding!"))
 (list (externalize-abstract-environment
	xs (abstract-environment-binding-abstract-values b))
       (externalize-abstract-value
	(abstract-environment-binding-abstract-value b))))

(define (externalize-abstract-flow xs bs)
 (when (not (and (list? bs)
		 (every (lambda (b) (abstract-environment-binding? b)) bs)))
  (panic "Not an abstract flow!"))
 (map (lambda (b) (externalize-abstract-environment-binding xs b)) bs))

(define (externalize-abstract-expression-binding b)
 (when (not (abstract-expression-binding? b))
  (panic "Not an abstract expression binding!"))
 (list (abstract->concrete (abstract-expression-binding-expression b))
       (externalize-abstract-flow
	(free-variables (abstract-expression-binding-expression b))
	(abstract-expression-binding-abstract-flow b))))

(define (externalize-abstract-analysis bs)
 (when (not (and (list? bs)
		 (every (lambda (b) (abstract-expression-binding? b)) bs)))
  (panic "Not an abstract analysis!"))
 (map externalize-abstract-expression-binding bs))

(define (externalize-addition a)
 (make-addition (addition-index a)
		(map externalize-abstract-value (addition-values a))))

(define (externalize-addition-u a)
 (make-addition (addition-index a)
		(map externalize-proto-abstract-value (addition-values a))))

(define (shorten-expression e es)
 (let ((lookup (lambda (e) (positionp expression-eqv? e es))))
  (cond ((constant-expression? e)
	 (list 'const (lookup e) (constant-expression-value e)))
	((variable-access-expression? e)
	 (list 'var (lookup e) (variable-access-expression-variable e)))
	((lambda-expression? e)
	 (list 'lambda (lookup e) (lambda-expression-variable e)
	       (lookup (lambda-expression-body e))))
	((application? e)
	 (list 'app (lookup e)
	       (map lookup
		    `(,(application-callee e) ,(application-argument e)))))
	((letrec-expression? e)
	 (list 'letrec (lookup e)
	       (map (lambda (f x e) (list f x (lookup e)))
		    (letrec-expression-procedure-variables e)
		    (letrec-expression-argument-variables e)
		    (letrec-expression-bodies e))
	       (lookup (letrec-expression-body e))))
	((cons-expression? e)
	 (list 'cons (lookup e)
	       (map lookup
		    `(,(cons-expression-car e) ,(cons-expression-cdr e)))))
	(else (fuck-up)))))

(define (map-threaded f l tx)
 (let loop ((l l) (l-new '()) (tx tx))
  (if (null? l)
      (cons (reverse l-new) tx)
      (let ((x-tx (f (first l) tx)))
       (loop (rest l) (cons (car x-tx) l) (cdr x-tx))))))

(define (map-vector-threaded f v tx)
 (let ((l-tx (map-threaded f (vector->list v) tx)))
  (cons (list->vector (car l-tx)) (cdr l-tx))))

(define (serialize-expressions es)
 (define (lookup e) (positionq e es))
 (map
  (lambda (e)
   (cond ((constant-expression? e) e)
	 ((variable-access-expression? e) e)
	 ((lambda-expression? e)
	  (make-lambda-expression
	   (lambda-expression-free-variables e)
	   (lambda-expression-free-variable-indices e)
	   (lambda-expression-variable e)
	   (lookup (lambda-expression-body e))))
	 ((application? e)
	  (make-application (lookup (application-callee e))
			    (lookup (application-argument e))
			    (application-free-variables e)))
	 ((letrec-expression? e)
	  (make-letrec-expression
	   (letrec-expression-bodies-free-variables e)
	   (letrec-expression-bodies-free-variable-indices e)
	   (letrec-expression-body-free-variables e)
	   (letrec-expression-body-free-variable-indices e)
	   (letrec-expression-procedure-variables e)
	   (letrec-expression-argument-variables e)
	   (map lookup (letrec-expression-bodies e))
	   (lookup (letrec-expression-body e))))
	 ((cons-expression? e)
	  (make-cons-expression (cons-expression-tags e)
				(lookup (cons-expression-car e))
				(lookup (cons-expression-cdr e))))
	 (else (fuck-up))))
  es))

(define (copy-expression e)
 (define (copy-list l) (map identity l))
 (define (copy-vector v) (if (eq? v #f) #f (map-vector identity v)))
 (cond ((integer? e) e)
       ((constant-expression? e)
	(make-constant-expression (constant-expression-value e)))
       ((variable-access-expression? e)
	(make-variable-access-expression
	 (variable-access-expression-variable e)
	 (variable-access-expression-index e)))
       ((lambda-expression? e)
	(make-lambda-expression
	 (copy-list (lambda-expression-free-variables e))
	 (copy-vector (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (copy-expression (lambda-expression-body e))))
       ((application? e)
	(make-application (copy-expression (application-callee e))
			  (copy-expression (application-argument e))
			  (copy-list (application-free-variables e))))
       ((letrec-expression? e)
	(make-letrec-expression
	 (copy-list (letrec-expression-bodies-free-variables e))
	 (copy-vector (letrec-expression-bodies-free-variable-indices e))
	 (copy-list (letrec-expression-body-free-variables e))
	 (copy-vector (letrec-expression-body-free-variable-indices e))
	 (copy-list (letrec-expression-procedure-variables e))
	 (copy-list (letrec-expression-argument-variables e))
	 (map copy-expression (letrec-expression-bodies e))
	 (copy-expression (letrec-expression-body e))))
       ((cons-expression? e)
	(make-cons-expression (copy-list (cons-expression-tags e))
			      (copy-expression (cons-expression-car e))
			      (copy-expression (cons-expression-cdr e))))
       (else (fuck-up))))

(define (unserialize-expressions es)
 (let ((es (map copy-expression es)))
  (define (lookup i) (list-ref es i))
  (for-each
   (lambda (e)
    (cond ((constant-expression? e) #f)
	  ((variable-access-expression? e) #f)
	  ((lambda-expression? e)
	   (set-lambda-expression-body! e (lookup (lambda-expression-body e))))
	  ((application? e)
	   (set-application-callee! e (lookup (application-callee e)))
	   (set-application-argument! e (lookup (application-argument e))))
	  ((letrec-expression? e)
	   (set-letrec-expression-bodies!
	    e (map lookup (letrec-expression-bodies e)))
	   (set-letrec-expression-body!
	    e (lookup (letrec-expression-body e))))
	  ((cons-expression? e)
	   (set-cons-expression-car! e (lookup (cons-expression-car e)))
	   (set-cons-expression-cdr! e (lookup (cons-expression-cdr e))))
	  (else (fuck-up))))
   es)
  es))

(define (expression? x)
 (or (constant-expression? x)
     (variable-access-expression? x)
     (lambda-expression? x)
     (application? x)
     (letrec-expression? x)
     (cons-expression? x)))

;;; From centersurroundlib-stuff.sc

(define (all-referenced-objects object)
 (let ((objects '(() #t #f))
       (chars '())
       (exacts '())
       (inexacts '())
       (symbols '())
       (expressions '())
       (primitives '())
       (strings '())
       (pairs '())
       (vectors '()))
  (let loop ((object object))
   (let ((num-obj
	  (reduce
	   + (map length
		  (list objects chars exacts inexacts symbols expressions
			primitives strings pairs vectors))
	   0)))
    (cond ((null? object) '())
	  ((boolean? object) '())
	  ((char? object)
	   (unless (memq object chars) (set! chars (cons object chars))))
	  ((and (number? object) (exact? object))
	   (unless (memq object exacts) (set! exacts (cons object exacts))))
	  ((and (number? object) (inexact? object))
	   (unless (memv object inexacts)
	    (set! inexacts (cons object inexacts))))
	  ((input-port? object) (set! objects (cons object objects)))
	  ((output-port? object) (set! objects (cons object objects)))
	  ((eof-object? object) (set! objects (cons object objects)))
	  ((symbol? object)
	   (unless (memq object symbols) (set! symbols (cons object symbols))))
	  ((procedure? object) (set! objects (cons object objects)))
	  ((expression? object) (unless (memq object expressions)
				 (set! expressions (cons object expressions))))
	  ((primitive-procedure? object)
	   (unless (memq object primitives)
	    (set! primitives (cons object primitives))))
	  ((string? object)
	   (unless (memq object strings) (set! strings (cons object strings))))
	  ((pair? object)
	   (unless (memq object pairs)
	    (set! pairs (cons object pairs))
	    (loop (car object))
	    (loop (cdr object))))
	  ((vector? object)
	   (unless (memq object vectors)
	    (set! vectors (cons object vectors))
	    (for-each-vector loop object)))
	  (else (panic "Can't determine subobjects of this object")))))
  (list objects chars exacts inexacts symbols expressions
	primitives strings pairs vectors object)))

(define (serialize object es)
 (let* ((o-oss (all-referenced-objects object))
	(o (last o-oss))
	(oss (but-last o-oss))
	(objects (append (reduce append oss '()) (list object)))
	(num-objects (length objects))
	(os-lengths (map length oss))
	(os-offsets
	 (let loop ((l (list 0)))
	  (if (= (length l) (length os-lengths))
	      (reverse l)
	      (loop (cons (+ (first l) (list-ref os-lengths (- (length l) 1)))
			  l)))))
	(sanity-check (when (not (= (reduce + (but-last os-lengths) 0)
				    (last os-offsets)))
		       (panic "Wrong-o!"))))
  (define (lookup o)
   (let* ((category (cond ((or (null? o) (boolean? o)) 0)
			  ((char? o) 1)
			  ((and (number? o) (exact? o)) 2)
			  ((and (number? o) (inexact? o)) 3)
			  ((symbol? o) 4)
			  ((expression? o) 5)
			  ((primitive-procedure? o) 6)
			  ((string? o) 7)
			  ((pair? o) 8)
			  ((vector? o) 9)
			  (else 0)))
	  (os (list-ref oss category))
	  (offset (list-ref os-offsets category))
	  (positionc (if (= category 3) positionv positionq))
	  (result (+ (positionc o os) offset)))
    (when (not (or (and (= category 3) (eqv? o (list-ref objects result)))
		   (eq? o (list-ref objects result))))
     (panic "Lookup mess-up"))
    result))
  (map-indexed
   (lambda (object i)
    (cond ((null? object) object)
	  ((boolean? object) object)
	  ((char? object) `(character ,(char->integer object)))
	  ((and (number? object) (exact? object)) object)
	  ((and (number? object) (inexact? object))
	   `(double ,(double-part object 0)
		    ,(double-part object 1)
		    ,(double-part object 2)
		    ,(double-part object 3)))
	  ((input-port? object) (panic "Can't serialize input ports"))
	  ((output-port? object) (panic "Can't serialize output ports"))
	  ((eof-object? object) '(eof))
	  ((symbol? object) object)
	  ((procedure? object) (panic "Can't serialize procedures"))
	  ((expression? object) `(expression ,(positionq object es)))
	  ((primitive-procedure? object)
	   `(primitive-procedure ,(primitive-procedure-name object)))
	  ((string? object)
	   `(string ,@(map char->integer (string->list object))))
	  ((pair? object) `(pair ,(lookup (car object))
				 ,(lookup (cdr object))))
	  ((vector? object)
	   `(vector ,@(vector->list
		       (map-vector (lambda (object) (lookup object))
				   object))))
	  (else (panic "Can't serialize this object"))))
   objects)))

(define (eof)
 (call-with-output-file "/tmp/eof" (lambda (port) #f))
 (let ((eof-object
	(call-with-input-file "/tmp/eof" (lambda (port) (read port)))))
  (system "rm /tmp/eof")
  eof-object))

(define (unserialize serialized-objects es)
 (let ((new-objects
	(map (lambda (serialized-object)
	      (if (pair? serialized-object)
		  (case (first serialized-object)
		   ((character) (integer->char (second serialized-object)))
		   ((double)
		    (make-double (second serialized-object)
				 (third serialized-object)
				 (fourth serialized-object)
				 (fifth serialized-object)))
		   ((eof) (eof))
		   ((string)
		    (list->string
		     (map integer->char (rest serialized-object))))
		   ((expression) (list-ref es (second serialized-object)))
		   ((primitive-procedure)
		    (value-binding-value
		     (find-if
		      (lambda (b) (variable=? (value-binding-variable b)
					      (second serialized-object)))
		      *value-bindings*)))
		   ((pair) (cons #f #f))
		   ((vector)
		    (make-vector (length (rest serialized-object)) #f))
		   (else (fuck-up)))
		  serialized-object))
	     serialized-objects)))
  (for-each
   (lambda (serialized-object new-object)
    (cond
     ((expression? new-object) '())
     ((primitive-procedure? new-object) '())
     ((pair? new-object)
      (set-car! new-object (list-ref new-objects (second serialized-object)))
      (set-cdr! new-object (list-ref new-objects (third serialized-object))))
     ((vector? new-object)
      (for-each-n
       (lambda (i)
	(vector-set!
	 new-object i
	 (list-ref new-objects (list-ref (rest serialized-object) i))))
       (vector-length new-object)))))
   serialized-objects new-objects)
  (last new-objects)))

(define (write-checkpoint-to-file object pathname)
 (let ((es (serialize-expressions *expression-list*))
       (x (serialize object *expression-list*)))
  (call-with-output-file (replace-extension pathname "checkpoint")
   (lambda (port) (write (list es x) port) (newline port)))))

(define (read-checkpoint-from-file pathname)
 (let* ((es-x (call-with-input-file (replace-extension pathname "checkpoint")
	       read))
	(es (unserialize-expressions (first es-x))))
  (set! *expression-list* es)
  (unserialize (second es-x) es)))

;;; End from centersurroundlib-stuff.sc

;;; to-do: Put the following code in the appropriate places.

;;; If we don't recurse on nonrecursive closures, each and every value
;;; resulting from the same lambda expression will return #t.  This is a
;;; definite issue.
;;;
;;; To remedy this, we'll take this conservative tact--
;;;   - if either v1 or v2 is up, return #t -- this is conservative and will
;;;     alleviate the need to loop in the trees
;;;   - otherwise, do the standard thing, but recurse into closures as needed
(define (nonempty-abstract-value-intersection? v1 v2)
 ;; note: this is a conservative approximation.  When this returns #f, it is
 ;;       guaranteed to be #f.  However, this will sometimes return #t when the
 ;;       result is indeed #f.
 (or
  (up? v1)
  (up? v2)
  (some
   (lambda (u1)
    (cond ((null? u1) (some null? v2))
	  ((or (eq? u1 #t) (eq? u1 #f)) (some (lambda (u2) (eq? u2 u1)) v2))
	  ((real? u1) (some (lambda (u2) (or (eq? u2 u1) (eq? u2 'real))) v2))
	  ((eq? u1 'real)
	   (some (lambda (u2) (or (real? u2) (eq? u2 'real))) v2))
	  ((primitive-procedure? u1) (some (lambda (u2) (eq? u2 u1)) v2))
	  ;; For two pairs to possibly have a nonempty intersection, must they
	  ;;   have the same set of tags?  This is what the following code
	  ;;   assumes.
	  ((branching-value? u1)
	   (some (lambda (u2)
		  ;; Do we really need (branching-value? u2) here?
		  ;;   branching-value-match? will check what's necessary
		  (and (branching-value? u2)
		       (branching-value-match? u1 u2)
		       (every nonempty-abstract-value-intersection?
			      (branching-value-values u1)
			      (branching-value-values-matching u1 u2))))
		 v2))
;;;	  ((nonrecursive-closure? u1)
;;;	   (some (lambda (u2)
;;;		  (and (nonrecursive-closure? u2)
;;;		       (nonrecursive-closure-match? u1 u2)
;;;		       (nonempty-abstract-environment-intersection?
;;;			(nonrecursive-closure-values u1)
;;;			(nonrecursive-closure-values-matching u1 u2))))
;;;		 v2))
;;;	  ((recursive-closure? u1)
;;;	   (some (lambda (u2)
;;;		  (and (recursive-closure? u2)
;;;		       (recursive-closure-match? u1 u2)
;;;		       (nonempty-abstract-environment-intersection?
;;;			(recursive-closure-values u1)
;;;			(recursive-closure-values-matching u1 u2))))
;;;		 v2))
;;;	  ;; needs work: do I need to worry about tags yet?
;;;	  ((tagged-pair? u1)
;;;	   (some (lambda (u2)
;;;		  (and (tagged-pair? u2)
;;;		       (nonempty-abstract-value-intersection?
;;;			(tagged-pair-car u1) (tagged-pair-car u2))
;;;		       (nonempty-abstract-value-intersection?
;;;			(tagged-pair-cdr u1) (tagged-pair-cdr u2))))
;;;		 v2))
	  (else (panic "Not a proto-abstract value!"))))
   v1)))

(define (nonempty-abstract-environment-intersection? vs1 vs2)
 (every-vector nonempty-abstract-value-intersection? vs1 vs2))

;;; An abstract mapping x->y in an abstract function f is redundant if there
;;; exists a different abstract mapping x'->y' in f such that:
;;;   - x is a subset of x' and
;;;   - y' is a subset of y

(define (remove-redundant-abstract-mappings bs)
 ;; An abstract mapping xi->yi in [x1->y1, ..., xn->yn] is redundant if
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

(define (imprec-value-union v1 v2)
 (if *imprec-no-unroll?*
     (abstract-value-union-without-unroll v1 v2)
     (abstract-value-union v1 v2)))

(define (imprec-environment-union vs1 vs2)
 (if *imprec-no-unroll?*
     (abstract-environment-union-without-unroll vs1 vs2)
     (abstract-environment-union vs1 vs2)))

(define (make-abstract-mapping-safe-to-add b bs0)
 ;; b = x |-> y
 ;; must hold: (forall i:xi intersects x) (subset? yi y)
 (report-time-for
  'safe #f #f b
  (lambda ()
   (let ((x-bar (abstract-environment-binding-abstract-values b))
	 (y-bar0 (abstract-environment-binding-abstract-value b)))
    (let loop ((y-bar y-bar0) (bs bs0))
     (cond ((null? bs)
	    (if (eq? y-bar y-bar0)
		b
		(make-abstract-environment-binding x-bar y-bar)))
	   ((nonempty-abstract-environment-intersection?
	     x-bar (abstract-environment-binding-abstract-values (first bs)))
	    (let ((yi-bar (abstract-environment-binding-abstract-value
			   (first bs)))
		  (i (positionq (first bs) bs0)))
	     (if (abstract-value-subset? yi-bar y-bar)
		 (loop y-bar (rest bs))
		 (loop (imprec-value-union y-bar yi-bar)
		       (rest bs)))))
	   (else (loop y-bar (rest bs)))))))))

;;; to-do: This has a bad name--it suggests that only mappings sigma |-> bottom
;;;          are added, but in fact it handles adding any mappings.
;;;        It also really acts as a sort of abstract flow union--one that
;;;          enforces monotonicity.
;;; rename?: add-new-abstract-domains-to-abstract-function
(define (add-new-abstract-environments-to-abstract-flow ei bs bs-new0)
 (define (add-new-abstract-environments-to-abstract-flow ei bs bs-new)
  (if (null? bs-new)
      bs
      ;; let b2       = (first bs-new)
      ;;     x1 -> y1 = b1
      ;;     x2 -> y2 = b2
      ;; then if x1 = x2, b1 is preserved while b2 is discarded
      (if (some (lambda (b1)
		 (abstract-environment-subset?
		  (abstract-environment-binding-abstract-values (first bs-new))
		  (abstract-environment-binding-abstract-values b1)))
		bs)
	  (add-new-abstract-environments-to-abstract-flow ei bs (rest bs-new))
	  (add-new-abstract-environments-to-abstract-flow
	   ei
	   (cons (make-abstract-mapping-safe-to-add (first bs-new) bs) bs)
	   (rest bs-new)))))
 (if (null? bs-new0)
     bs
     (add-new-abstract-environments-to-abstract-flow ei bs bs-new0)))

(define (introduce-imprecision-to-abstract-mapping-in-flow ei i bs bs-old)
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
		(if (report-time-for
		     'sub ei (positionq b bs) #f
		     (lambda ()
		      (when
			(and #t
			     (= *num-updates* 433)
			     (= (vector-ref *call-buckets*
					    (positionq 'sub *bucket-names*))
				7248))
		       (write-checkpoint-to-file (list vs vs-new all-vs-old)
						 "vs7248"))
		      (abstract-environment-proper-subset? vs vs-new)))
		    (make-abstract-mapping-safe-to-add
		     (make-abstract-environment-binding
		      vs-new (abstract-environment-binding-abstract-value b))
		     bs)
		    b)))
	    (v-new (widen-abstract-value v)))
      (list-replace bs
		    (positionq b bs)
		    (make-abstract-environment-binding vs-new v-new)))))

;;; How should we deal with the widening by restricting # of flow elements?
;;;
;;; One solution would be to do things in the old fashion, just with our new
;;; safeguards.  This is kinda random and unprincipled, but it is simple.
;;;
;;; Another solution would be to do some sort of ordering on the environments
;;; (think grouping them into a tree/forest with ordering being based off of
;;;  the subset relation).  One could then decide to favor special cases, the
;;;  most general case, etc with regards to which to widen/preserve.
;;;
;;; Yet another (more far-out) idea occurs.  Suppose that the compiler had an
;;; interest in a particular case (environment or set thereof).  We could look
;;; to preserve such cases during the analysis in order to satisfy the
;;; compiler.  In fact, one could imagine that for each expression, the
;;; compiler might be interested in some (potentially-empty) set of cases and
;;; specify this to the flow analysis.
;;;
;;; Again another approach--perhaps it's best to try to group mappings with
;;; "similar" ranges, while keeping mappings with "different" ranges separate.
;;;
;;; This list could really go on, and I'm not sure what the best way is right
;;; now.  In fact, these latter two, while appealing, are pretty vague and
;;; would require a bit of thought into what would be useful.  They might best
;;; be considered as future improvements.  The sorting idea could lead to some
;;; perahps more directed methods of restricting # of flow elements.  However,
;;; it's unclear at this stage what sort of heuristics might be most beneficial
;;; to the compiler.  So, I'm reluctantly implementing the first (and simplest)
;;; approach.  It'd be a good idea to revisit this discussion at a later time.

(define (introduce-imprecision-by-restricting-abstract-function-size k bs)
 ;;    a. *somehow* pick 2 flow elements m1 and m2 to replace with a new one
 ;;    b. these two can be replaced with an abstract mapping which maps the
 ;;       Dom(m1)uDom(m2) to a range AT LEAST as wide as Range(m1)uRange(m2).
 ;;    c. after this is done, we should widen domain/range and remove redundant
 ;;       mappings. (is this check needed? Yes!)
 ;;    d. if still over the # of flow elements, goto a
 (if (<= (length bs) k)
     bs
     (let* ((b1 (first bs))
	    (b2 (second bs))
	    (vs1 (abstract-environment-binding-abstract-values b1))
	    (v1 (abstract-environment-binding-abstract-value b1))
	    (vs2 (abstract-environment-binding-abstract-values b2))
	    (v2 (abstract-environment-binding-abstract-value b2))
	    (b-new
	     (make-abstract-mapping-safe-to-add
	      (make-abstract-environment-binding
	       (map-vector widen-abstract-value
			   (imprec-environment-union vs1 vs2))
	       (imprec-value-union v1 v2))
	      (rest (rest bs))))
	    (b-new (make-abstract-environment-binding
		    (abstract-environment-binding-abstract-values b-new)
		    (widen-abstract-value
		     (abstract-environment-binding-abstract-value b-new)))))
      (introduce-imprecision-by-restricting-abstract-function-size
       k (remove-redundant-abstract-mappings (cons b-new (rest (rest bs))))))))

(define (introduce-imprecision-by-restricting-abstract-function-size2 k bs)
 ;;    a. *somehow* pick 2 flow elements m1 and m2 to replace with a new one
 ;;    b. these two can be replaced with an abstract mapping which maps the
 ;;       Dom(m1)uDom(m2) to a range AT LEAST as wide as Range(m1)uRange(m2).
 ;;    c. after this is done, we should widen domain/range and remove redundant
 ;;       mappings. (is this check needed? Yes!)
 ;;    d. if still over the # of flow elements, goto a
 (if (<= (length bs) k)
     bs
     (let ((result
	    (let* ((b1 (first bs))
		   (b2 (second bs))
		   (vs1 (abstract-environment-binding-abstract-values b1))
		   (v1 (abstract-environment-binding-abstract-value b1))
		   (vs2 (abstract-environment-binding-abstract-values b2))
		   (v2 (abstract-environment-binding-abstract-value b2)))
	     (make-abstract-mapping-safe-to-add
	      (make-abstract-environment-binding
	       (imprec-environment-union vs1 vs2)
	       (imprec-value-union v1 v2))
	      (rest (rest bs))))))
      (introduce-imprecision-by-restricting-abstract-function-size2
       k (cons result (rest (rest bs)))))))

;;; At the present, introduce-imprecision-to-abstract-flow only avoids
;;; unnecessary syntactic checks/widening when the whole flow is identical
;;; (eq?) to the previous flow.  In the future, we could implement a means to
;;; avoid unnecessary checks on individual mappings within the flow:
;;;   a mapping m in bs doesn't need checked/widened if:
;;;      - exists m' in bs-old such that (eq? m m')
(define (introduce-imprecision-to-abstract-flow ei bs bs-old)
 ;; bs is the current abstract flow
 ;; bs-old is the last abstract flow
 (report-time-for
  'imprec ei #f bs
  (lambda ()
   (if (eq? bs bs-old)
       bs
       (if *widen-first?*
	   ;; 0. remove redundant flow elements (will this do anything here??)
	   ;; 1. widen flow domains
	   ;; 2. widen flow ranges
	   ;; 3. remove redundant flow elements
	   (let ((bs-new
		  (remove-redundant-abstract-mappings
		   (let loop ((i 0)
			      ;; this remove-redundant-abstract-mappings
			      ;; sometimes incites a slowdown
			      (bs (if *test?*
				      bs
				      (remove-redundant-abstract-mappings
				       bs))))
		    (if (= i (length bs))
			bs
			(loop
			 (+ i 1)
			 (introduce-imprecision-to-abstract-mapping-in-flow
			  ei i bs bs-old)))))))
	    ;; 4. restrict # of flow elements
	    (if (not (eq? #f *l1*))
		(introduce-imprecision-by-restricting-abstract-function-size
		 *l1* bs-new)
		bs-new))
	   (let*
	     ((bs-new
	       (report-time-for
		'l1 ei #f bs
		(lambda ()
		 (if
		  (not (eq? #f *l1*))
		  (introduce-imprecision-by-restricting-abstract-function-size2
		   *l1* bs)
		  bs))))
	      (result
	       (report-time-for
		'l-rest ei #f bs-new
		(lambda ()
		 (let loop ((i 0)
			    ;; this remove-redundant-abstract-mappings1
			    ;; sometimes incites a slowdown
			    (bs (if *test?*
				    bs-new
				    (report-time-for
				     'remove1 #f #f bs-new
				     (lambda ()
				      (remove-redundant-abstract-mappings
				       bs-new))))))
		  (if (= i (length bs))
		      bs
		      (loop
		       (+ i 1)
		       (introduce-imprecision-to-abstract-mapping-in-flow
			ei i bs bs-old))))))))
	    (report-time-for
	     'remove2 #f #f result
	     (lambda () (remove-redundant-abstract-mappings result)))))))))

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
  (let ((x1 (vlad-car x '())) (x23 (vlad-cdr x '())))
   (unless (vlad-pair? x23 '())
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 (vlad-car x23 '()) (vlad-cdr x23 '())))))

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
  (abstract-binary-u->v abstract-bundle-u "bundle")
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
