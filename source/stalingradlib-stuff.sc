(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - A global optimizing compiler for Scheme
;;; Copyright 2004 Purdue University. All rights reserved.

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
;;;    barak@cs.may.ie
;;;    http://www-bcl.cs.may.ie/~bap

(include "QobiScheme.sch")
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. LET, AND, and OR macros and NOT procedure
;;;  2. factor common constants
;;;  3. spread arguments should be lists
;;;  4. DEFINE
;;;  5. () -> '()
;;;  6. quoted list constants
;;;  7. unary -

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: value
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

;;; Structures

(define-structure variable-access-expression variable)

(define-structure application callee argument)

(define-structure lambda-expression variable free-variables body)

(define-structure letrec-expression
 procedure-variables argument-variables bodies body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure closure value-bindings variable body)

(define-structure recursive-closure
 value-bindings procedure-variables argument-variables bodies)

(define-structure primitive-procedure procedure)

;;; Variables

(define *gensym* 0)

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

(define *last* '())

;;; Parameters

;;; Procedures

(define (syntax-check-parameter! p)
 (cond
  ((symbol? p)
   (when (memq p '(lambda letrec let* if cons cond else))
    (panic (format #f "Invalid variable: ~s" p)))
   #f)
  ((and (list? p) (not (null? p)))
   (case (first p)
    ((cons)
     (unless (= (length p) 3) (panic (format #f "Invalid parameter: ~s" p)))
     (syntax-check-parameter! (second p))
     (syntax-check-parameter! (third p)))
    (else (panic (format #f "Invalid parameter: ~s" p)))))
  (else (panic (format #f "Invalid parameter: ~s" p)))))

(define (parameter-variables p)
 (cond
  ((symbol? p) (list p))
  ((list? p)
   (case (first p)
    ((cons)
     (append (parameter-variables (second p)) (parameter-variables (third p))))
    (else (fuck-up))))
  (else (fuck-up))))

(define (duplicatesq? xs)
 (and (not (null? xs))
      (or (memq (first xs) (rest xs)) (duplicatesq? (rest xs)))))

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol (format #f "G~s" gensym))))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs *basis-constants*))
  (cond
   ((null? e) #f)
   ((boolean? e) #f)
   ((real? e) #f)
   ((symbol? e)
    (unless (memq e xs) (panic (format #f "Unbound variable: ~s" e)))
    #f)
   ((list? e)
    (case (first e)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop `(lambda (,(gensym)) ,(third e)) xs))
       ((1) (syntax-check-parameter! (first (second e)))
	    (let ((xs0 (parameter-variables (first (second e)))))
	     (when (duplicatesq? xs0)
	      (panic (format #f "Duplicate variables: ~s" (second e))))
	     (loop (third e) (append xs0 xs))))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   xs))))
     ((letrec)
      (unless (and (= (length e) 3)
		   (list? (second e))
		   (every (lambda (b)
			   (and (list? b)
				(= (length b) 2)
				(symbol? (first b))
				(list? (second b))
				(= (length (second b)) 3)
				(eq? (first (second b)) 'lambda)))
			  (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (let ((xs0 (map first (second e))))
       (when (duplicatesq? xs0)
	(panic (format #f "Duplicate variables: ~s" e)))
       (for-each (lambda (b) (loop (second b) (append xs0 xs))) (second e))
       (loop (third e) (append xs0 xs))))
     ((let*)
      (unless (and (= (length e) 3)
		   (list? (second e))
		   (every (lambda (b) (and (list? b) (= (length b) 2)))
			  (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (third e) xs))
       ((1) (loop `((lambda (,(first (first (second e)))) ,(third e))
		    ,(second (first (second e))))
		  xs))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 xs))))
     ((if) (loop
	    ;; needs work: to ensure that you don't shadow if-procedure
	    `((if-procedure
	       ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))
	    xs))
     ;; needs work: to ensure that you don't shadow cons-procedure
     ((cons) (loop `((cons-procedure ,(second e)) ,(third e)) xs))
     ((cond)
      (unless (and (>= (length e) 2)
		   (every (lambda (b) (and (list? b) (= (length b) 2)))
			  (rest e))
		   (eq? (first (last e)) 'else))
       (panic (format #f "Invalid expression: ~s" e)))
      (loop (if (null? (rest (rest e)))
		(second (second e))
		`(if ,(first (second e))
		     ,(second (second e))
		     (cond ,@(rest (rest e)))))
	    xs))
     (else
      (case (length (rest e))
       ((0) (loop `(,(first e) ()) xs))
       ((1) (loop (first e) xs)
	    (loop (second e) xs))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (abstract->concrete e)
 (cond
  ((variable-access-expression? e) (variable-access-expression-variable e))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((lambda-expression? e)
   `(lambda (,(lambda-expression-variable e))
     ,(abstract->concrete (lambda-expression-body e))))
  ((letrec-expression? e)
   `(letrec ,(map (lambda (x1 x2 e)
		   `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		  (letrec-expression-procedure-variables e)
		  (letrec-expression-argument-variables e)
		  (letrec-expression-bodies e))
     ,(abstract->concrete (letrec-expression-body e))))
  (else (fuck-up))))

(define (concrete->abstract-parameter p)
 (cond ((symbol? p) p)
       ((list? p)
	(case (first p)
	 ((cons) (gensym))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (parameter-variable-bindings x p)
 (let loop ((p p) (e (make-variable-access-expression x)))
  (cond ((symbol? p) (list (make-variable-binding p e)))
	((list? p)
	 (case (first p)
	  ((cons)
	   (append (loop (second p)
			 (make-application
			  ;; needs work: to ensure that you don't shadow car
			  (make-variable-access-expression 'car) e))
		   (loop (third p)
			 (make-application
			  ;; needs work: to ensure that you don't shadow cdr
			  (make-variable-access-expression 'cdr) e))))
	  (else (fuck-up))))
	(else (fuck-up)))))

(define (free-variables-in e)
 (cond ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((application? e)
	(unionq (free-variables-in (application-callee e))
		(free-variables-in (application-argument e))))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       ((letrec-expression? e)
	(set-differenceq
	 (unionq (reduce unionq
			 (map (lambda (x e) (removeq x (free-variables-in e)))
			      (letrec-expression-argument-variables e)
			      (letrec-expression-bodies e))
			 '())
		 (free-variables-in (letrec-expression-body e)))
	 (letrec-expression-procedure-variables e)))
       (else (fuck-up))))

(define (concrete->abstract-expression e)
 (let loop ((e e) (bs *variable-bindings*))
  (cond
   ((null? e)
    (let ((x (gensym)))
     (list (make-variable-access-expression x)
	   (list (make-value-binding x e)))))
   ((boolean? e)
    (let ((x (gensym)))
     (list (make-variable-access-expression x)
	   (list (make-value-binding x e)))))
   ((real? e)
    (let ((x (gensym)))
     (list (make-variable-access-expression x)
	   (list (make-value-binding x e)))))
   ((symbol? e)
    (list (variable-binding-expression
	   (find-if (lambda (b) (eq? (variable-binding-variable b) e)) bs))
	  '()))
   ((list? e)
    (case (first e)
     ((lambda)
      (case (length (second e))
       ((0) (loop `(lambda (,(gensym)) ,(third e)) bs))
       ((1) (let* ((x (concrete->abstract-parameter (first (second e))))
		   (result
		    (loop
		     (third e)
		     (append
		      (parameter-variable-bindings x (first (second e))) bs))))
	     (list (make-lambda-expression
		    x
		    (removeq x (free-variables-in (first result)))
		    (first result))
		   (second result))))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   bs))))
     ((letrec)
      (let* ((bs
	      (append
	       (map (lambda (b)
		     (make-variable-binding
		      (first b) (make-variable-access-expression (first b))))
		    (second e))
	       bs))
	     (results (map (lambda (b) (loop (second b) bs)) (second e)))
	     (result (loop (third e) bs)))
       (list
	(make-letrec-expression
	 (map first (second e))
	 (map (lambda (result) (lambda-expression-variable (first result)))
	      results)
	 (map (lambda (result) (lambda-expression-body (first result)))
	      results)
	 (first result))
	(append (second result) (reduce append (map second results) '())))))
     ((let*)
      (case (length (second e))
       ((0) (loop (third e) bs))
       ((1) (loop `((lambda (,(first (first (second e)))) ,(third e))
		    ,(second (first (second e))))
		  bs))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 bs))))
     ((if) (loop
	    ;; needs work: to ensure that you don't shadow if-procedure
	    `((if-procedure
	       ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))
	    bs))
     ((cons)
      ;; needs work: to ensure that you don't shadow cons-procedure
      (loop `((cons-procedure ,(second e)) ,(third e)) bs))
     ((cond) (loop (if (null? (rest (rest e)))
		       (second (second e))
		       `(if ,(first (second e))
			    ,(second (second e))
			    (cond ,@(rest (rest e)))))
		   bs))
     (else
      (case (length (rest e))
       ((0) (loop `(,(first e) ()) bs))
       ((1) (let ((result1 (loop (first e) bs))
		  (result2 (loop (second e) bs)))
	     (list (make-application (first result1) (first result2))
		   (append (second result1) (second result2)))))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 bs))))))
   (else (fuck-up)))))

(define (externalize v)
 (cond
  ((null? v) '())
  ((boolean? v) v)
  ((real? v) v)
  ((pair? v) (cons (externalize (car v)) (externalize (cdr v))))
  ((primitive-procedure? v) 'primitive-procedure)
  ((closure? v)
   `(closure ,(map (lambda (b)
		    (list (value-binding-variable b)
			  (externalize (value-binding-value b))))
		   (closure-value-bindings v))
	     (lambda (,(closure-variable v))
	      ,(abstract->concrete (closure-body v)))))
  ((recursive-closure? v)
   `(recursive-closure
     ,(map (lambda (b)
	    (list (value-binding-variable b)
		  (externalize (value-binding-value b))))
	   (recursive-closure-value-bindings v))
     ,(map (lambda (x1 x2 e) `(,x1 (lambda (,x2) ,(abstract->concrete e))))
	   (recursive-closure-procedure-variables v)
	   (recursive-closure-argument-variables v)
	   (recursive-closure-bodies v))))
  (else (fuck-up))))

(define (run-time-error message v)
 (format #t "Last trace~%")
 (set-write-level! 5)
 (set-write-length! 5)
 (for-each (lambda (record)
	    (write (abstract->concrete (first record)))
	    (newline))
	   *last*)
 (newline)
 (pp (externalize v))
 (newline)
 (panic message))

(define (call callee argument)
 (cond
  ((primitive-procedure? callee)
   ((primitive-procedure-procedure callee) argument))
  ((closure? callee)
   (evaluate (closure-body callee)
	     (cons (make-value-binding (closure-variable callee) argument)
		   (closure-value-bindings callee))))
  ((recursive-closure? callee)
   (evaluate
    (first (recursive-closure-bodies callee))
    (cons
     (make-value-binding
      (first (recursive-closure-argument-variables callee)) argument)
     (append
      (map-indexed
       (lambda (x i)
	(make-value-binding
	 x
	 (make-recursive-closure
	  (recursive-closure-value-bindings callee)
	  (cons (list-ref (recursive-closure-procedure-variables callee) i)
		(list-remove (recursive-closure-procedure-variables callee) i))
	  (cons (list-ref (recursive-closure-argument-variables callee) i)
		(list-remove (recursive-closure-argument-variables callee) i))
	  (cons (list-ref (recursive-closure-bodies callee) i)
		(list-remove (recursive-closure-bodies callee) i)))))
       (recursive-closure-procedure-variables callee))
      (recursive-closure-value-bindings callee)))))
  (else (run-time-error "Target is not a procedure" callee))))

(define (evaluate e bs)
 (cond
  ((variable-access-expression? e)
   (value-binding-value
    (find-if (lambda (b)
	      (eq? (value-binding-variable b)
		   (variable-access-expression-variable e)))
	     bs)))
  ((application? e)
   (let ((v1 (evaluate (application-callee e) bs))
	 (v2 (evaluate (application-argument e) bs)))
    (set! *last*
	  (cons (list e v1 v2)
		(if (>= (length *last*) 10) (but-last *last*) *last*)))
    (call v1 v2)))
  ((lambda-expression? e)
   (let ((free-variables (free-variables-in e)))
    (make-closure
     (remove-if-not
      (lambda (b) (memq (value-binding-variable b) free-variables)) bs)
     (lambda-expression-variable e)
     (lambda-expression-body e))))
  ((letrec-expression? e)
   (let* ((xs1 (letrec-expression-procedure-variables e))
	  (xs2 (letrec-expression-argument-variables e))
	  (es (letrec-expression-bodies e))
	  (free-variables
	   (set-differenceq
	    (reduce
	     unionq
	     (map (lambda (x e) (removeq x (free-variables-in e))) xs2 es)
	     '())
	    xs1)))
    (evaluate
     (letrec-expression-body e)
     (append
      (let ((bs (remove-if-not
		 (lambda (b) (memq (value-binding-variable b) free-variables))
		 bs)))
       (map-indexed (lambda (x i)
		     (make-value-binding
		      x
		      (make-recursive-closure
		       bs
		       (cons (list-ref xs1 i) (list-remove xs1 i))
		       (cons (list-ref xs2 i) (list-remove xs2 i))
		       (cons (list-ref es i) (list-remove es i)))))
		    xs1))
      bs))))
  (else (fuck-up))))

(define (define-primitive-basis-constant x procedure)
 (set! *basis-constants* (cons x *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding x (make-variable-access-expression x))
	     *variable-bindings*))
 (set! *value-bindings*
       (cons (make-value-binding x (make-primitive-procedure procedure))
	     *value-bindings*)))

(define (initialize-basis!)
 (define-primitive-basis-constant
  '+
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to +" x))
   (+ (car x) (cdr x))))
 (define-primitive-basis-constant
  '-
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to -" x))
   (- (car x) (cdr x))))
 (define-primitive-basis-constant
  '*
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to *" x))
   (* (car x) (cdr x))))
 (define-primitive-basis-constant
  '/
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to /" x))
   (/ (car x) (cdr x))))
 (define-primitive-basis-constant
  'sqrt
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to sqrt" x))
   (sqrt x)))
 (define-primitive-basis-constant
  'exp
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to exp" x))
   (exp x)))
 (define-primitive-basis-constant
  'log
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to log" x))
   (log x)))
 (define-primitive-basis-constant
  'sin
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to sin" x))
   (sin x)))
 (define-primitive-basis-constant
  'cos
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to cos" x))
   (cos x)))
 (define-primitive-basis-constant
  'atan
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to atan" x))
   (atan (car x) (cdr x))))
 (define-primitive-basis-constant
  '=
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to =" x))
   (= (car x) (cdr x))))
 (define-primitive-basis-constant
  '<
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to <" x))
   (< (car x) (cdr x))))
 (define-primitive-basis-constant
  '>
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to >" x))
   (> (car x) (cdr x))))
 (define-primitive-basis-constant
  '<=
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to <=" x))
   (<= (car x) (cdr x))))
 (define-primitive-basis-constant
  '>=
  (lambda (x)
   (unless (and (pair? x) (real? (car x)) (real? (cdr x)))
    (run-time-error "Invalid argument to >=" x))
   (>= (car x) (cdr x))))
 (define-primitive-basis-constant
  'zero?
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to zero?" x))
   (zero? x)))
 (define-primitive-basis-constant
  'positive?
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to positive?" x))
   (positive? x)))
 (define-primitive-basis-constant
  'negative?
  (lambda (x)
   (unless (real? x) (run-time-error "Invalid argument to negative?" x))
   (negative? x)))
 (define-primitive-basis-constant
  'null?
  (lambda (x) (null? x)))
 (define-primitive-basis-constant
  'boolean?
  (lambda (x) (boolean? x)))
 (define-primitive-basis-constant
  'real?
  (lambda (x) (real? x)))
 (define-primitive-basis-constant
  'pair?
  (lambda (x) (pair? x)))
 (define-primitive-basis-constant
  'procedure?
  (lambda (x)
   (or (primitive-procedure? x) (closure? x) (recursive-closure? x))))
 (define-primitive-basis-constant
  'car
  (lambda (x)
   (unless (pair? x) (run-time-error "Invalid argument to car" x))
   (car x)))
 (define-primitive-basis-constant
  'cdr
  (lambda (x)
   (unless (pair? x) (run-time-error "Invalid argument to cdr" x))
   (cdr x)))
 (define-primitive-basis-constant
  'cons-procedure
  ;; note that we can't apply j-forward or j-reverse to the result of
  ;; (cons-procedure e)
  (lambda (x) (make-primitive-procedure (lambda (y) (cons x y)))))
 (define-primitive-basis-constant
  'if-procedure
  (lambda (x)
   (unless (and (pair? x) (pair? (car x)))
    (run-time-error "Invalid argument to if-procedure" x))
   (unless (boolean? (caar x)) (run-time-error "Antecedent is not boolean" x))
   (if (caar x) (cdar x) (cdr x))))
 (define-primitive-basis-constant
  'eq?
  (lambda (x)
   (unless (pair? x) (run-time-error "Invalid argument to eq?" x))
   (or (eq? (car x) (cdr x))
       (and (closure? (car x))
	    (closure? (cdr x))
	    (eq? (closure-body (car x)) (closure-body (cdr x))))
       (and (recursive-closure? (car x))
	    (recursive-closure? (cdr x))
	    (= (length (recursive-closure-bodies (car x)))
	       (length (recursive-closure-bodies (cdr x))))
	    (every eq?
		   (recursive-closure-bodies (car x))
		   (recursive-closure-bodies (cdr x)))))))
 (define-primitive-basis-constant
  'map-closure
  (lambda (x)
   (unless (and (pair? x) (or (closure? (cdr x)) (recursive-closure? (cdr x))))
    (run-time-error "Invalid argument to map-closure" x))
   (cond ((closure? (cdr x))
	  (make-closure
	   (map (lambda (b)
		 (make-value-binding
		  (value-binding-variable b)
		  (call (car x) (value-binding-value b))))
		(closure-value-bindings (cdr x)))
	   (closure-variable (cdr x))
	   (closure-body (cdr x))))
	 ((recursive-closure? (cdr x))
	  (make-recursive-closure
	   (map (lambda (b)
		 (make-value-binding
		  (value-binding-variable b)
		  (call (car x) (value-binding-value b))))
		(recursive-closure-value-bindings (cdr x)))
	   (recursive-closure-procedure-variables (cdr x))
	   (recursive-closure-argument-variables (cdr x))
	   (recursive-closure-bodies (cdr x))))
	 (else (fuck-up)))))
 (define-primitive-basis-constant
  'write
  (lambda (x)
   (write (externalize x))
   (newline)
   x)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
