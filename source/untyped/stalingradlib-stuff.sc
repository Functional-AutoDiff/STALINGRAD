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
;;;  1. The forward and reverse versions of the primitives will give car/cdr
;;;     errors instead of primitive-specific errors in certain circumstances.
;;;  2. AND and OR macros and NOT function

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete variable

;;; Macros

;;; Structures

(define-structure constant-expression value)

(define-structure variable-access-expression variable)

(define-structure application callee argument)

(define-structure lambda-expression variable body)

(define-structure if-expression antecedent consequent alternate)

(define-structure cons-expression car-argument cdr-argument)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure closure value-bindings lambda-expression)

(define-structure primitive-function procedure forward-value reverse-value)

;;; Variables

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

;;; Parameters

;;; Procedures

(define (syntax-check-parameter! p)
 (cond
  ((symbol? p)
   (when (memq p '(lambda let* if cons cond else unit))
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

(define (duplicatesq? l)
 (and (not (null? l)) (or (memq (first l) (rest l)) (duplicatesq? (rest l)))))

(define (gensym) (string->uninterned-symbol "gensym"))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs *basis-constants*))
  (cond
   ((boolean? e) #f)
   ((number? e) #f)
   ((symbol? e)
    (unless (or (eq? e 'unit) (memq e xs))
     (panic (format #f "Unbound variable: ~s" e)))
    #f)
   ((and (list? e) (not (null? e)))
    (case (first e)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop `(lambda (,(gensym)) ,(third e)) xs))
       ((1)
	(syntax-check-parameter! (first (second e)))
	(let ((xs0 (parameter-variables (first (second e)))))
	 (when (duplicatesq? xs0)
	  (panic (format #f "Duplicate variables: ~s" (second e))))
	 (loop (third e) (append xs0 xs))))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   xs))))
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
     ((if)
      (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs)
      (loop (third e) xs)
      (loop (fourth e) xs))
     ((cons)
      (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs)
      (loop (third e) xs))
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
       ((0) (loop `(,(first e) unit) xs))
       ((1) (loop (first e) xs)
	    (loop (second e) xs))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (abstract->concrete e)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e) (variable-access-expression-variable e))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((lambda-expression? e)
   `(lambda (,(lambda-expression-variable e))
     ,(abstract->concrete (lambda-expression-body e))))
  ((if-expression? e)
   `(if ,(abstract->concrete (if-expression-antecedent e))
	,(abstract->concrete (if-expression-consequent e))	
	,(abstract->concrete (if-expression-alternate e))))
  ((cons-expression? e)
   `(cons ,(abstract->concrete (cons-expression-car-argument e))
	  ,(abstract->concrete (cons-expression-cdr-argument e))))
  (else (fuck-up))))

(define (concrete->abstract-parameter p)
 (cond ((symbol? p) p)
       ((list? p)
	(case (first p)
	 ((cons) (gensym))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (parameter-variable-bindings variable p)
 (let loop ((p p) (e (make-variable-access-expression variable)))
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

(define (concrete->abstract-expression e)
 (let loop ((e e) (variable-bindings *variable-bindings*))
  (cond
   ((boolean? e) (make-constant-expression e))
   ((number? e) (make-constant-expression e))
   ((symbol? e)
    (if (eq? e 'unit)
	(make-constant-expression e)
	(variable-binding-expression
	 (find-if (lambda (variable-binding)
		   (eq? (variable-binding-variable variable-binding) e))
		  variable-bindings))))
   ((list? e)
    (case (first e)
     ((lambda)
      (case (length (second e))
       ((0) (loop `(lambda (,(gensym)) ,(third e)) variable-bindings))
       ((1) (let ((variable (concrete->abstract-parameter (first (second e)))))
	     (make-lambda-expression
	      variable
	      (loop (third e)
		    (append
		     (parameter-variable-bindings variable (first (second e)))
		     variable-bindings)))))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   variable-bindings))))
     ((let*)
      (case (length (second e))
       ((0) (loop (third e) variable-bindings))
       ((1) (loop `((lambda (,(first (first (second e)))) ,(third e))
		    ,(second (first (second e))))
		  variable-bindings))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 variable-bindings))))
     ((if) (make-if-expression (loop (second e) variable-bindings)
			       (loop (third e) variable-bindings)
			       (loop (fourth e) variable-bindings)))
     ((cons) (make-cons-expression (loop (second e) variable-bindings)
				   (loop (third e) variable-bindings)))
     ((cond) (loop (if (null? (rest (rest e)))
		       (second (second e))
		       `(if ,(first (second e))
			    ,(second (second e))
			    (cond ,@(rest (rest e)))))
		   variable-bindings))
     (else
      (case (length (rest e))
       ((0) (loop `(,(first e) unit) variable-bindings))
       ((1) (make-application (loop (first e) variable-bindings)
			      (loop (second e) variable-bindings)))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 variable-bindings))))))
   (else (fuck-up)))))

(define (forwardize e)
 (cond ((constant-expression? e)
	(cond ((eq? (constant-expression-value e) 'unit)
	       (make-cons-expression e (make-constant-expression 'unit)))
	      ((boolean? (constant-expression-value e))
	       (make-cons-expression e (make-constant-expression 'unit)))
	      ((number? (constant-expression-value e))
	       (make-cons-expression e (make-constant-expression 0)))
	      (else (fuck-up))))
       ((variable-access-expression? e) e)
       ((application? e)
	(make-application (forwardize (application-callee e))
			  (forwardize (application-argument e))))
       ((lambda-expression? e)
	(make-lambda-expression (lambda-expression-variable e)
				(forwardize (lambda-expression-body e))))
       ((if-expression? e)
	(make-if-expression (make-application
			     ;; needs work: to ensure that you don't shadow car
			     (make-variable-access-expression 'car)
			     (forwardize (if-expression-antecedent e)))
			    (forwardize (if-expression-consequent e))
			    (forwardize (if-expression-alternate e))))
       ((cons-expression? e)
	(make-cons-expression (forwardize (cons-expression-car-argument e))
			      (forwardize (cons-expression-cdr-argument e))))
       (else (fuck-up))))

(define (reversize e)
 (cond ((constant-expression? e)
	(cond
	 ((eq? (constant-expression-value e) 'unit)
	  (make-cons-expression
	   e
	   (make-lambda-expression
	    'x-tilde
	    (make-application (make-variable-access-expression 'x-tilde)
			      (make-constant-expression 'unit)))))
	 ((boolean? (constant-expression-value e))
	  (make-cons-expression
	   e
	   (make-lambda-expression
	    'x-tilde
	    (make-application (make-variable-access-expression 'x-tilde)
			      (make-constant-expression 'unit)))))
	 ((number? (constant-expression-value e))
	  (make-cons-expression
	   e
	   (make-lambda-expression
	    'x-tilde
	    (make-application (make-variable-access-expression 'x-tilde)
			      (make-constant-expression 0)))))
	 (else (fuck-up))))
       ((variable-access-expression? e) e)
       ((application? e)
	(make-application (reversize (application-callee e))
			  (reversize (application-argument e))))
       ((lambda-expression? e)
	(make-lambda-expression (lambda-expression-variable e)
				(reversize (lambda-expression-body e))))
       ((if-expression? e)
	(make-if-expression (make-application
			     ;; needs work: to ensure that you don't shadow car
			     (make-variable-access-expression 'car)
			     (reversize (if-expression-antecedent e)))
			    (reversize (if-expression-consequent e))
			    (reversize (if-expression-alternate e))))
       ((cons-expression? e)
	(make-cons-expression
	 (make-application
	  (make-application
	   ;; needs work: to ensure that you don't shadow map
	   (make-variable-access-expression 'map)
	   (make-lambda-expression
	    'x-tilde
	    (make-lambda-expression
	     'y-grave
	     (make-application
	      (make-variable-access-expression 'x-tilde)
	      ;; needs work: to ensure that you don't shadow car
	      (make-application (make-variable-access-expression 'car)
				(make-variable-access-expression 'y-grave))))))
	  (reversize (cons-expression-car-argument e)))
	 (make-application
	  (make-application
	   ;; needs work: to ensure that you don't shadow map
	   (make-variable-access-expression 'map)
	   (make-lambda-expression
	    'x-tilde
	    (make-lambda-expression
	     'y-grave
	     (make-application
	      (make-variable-access-expression 'x-tilde)
	      ;; needs work: to ensure that you don't shadow cdr
	      (make-application (make-variable-access-expression 'cdr)
				(make-variable-access-expression 'y-grave))))))
	  (reversize (cons-expression-cdr-argument e)))))
       (else (fuck-up))))

(define (j-forward x)
 (cond
  ((eq? x 'unit) (cons x 'unit))
  ((boolean? x) (cons x 'unit))
  ((number? x) (cons x 0))
  ((pair? x) (cons (j-forward (car x)) (j-forward (cdr x))))
  ((primitive-function? x) (primitive-function-forward-value x))
  ((closure? x)
   (make-closure
    (map (lambda (value-binding)
	  (make-value-binding (value-binding-variable value-binding)
			      (j-forward (value-binding-value value-binding))))
	 (closure-value-bindings x))
    (forwardize (closure-lambda-expression x))))
  (else (fuck-up))))

(define (j-reverse x)
 (cond
  ((eq? x 'unit)
   (cons x
	 (make-closure
	  '()
	  (make-lambda-expression
	   'x-tilde
	   (make-application (make-variable-access-expression 'x-tilde)
			     (make-constant-expression 'unit))))))
  ((boolean? x)
   (cons x
	 (make-closure
	  '()
	  (make-lambda-expression
	   'x-tilde
	   (make-application (make-variable-access-expression 'x-tilde)
			     (make-constant-expression 'unit))))))
  ((number? x)
   (cons x
	 (make-closure
	  '()
	  (make-lambda-expression
	   'x-tilde
	   (make-application (make-variable-access-expression 'x-tilde)
			     (make-constant-expression 0))))))
  ((pair? x) (cons (j-reverse (car x)) (j-reverse (cdr x))))
  ((primitive-function? x) (primitive-function-reverse-value x))
  ((closure? x)
   (make-closure
    (map (lambda (value-binding)
	  (make-value-binding (value-binding-variable value-binding)
			      (j-reverse (value-binding-value value-binding))))
	 (closure-value-bindings x))
    (reversize (closure-lambda-expression x))))
  (else (fuck-up))))

(define (evaluate e)
 (let loop ((e e) (value-bindings *value-bindings*))
  (define (call callee argument)
   (cond
    ((primitive-function? callee)
     ((primitive-function-procedure callee) argument))
    ((closure? callee)
     (loop
      (lambda-expression-body (closure-lambda-expression callee))
      (cons (make-value-binding
	     (lambda-expression-variable (closure-lambda-expression callee))
	     argument)
	    (closure-value-bindings callee))))
    (else (panic "Target is not a function"))))
  (cond ((constant-expression? e) (constant-expression-value e))
	((variable-access-expression? e)
	 (value-binding-value
	  (find-if (lambda (value-binding)
		    (eq? (value-binding-variable value-binding)
			 (variable-access-expression-variable e)))
		   value-bindings)))
	((application? e)
	 (call (loop (application-callee e) value-bindings)
	       (loop (application-argument e) value-bindings)))
	((lambda-expression? e) (make-closure value-bindings e))
	((if-expression? e)
	 (let ((antecedent (loop (if-expression-antecedent e) value-bindings)))
	  (unless (boolean? antecedent) (panic "Antecedent is not boolean"))
	  (if antecedent
	      (loop (if-expression-consequent e) value-bindings)
	      (loop (if-expression-alternate e) value-bindings))))
	((cons-expression? e)
	 (cons (loop (cons-expression-car-argument e) value-bindings)
	       (loop (cons-expression-cdr-argument e) value-bindings)))
	(else (fuck-up)))))

(define (define-primitive-basis-constant
	 variable procedure forward-value reverse-value)
 (set! *basis-constants* (cons variable *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding
	      variable (make-variable-access-expression variable))
	     *variable-bindings*))
 (set! *value-bindings*
       (cons (make-value-binding
	      variable
	      (make-primitive-function procedure forward-value reverse-value))
	     *value-bindings*)))

(define (define-basis-constant variable expression)
 (set! *basis-constants* (cons variable *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding
	      variable (make-variable-access-expression variable))
	     *variable-bindings*))
 (set! *value-bindings*
       (cons (make-value-binding variable (make-closure '() expression))
	     *value-bindings*)))

(define (initialize-basis!)
 (define-primitive-basis-constant
  '+
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to +"))
   (+ (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute))
    (cons (+ x1 x2) (+ x1-acute x2-acute)))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (+ x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons y-grave 0)) (x2-tilde (cons 0 y-grave)))))))
 (define-primitive-basis-constant
  '-
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to -"))
   (- (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute))
    (cons (- x1 x2) (- x1-acute x2-acute)))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons
     (- x1 x2)
     (lambda (y-grave)
      (plus (x1-tilde (cons y-grave 0)) (x2-tilde (cons 0 (- 0 y-grave))))))))
 (define-primitive-basis-constant
  '*
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to *"))
   (* (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute))
    (cons (* x1 x2) (+ (* x2 x1-acute) (* x1 x2-acute))))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (* x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons (* x2 y-grave) 0))
		 (x2-tilde (cons 0 (* x1 y-grave))))))))
 (define-primitive-basis-constant
  '/
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to /"))
   (/ (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute))
    (cons (/ x1 x2) (/ (- (* x2 x1-acute) (* x1 x2-acute)) (* x2 x2))))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (/ x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons (/ y-grave x2) 0))
		 (x2-tilde (cons 0 (- 0 (/ (* x1 y-grave) (* x2 x2))))))))))
 (define-primitive-basis-constant
  'sqrt
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to sqrt"))
   (sqrt x))
  '(lambda (x x-acute) (cons (sqrt x) (/ x-acute (* 2 (sqrt x)))))
  '(lambda (x x-tilde)
    (cons (sqrt x) (lambda (y-grave) (x-tilde (/ y-grave (* 2 (sqrt x))))))))
 (define-primitive-basis-constant
  'exp
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to exp"))
   (exp x))
  '(lambda (x x-acute) (cons (exp x) (* (exp x) x-acute)))
  '(lambda (x x-tilde)
    (cons (exp x) (lambda (y-grave) (x-tilde (* (exp x) y-grave))))))
 (define-primitive-basis-constant
  'log
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to log"))
   (log x))
  '(lambda (x x-acute) (cons (log x) (/ x-acute x)))
  '(lambda (x x-tilde)
    (cons (log x) (lambda (y-grave) (x-tilde (/ y-grave x))))))
 (define-primitive-basis-constant
  'sin
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to sin"))
   (sin x))
  '(lambda (x x-acute) (cons (sin x) (* (cos x) x-acute)))
  '(lambda (x x-tilde)
    (cons (sin x) (lambda (y-grave) (x-tilde (* (cos x) y-grave))))))
 (define-primitive-basis-constant
  'cos
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to cos"))
   (cos x))
  '(lambda (x x-acute) (cons (cos x) (- 0 (* (sin x) x-acute))))
  '(lambda (x x-tilde)
    (cons (cos x) (lambda (y-grave) (x-tilde (- 0 (* (sin x) y-grave)))))))
 (define-primitive-basis-constant
  'atan
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to atan"))
   (atan (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute))
    (cons (atan x2 x1)
	  (/ (- (* x1 x2-acute) (* x2 x1-acute)) (+ (* x1 x1) (* x2 x2)))))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (atan x2 x1)
	  (lambda (y-grave)
	   (plus (x1-tilde
		  (cons (- 0 (/ (* x2 y-grave) (+ (* x1 x1) (* x2 x2)))) 0))
		 (x2-tilde
		  (cons 0 (/ (* x1 y-grave) (+ (* x1 x1) (* x2 x2))))))))))
 (define-primitive-basis-constant
  '=
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to ="))
   (= (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute)) (cons (= x1 x2) unit))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (= x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons 0 0)) (x2-tilde (cons 0 0)))))))
 (define-primitive-basis-constant
  '<
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to <"))
   (< (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute)) (cons (< x1 x2) unit))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (< x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons 0 0)) (x2-tilde (cons 0 0)))))))
 (define-primitive-basis-constant
  '>
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to >"))
   (> (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute)) (cons (> x1 x2) unit))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (> x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons 0 0)) (x2-tilde (cons 0 0)))))))
 (define-primitive-basis-constant
  '<=
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to <="))
   (<= (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute)) (cons (<= x1 x2) unit))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (<= x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons 0 0)) (x2-tilde (cons 0 0)))))))
 (define-primitive-basis-constant
  '>=
  (lambda (x)
   (unless (and (pair? x) (number? (car x)) (number? (cdr x)))
    (panic "Invalid argument to >="))
   (>= (car x) (cdr x)))
  '(lambda ((cons x1 x1-acute) (cons x2 x2-acute)) (cons (>= x1 x2) unit))
  '(lambda ((cons x1 x1-tilde) (cons x2 x2-tilde))
    (cons (>= x1 x2)
	  (lambda (y-grave)
	   (plus (x1-tilde (cons 0 0)) (x2-tilde (cons 0 0)))))))
 (define-primitive-basis-constant
  'zero?
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to zero?"))
   (zero? x))
  '(lambda (x x-acute) (cons (zero? x) unit))
  '(lambda (x x-tilde) (cons (zero? x) (lambda (y-grave) (x-tilde 0)))))
 (define-primitive-basis-constant
  'positive?
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to positive?"))
   (positive? x))
  '(lambda (x x-acute) (cons (positive? x) unit))
  '(lambda (x x-tilde) (cons (positive? x) (lambda (y-grave) (x-tilde 0)))))
 (define-primitive-basis-constant
  'negative?
  (lambda (x)
   (unless (number? x) (panic "Invalid argument to negative?"))
   (negative? x))
  '(lambda (x x-acute) (cons (negative? x) unit))
  '(lambda (x x-tilde) (cons (negative? x) (lambda (y-grave) (x-tilde 0)))))
 (define-primitive-basis-constant
  'unit?
  (lambda (x) (eq? x 'unit))
  '(lambda (x) (cons (if (pair? x) (unit? (car x)) #f) unit))
  '(lambda (x)
    (cons (if (pair? x) (unit? (car x)) #f)
	  (lambda (y-grave) (map-plus x)))))
 (define-primitive-basis-constant
  'boolean?
  (lambda (x) (boolean? x))
  '(lambda (x) (cons (if (pair? x) (boolean? (car x)) #f) unit))
  '(lambda (x)
    (cons (if (pair? x) (boolean? (car x)) #f)
	  (lambda (y-grave) (map-plus x)))))
 (define-primitive-basis-constant
  'number?
  (lambda (x) (number? x))
  '(lambda (x) (cons (if (pair? x) (number? (car x)) #f) unit))
  '(lambda (x)
    (cons (if (pair? x) (number? (car x)) #f)
	  (lambda (y-grave) (map-plus x)))))
 (define-primitive-basis-constant
  'pair?
  (lambda (x) (pair? x))
  '(lambda (x)
    (cons (if (pair? x)
	      (cond ((unit? (car x)) #f)
		    ((boolean? (car x)) #f)
		    ((number? (car x)) #f)
		    (else #t))
	      #f)
	  unit))
  '(lambda (x)
    (cons (if (pair? x)
	      (cond ((unit? (car x)) #f)
		    ((boolean? (car x)) #f)
		    ((number? (car x)) #f)
		    (else #t))
	      #f)
	  (lambda (y-grave) (map-plus x)))))
 (define-primitive-basis-constant
  'function?
  (lambda (x) (or (primitive-function? x) (closure? x)))
  '(lambda (x) (cons (if (pair? x) #f #t) unit))
  '(lambda (x) (cons (if (pair? x) #f #t) (lambda (y-grave) (map-plus x)))))
 (define-primitive-basis-constant
  'car
  (lambda (x)
   (unless (pair? x) (panic "Invalid argument to car"))
   (car x))
  '(lambda (x) (car x))
  '(lambda (x)
    (map (lambda (x-tilde)
	  (lambda (y-grave) (x-tilde (cons y-grave (zero (cdr x))))))
	 (car x))))
 (define-primitive-basis-constant
  'cdr
  (lambda (x)
   (unless (pair? x) (panic "Invalid argument to cdr"))
   (cdr x))
  '(lambda (x) (cdr x))
  '(lambda (x)
    (map (lambda (x-tilde)
	  (lambda (y-grave) (x-tilde (cons (zero (car x)) y-grave))))
	 (cdr x))))
 (define-primitive-basis-constant
  'j-forward
  j-forward
  '(lambda (x) (j-forward (j-forward x)))
  '(lambda (x) (j-reverse (j-forward x))))
 (define-primitive-basis-constant
  'j-reverse
  j-reverse
  '(lambda (x) (j-forward (j-reverse x)))
  '(lambda (x) (j-reverse (j-reverse x))))
 (define-basis-constant
  'y
  '(lambda (f)
    ((lambda (g) (lambda (x) ((f (g g)) x)))
     (lambda (g) (lambda (x) ((f (g g)) x))))))
 (define-basis-constant
  ;; plus is used on the results of backpropagators. The input will always be
  ;; a pair of same-shape trees. Each tree will only contain nulls, numbers,
  ;; pairs, and functions.
  'plus
  '(lambda (x1 x2)
    ((y (lambda (plus)
	 (lambda (x1 x2)
	  (cond ((unit? x1) unit)
		((number? x1) (+ x1 x2))
		((pair? x1)
		 (cons (plus (car x1) (car x2))
		       (plus (cdr x1) (cdr x2))))
		(else (lambda (y) (plus (x1 y) (x2 y))))))))
     x1 x2)))
 (define-basis-constant
  ;; zero is used on reverse conjoint values.
  'zero
  '(lambda (x)
    ((y (lambda (zero)
	 (lambda (x)
	  (if (pair? x)
	      (cond ((unit? (car x)) unit)
		    ((boolean? (car x)) unit)
		    ((number? (car x)) 0)
		    (else (cons (zero (car x)) (zero (cdr x)))))
	      zero))))
     x)))
 (define-basis-constant
  ;; map is used on reverse conjoint values.
  'map
  '(lambda (f)
    (lambda (x)
     ((y (lambda (map)
	  (lambda (x)
	   (if (pair? x)
	       (cond ((unit? (car x)) (cons (car x) (f (cdr x))))
		     ((boolean? (car x)) (cons (car x) (f (cdr x))))
		     ((number? (car x)) (cons (car x) (f (cdr x))))
		     (else (cons (map (car x)) (map (cdr x)))))
	       (lambda (y) (map (x y)))))))
      x))))
 (define-basis-constant
  ;; map-plus is used on reverse conjoint values.
  'map-plus
  '(lambda (x)
    ((y (lambda (map-plus)
	 (lambda (x)
	  (if (pair? x)
	      (cond ((unit? (car x)) ((cdr x) unit))
		    ((boolean? (car x)) ((cdr x) unit))
		    ((number? (car x)) ((cdr x) 0))
		    (else (plus (map-plus (car x)) (map-plus (cdr x)))))
	      (lambda (y) (map-plus (x y)))))))
     x)))
 (for-each
  (lambda (value-binding)
   (let ((value (value-binding-value value-binding)))
    (cond
     ((primitive-function? value)
      (syntax-check-expression! (primitive-function-forward-value value))
      (set-primitive-function-forward-value!
       value
       (make-closure *value-bindings*
		     (concrete->abstract-expression
		      (primitive-function-forward-value value))))
      (syntax-check-expression! (primitive-function-reverse-value value))
      (set-primitive-function-reverse-value!
       value
       (make-closure *value-bindings*
		     (concrete->abstract-expression
		      (primitive-function-reverse-value value))))
      (set-closure-value-bindings! (primitive-function-reverse-value value)
				   *value-bindings*))
     ((closure? value)
      (syntax-check-expression! (closure-lambda-expression value))
      (set-closure-lambda-expression!
       value (concrete->abstract-expression (closure-lambda-expression value)))
      (set-closure-value-bindings! value *value-bindings*))
     (else (fuck-up)))))
  *value-bindings*))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
