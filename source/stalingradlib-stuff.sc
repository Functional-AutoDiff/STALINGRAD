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

;;; To do:
;;;  1. type inference
;;;  2. evaluator
;;;  3. let, let*, cond

;;; Key
;;;  e: concrete or abstract expression
;;;  t: concrete or abstract type
;;;  p: concrete or abstract parameter
;;;  l: list
;;;  x: concrete variable
;;;  a: concrete or abstract type variable
;;;  i: index

;;; Macros

;;; Structures

(define-structure type-variable type)

(define-structure function-type parameter-type result-type)

(define-structure cons-type car-type cdr-type)

(define-structure cons-parameter car-parameter cdr-parameter type)

(define-structure variable-parameter variable type)

(define-structure constant-expression value type)

(define-structure variable-access-expression lambda-expression path type)

(define-structure application callee argument type)

(define-structure lambda-expression parameter body type)

(define-structure if-expression antecedent consequent alternate type)

(define-structure car-expression argument type)

(define-structure cdr-expression argument type)

(define-structure cons-expression car-argument cdr-argument type)

(define-structure y-expression argument type)

(define-structure binding variable lambda-expression path)

(define-structure type-binding concrete abstract)

;;; Variables

;;; Parameters

;;; Procedures

(define (parameter-type e)
 (cond ((cons-parameter? e) (cons-parameter-type e))
       ((variable-parameter? e) (variable-parameter-type e))
       (else (fuck-up))))

(define (expression-type e)
 (cond ((constant-expression? e) (constant-expression-type e))
       ((variable-access-expression? e) (variable-access-expression-type e))
       ((application? e) (application-type e))
       ((lambda-expression? e) (lambda-expression-type e))
       ((if-expression? e) (if-expression-type e))
       ((car-expression? e) (car-expression-type e))
       ((cdr-expression? e) (cdr-expression-type e))
       ((cdr-expression? e) (cdr-expression-type e))
       ((cons-expression? e) (cons-expression-type e))
       ((y-expression? e) (y-expression-type e))
       (else (fuck-up))))

(define (syntax-check-type! t)
 (cond ((eq? t 'boolean) #f)
       ((eq? t 'real) #f)
       ((and (list? t) (not (null? t)))
	(case (first t)
	 ((quote)
	  (unless (and (= (length t) 2) (symbol? (second t)))
	   (panic (format #f "Invalid type: ~s" t)))
	  #f)
	 ((=>)
	  (unless (= (length t) 3) (panic (format #f "Invalid type: ~s" t)))
	  (syntax-check-type! (second t))
	  (syntax-check-type! (third t)))
	 ((cons)
	  (unless (= (length t) 3) (panic (format #f "Invalid type: ~s" t)))
	  (syntax-check-type! (second t))
	  (syntax-check-type! (third t)))
	 (else (panic (format #f "Invalid type: ~s" t)))))
       (else (panic (format #f "Invalid type: ~s" t)))))

(define (syntax-check-parameter! p)
 (cond
  ((symbol? p)
   (when (memq p '(: lambda if car cdr cons y))
    (panic (format #f "Invalid variable: ~s" p)))
   #f)
  ((and (list? p) (not (null? p)))
   (case (first p)
    ((:)
     (unless (= (length p) 3) (panic (format #f "Invalid parameter: ~s" p)))
     (syntax-check-parameter! (second p))
     (syntax-check-type! (third p)))
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
    ((:) (parameter-variables (second p)))
    ((cons)
     (append (parameter-variables (second p)) (parameter-variables (third p))))
    (else (fuck-up))))
  (else (fuck-up))))

(define (duplicatesq? l)
 (and (not (null? l)) (or (memq (first l) (rest l)) (duplicatesq? (rest l)))))

(define (syntax-check-expression! e xs)
 (cond
  ((boolean? e) #f)
  ((number? e) #f)
  ((symbol? e)
   (unless (memq e xs)
    (panic (format #f "Unbound variable: ~s" e)))
   #f)
  ((and (list? e) (not (null? e)))
   (case (first e)
    ((:)
     (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs)
     (syntax-check-type! (third e)))
    ((lambda)
     (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-parameter! (second e))
     (let ((xs0 (parameter-variables (second e))))
      (when (duplicatesq? xs0)
       (panic (format #f "Duplicate variables: ~s" (second e))))
      (syntax-check-expression! (third e) (append xs0 xs))))
    ((if)
     (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs)
     (syntax-check-expression! (third e) xs)
     (syntax-check-expression! (fourth e) xs))
    ((car)
     (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs))
    ((cdr)
     (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs))
    ((cons)
     (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs)
     (syntax-check-expression! (third e) xs))
    ((y)
     (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs))
    (else
     (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
     (syntax-check-expression! (second e) xs)
     (syntax-check-expression! (third e) xs))))
  (else (panic (format #f "Invalid expression: ~s" e)))))

(define (create-type-variable)
 (let ((a (make-type-variable #f)))
  (set-type-variable-type! a a)
  a))

(define (bound? a) (not (eq? (type-variable-type? a) a)))

(define (abstract-type-variables-in t)
 (cond ((eq? t 'boolean) '())
       ((eq? t 'real) '())
       ((type-variable? t)
	(if (bound? t)
	    (abstract-type-variables-in (type-variable-type t))
	    (list t)))
       ((function-type? t)
	(unionq (abstract-type-variables-in (function-type-parameter-type t))
		(abstract-type-variables-in (function-type-result-type t))))
       ((cons-type? t)
	(unionq (abstract-type-variables-in (cons-type-car-type t))
		(abstract-type-variables-in (cons-type-cdr-type t))))
       (else (fuck-up))))

(define (abstract->concrete-type t)
 (let ((type-bindings
	(map-indexed (lambda (a i)
		      (make-type-binding
		       ;; There can be at most 26 concrete type variables.
		       (string->symbol
			(string (integer->char (+ (char->integer #\A) i))))
		       a))
		     (abstract-type-variables-in t))))
  (let loop ((t t))
   (cond ((eq? t 'boolean) 'boolean)
	 ((eq? t 'real) 'real)
	 ((type-variable? t)
	  (if (bound? t)
	      (loop (type-variable-type t))
	      `',(type-binding-concrete
		  (find-if (lambda (type-binding)
			    (eq? (type-binding-abstract type-binding) t))
			   type-bindings))))
	 ((function-type? t)
	  `(=> ,(loop (function-type-parameter-type t))
	       ,(loop (function-type-result-type t))))
	 ((cons-type? t)
	  `(cons ,(loop (cons-type-car-type t))
		 ,(loop (cons-type-cdr-type t))))
	 (else (fuck-up))))))

(define (abstract->undecorated-concrete-parameter p)
 (cond ((cons-parameter? p)
	`(cons ,(abstract->undecorated-concrete-parameter
		 (cons-parameter-car-parameter p))
	       ,(abstract->undecorated-concrete-parameter
		 (cons-parameter-cdr-parameter p))))
       ;; This assumes that no manipulation can cause capture.
       ((variable-parameter? p) (variable-parameter-variable p))
       (else (fuck-up))))

(define (abstract->decorated-concrete-parameter p)
 `(: ,(cond ((cons-parameter? p)
	     `(cons ,(abstract->decorated-concrete-parameter
		      (cons-parameter-car-parameter p))
		    ,(abstract->decorated-concrete-parameter
		      (cons-parameter-cdr-parameter p))))
	    ;; This assumes that no manipulation can cause capture.
	    ((variable-parameter? p) (variable-parameter-variable p))
	    (else (fuck-up)))
     ,(abstract->concrete-type (parameter-type p))))

(define (abstract->undecorated-concrete-expression e)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e)
   ;; This assumes that no manipulation can cause capture.
   (let loop ((p (lambda-expression-parameter
		  (variable-access-expression-lambda-expression e)))
	      (path (variable-access-expression-path e)))
    (if (null? path)
	parameter
	(case (first path)
	 ((car) (loop (cons-parameter-car-parameter p) (rest path)))
	 ((cdr) (loop (cons-parameter-cdr-parameter p) (rest path)))
	 (else (fuck-up))))))
  ((application? e)
   `(,(abstract->undecorated-concrete-expression (application-callee e))
     ,(abstract->undecorated-concrete-expression (application-argument e))))
  ((lambda-expression? e)
   `(lambda ,(abstract->undecorated-concrete-parameter
	      (lambda-expression-parameter e))
     ,(abstract->undecorated-concrete-expression (lambda-expression-body e))))
  ((if-expression? e)
   `(if ,(abstract->undecorated-concrete-parameter
	  (if-expression-antecedent e))
	,(abstract->undecorated-concrete-parameter
	  (if-expression-consequent e))	
	,(abstract->undecorated-concrete-parameter
	  (if-expression-alternate e))))
  ((car-expression? e)
   `(car ,(abstract->undecorated-concrete-parameter
	   (car-expression-argument e))))
  ((cdr-expression? e)
   `(cdr ,(abstract->undecorated-concrete-parameter
	   (cdr-expression-argument e))))
  ((cons-expression? e)
   `(cons ,(abstract->undecorated-concrete-parameter
	    (cons-expression-car-argument e))
	  ,(abstract->undecorated-concrete-parameter
	    (cons-expression-cdr-argument e))))
  ((y-expression? e)
   `(y ,(abstract->undecorated-concrete-parameter
	 (y-expression-argument e))))
  (else (fuck-up))))

(define (abstract->decorated-concrete-expression e)
 `(: ,(cond
       ((constant-expression? e) (constant-expression-value e))
       ((variable-access-expression? e)
	;; This assumes that no manipulation can cause capture.
	(let loop ((p (lambda-expression-parameter
		       (variable-access-expression-lambda-expression e)))
		   (path (variable-access-expression-path e)))
	 (if (null? path)
	     parameter
	     (case (first path)
	      ((car) (loop (cons-parameter-car-parameter p) (rest path)))
	      ((cdr) (loop (cons-parameter-cdr-parameter p) (rest path)))
	      (else (fuck-up))))))
       ((application? e)
	`(,(abstract->decorated-concrete-expression (application-callee e))
	  ,(abstract->decorated-concrete-expression (application-argument e))))
       ((lambda-expression? e)
	`(lambda ,(abstract->decorated-concrete-parameter
		   (lambda-expression-parameter e))
	  ,(abstract->decorated-concrete-expression
	    (lambda-expression-body e))))
       ((if-expression? e)
	`(if ,(abstract->decorated-concrete-parameter
	       (if-expression-antecedent e))
	     ,(abstract->decorated-concrete-parameter
	       (if-expression-consequent e))	
	     ,(abstract->decorated-concrete-parameter
	       (if-expression-alternate e))))
       ((car-expression? e)
	`(car ,(abstract->decorated-concrete-parameter
		(car-expression-argument e))))
       ((cdr-expression? e)
	`(cdr ,(abstract->decorated-concrete-parameter
		(cdr-expression-argument e))))
       ((cons-expression? e)
	`(cons ,(abstract->decorated-concrete-parameter
		 (cons-expression-car-argument e))
	       ,(abstract->decorated-concrete-parameter
		 (cons-expression-cdr-argument e))))
       ((y-expression? e)
	`(y ,(abstract->decorated-concrete-parameter
	      (y-expression-argument e))))
       (else (fuck-up)))
     ,(abstract->concrete-type (expression-type e))))

(define (concrete-type-variables-in t)
 (cond ((eq? t 'boolean) '())
       ((eq? t 'real) '())
       ((list? t)
	(case (first t)
	 ((quote) (list (second t)))
	 ((=>) (unionq (concrete-type-variables-in (second t))
		       (concrete-type-variables-in (third t))))
	 ((cons) (unionq (concrete-type-variables-in (second t))
			 (concrete-type-variables-in (third t))))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (occurs? a t)
 (or (eq? a t)
     (and (type-variable? t)
	  (bound? t)
	  (occurs? a (type-variable-type t)))
     (and (function-type? t)
	  (or (occurs? a (function-type-parameter-type t))
	      (occurs? a (function-type-result-type t))))
     (and (cons-type? t)
	  (or (occurs? a (cons-type-car-type t))
	      (occurs? a (cons-type-cdr-type t))))))

(define (unify! t1 t2)
 (cond ((type-variable? t1)
	(cond ((bound? t1) (unify! (type-variable-type t1) t2))
	      (else (when (occurs? t1 t2)
		     (format #f "Cannot unify types: ~s and: ~s"
			     (abstract->concrete-type t1)
			     (abstract->concrete-type t2)))
		    (set-type-variable-type! t1 t2))))
       ((type-variable? t2)
	(cond ((bound? t2) (unify! t1 (type-variable-type t2)))
	      (else (when (occurs? t2 t1)
		     (format #f "Cannot unify types: ~s and: ~s"
			     (abstract->concrete-type t1)
			     (abstract->concrete-type t2)))
		    (set-type-variable-type! t2 t1))))
       ((and (eq? t1 'boolean) (eq? t2 'boolean)) #f)
       ((and (eq? t1 'real) (eq? t2 'real)) #f)
       ((and (function-type? t1) (function-type? t2))
	(unify! (function-type-parameter-type t1)
		(function-type-parameter-type t2))
	(unify! (function-type-result-type t1)
		(function-type-result-type t2)))
       ((and (cons-type? t1) (cons-type? t2))
	(unify! (cons-type-car-type t1) (cons-type-car-type t2))
	(unify! (cons-type-cdr-type t1) (cons-type-cdr-type t2)))
       (else (panic (format #f "Cannot unify types: ~s and: ~s"
			    (abstract->concrete-type t1)
			    (abstract->concrete-type t2))))))

(define (concrete->abstract-type t)
 (let ((type-bindings
	(map (lambda (a) (make-type-binding a (create-type-variable)))
	     (concrete-type-variables-in t))))
  (let loop ((t t))
   (cond ((eq? t 'boolean) 'boolean)
	 ((eq? t 'real) 'real)
	 ((list? t)
	  (case (first t)
	   ((quote)
	    (type-binding-abstract
	     (find-if (lambda (type-binding)
		       (eq? (type-binding-concrete type-binding) (second t)))
		      type-bindings)))
	   ((=>) (make-function-type (loop (second t)) (loop (third t))))
	   ((cons) (make-cons-type (loop (second t)) (loop (third t))))
	   (else (fuck-up))))
	 (else (fuck-up))))))

(define (concrete->abstract-parameter p)
 (cond ((symbol? p) (make-variable-parameter p (create-type-variable)))
       ((list? p)
	(case (first p)
	 ((:) (let ((p0 (concrete->abstract-parameter (second p))))
	       (unify! (parameter-type p0)
		       (concrete->abstract-type (third p)))
	       p0))
	 ((cons) (make-cons-parameter
		  (concrete->abstract-parameter (second p))
		  (concrete->abstract-parameter (third p))
		  (create-type-variable)))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (parameter-bindings p e path)
 (cond
  ((variable-parameter? p)
   (list (make-binding (variable-parameter-variable p) e path)))
  ((cons-parameter? p)
   (append
    (parameter-bindings (cons-parameter-car-parameter p) e (cons 'car path))
    (parameter-bindings (cons-parameter-cdr-parameter p) e (cons 'cdr path))))
  (else (fuck-up))))

(define (concrete->abstract-expression e bindings)
 (cond ((boolean? e) (make-constant-expression e (create-type-variable)))
       ((number? e) (make-constant-expression e (create-type-variable)))
       ((symbol? e)
	(let ((binding
	       (find-if (lambda (binding) (eq? (binding-variable binding) e))
			bindings)))
	 (make-variable-access-expression
	  (binding-lambda-expression binding)
	  (binding-path binding)
	  (create-type-variable))))
       ((list? e)
	(case (first e)
	 ((:) (let ((e0 (concrete->abstract-expression (second e) bindings)))
	       (unify! (expression-type e0)
		       (concrete->abstract-type (third e)))
	       e0))
	 ((lambda)
	  (let ((e0 (make-lambda-expression
		     (concrete->abstract-parameter (second e))
		     #f
		     (create-type-variable))))
	   (set-lambda-expression-body!
	    e0
	    (concrete->abstract-expression
	     (third e)
	     (append
	      (parameter-bindings (lambda-expression-parameter e0) e0 '())
	      bindings)))
	   e0))
	 ((if) (make-if-expression
		(concrete->abstract-expression (second e) binding)
		(concrete->abstract-expression (third e) bindings)
		(concrete->abstract-expression (fourth e) bindings)
		(create-type-variable)))
	 ((car) (make-car-expression
		 (concrete->abstract-expression (second e) bindings)
		 (create-type-variable)))
	 ((cdr) (make-cdr-expression
		 (concrete->abstract-expression (second e) bindings)
		 (create-type-variable)))
	 ((cons) (make-cons-expression
		  (concrete->abstract-expression (second e) bindings)
		  (concrete->abstract-expression (third e) bindings)
		  (create-type-variable)))
	 ((y) (make-y-expression
	       (concrete->abstract-expression (second e) bindings)
	       (create-type-variable)))
	 (else (make-application
		(concrete->abstract-expression (first e) bindings)
		(concrete->abstract-expression (second e) bindings)
		(create-type-variable)))))
       (else (fuck-up))))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
