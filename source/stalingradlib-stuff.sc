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
;;;  1. the value restriction or whatever it is called
;;;  2. scoping of concrete type variables is screwed up
;;;  3. datatypes
;;;  4. reflective API

;;; Key
;;;  e: concrete or abstract expression
;;;  t: concrete or abstract type
;;;  p: concrete or abstract parameter
;;;  l: list
;;;  x: concrete variable
;;;  a: concrete or abstract type variable
;;;  i: index
;;;  b: blah blah blah

;;; Macros

;;; Structures

(define-structure type-variable type)

(define-structure function-type parameter-type result-type)

(define-structure cons-type car-type cdr-type)

(define-structure cons-parameter car-parameter cdr-parameter type)

(define-structure variable-parameter variable type)

(define-structure constant-expression value type)

(define-structure variable-access-expression binding-expression path type)

(define-structure application callee argument type)

(define-structure lambda-expression parameter body type)

(define-structure let-expression
 parameter quantified-type-variables expression body type)

(define-structure if-expression antecedent consequent alternate type)

(define-structure cons-expression car-argument cdr-argument type)

(define-structure parameter-binding parameter binding-expression path)

(define-structure type-binding concrete abstract)

(define-structure instantiate-binding old new)

(define-structure value-binding binding-expression value)

(define-structure basis-constant name value type)

;;; Variables

(define *basis-constants* '())

(define *parameter-bindings* '())

(define *value-bindings* '())

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
       ((let-expression? e) (let-expression-type e))
       ((if-expression? e) (if-expression-type e))
       ((cons-expression? e) (cons-expression-type e))
       (else (fuck-up))))

(define (binding-expression-parameter e)
 (cond ((lambda-expression? e) (lambda-expression-parameter e))
       ((let-expression? e) (let-expression-parameter e))
       (else (fuck-up))))

(define (binding-expression-quantified-type-variables e)
 (cond ((lambda-expression? e) '())
       ((let-expression? e) (let-expression-quantified-type-variables e))
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
   (when (memq p '(: lambda let* if cons y cond))
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

(define (syntax-check-expression! e)
 (let loop ((e e) (xs (map basis-constant-name *basis-constants*)))
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
      (loop (second e) xs)
      (syntax-check-type! (third e)))
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ;; needs work: To implement thunks.
       ((0) (panic (format #f "Thunks not (yet) implemented: ~s" e)))
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
       ((1)
	(syntax-check-parameter! (first (first (second e))))
	(loop (second (first (second e))) xs)
	(let ((xs0 (parameter-variables (first (first (second e))))))
	 (when (duplicatesq? xs0)
	  (panic
	   (format #f "Duplicate variables: ~s" (first (first (second e))))))
	 (loop (third e) (append xs0 xs))))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 xs))))
     ((if)
      (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs)
      (loop (third e) xs)
      (loop (fourth e) xs))
     ((car)
      (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs))
     ((cdr)
      (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs))
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
       ;; needs work: To implement thunks.
       ((0) (panic (format #f "Thunks not (yet) implemented: ~s" e)))
       ((1) (loop (first e) xs)
	    (loop (second e) xs))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (create-type-variable)
 (let ((a (make-type-variable #f)))
  (set-type-variable-type! a a)
  a))

(define (bound? a) (not (eq? (type-variable-type a) a)))

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
   (let loop ((p (binding-expression-parameter
		  (variable-access-expression-binding-expression e)))
	      (path (variable-access-expression-path e)))
    (if (null? path)
	(variable-parameter-variable p)
	(case (first path)
	 ((car) (loop (cons-parameter-car-parameter p) (rest path)))
	 ((cdr) (loop (cons-parameter-cdr-parameter p) (rest path)))
	 (else (fuck-up))))))
  ((application? e)
   `(,(abstract->undecorated-concrete-expression (application-callee e))
     ,(abstract->undecorated-concrete-expression (application-argument e))))
  ((lambda-expression? e)
   `(lambda (,(abstract->undecorated-concrete-parameter
	       (lambda-expression-parameter e)))
     ,(abstract->undecorated-concrete-expression (lambda-expression-body e))))
  ((let-expression? e)
   `(let* ((,(abstract->undecorated-concrete-parameter
	      (let-expression-parameter e))
	    ,(abstract->undecorated-concrete-expression
	      (let-expression-expression e))))
     ,(abstract->undecorated-concrete-expression (let-expression-body e))))
  ((if-expression? e)
   `(if ,(abstract->undecorated-concrete-expression
	  (if-expression-antecedent e))
	,(abstract->undecorated-concrete-expression
	  (if-expression-consequent e))	
	,(abstract->undecorated-concrete-expression
	  (if-expression-alternate e))))
  ((cons-expression? e)
   `(cons ,(abstract->undecorated-concrete-expression
	    (cons-expression-car-argument e))
	  ,(abstract->undecorated-concrete-expression
	    (cons-expression-cdr-argument e))))
  (else (fuck-up))))

(define (abstract->decorated-concrete-expression e)
 `(: ,(cond
       ((constant-expression? e) (constant-expression-value e))
       ((variable-access-expression? e)
	;; This assumes that no manipulation can cause capture.
	(let loop ((p (binding-expression-parameter
		       (variable-access-expression-binding-expression e)))
		   (path (variable-access-expression-path e)))
	 (if (null? path)
	     (variable-parameter-variable p)
	     (case (first path)
	      ((car) (loop (cons-parameter-car-parameter p) (rest path)))
	      ((cdr) (loop (cons-parameter-cdr-parameter p) (rest path)))
	      (else (fuck-up))))))
       ((application? e)
	`(,(abstract->decorated-concrete-expression (application-callee e))
	  ,(abstract->decorated-concrete-expression (application-argument e))))
       ((lambda-expression? e)
	`(lambda (,(abstract->decorated-concrete-parameter
		    (lambda-expression-parameter e)))
	  ,(abstract->decorated-concrete-expression
	    (lambda-expression-body e))))
       ((let-expression? e)
	`(let* ((,(abstract->decorated-concrete-parameter
		   (let-expression-parameter e))
		 ,(abstract->decorated-concrete-expression
		   (let-expression-expression e))))
	  ,(abstract->decorated-concrete-expression (let-expression-body e))))
       ((if-expression? e)
	`(if ,(abstract->decorated-concrete-expression
	       (if-expression-antecedent e))
	     ,(abstract->decorated-concrete-expression
	       (if-expression-consequent e))	
	     ,(abstract->decorated-concrete-expression
	       (if-expression-alternate e))))
       ((cons-expression? e)
	`(cons ,(abstract->decorated-concrete-expression
		 (cons-expression-car-argument e))
	       ,(abstract->decorated-concrete-expression
		 (cons-expression-cdr-argument e))))
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
		     (format #f "Cannot unify types ~s and ~s"
			     (abstract->concrete-type t1)
			     (abstract->concrete-type t2)))
		    (set-type-variable-type! t1 t2))))
       ((type-variable? t2)
	(cond ((bound? t2) (unify! t1 (type-variable-type t2)))
	      (else (when (occurs? t2 t1)
		     (format #f "Cannot unify types ~s and ~s"
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
       (else (panic (format #f "Cannot unify types ~s and ~s"
			    (abstract->concrete-type t1)
			    (abstract->concrete-type t2))))))

(define (instantiate as t)
 (let ((instantiate-bindings
	(map (lambda (a) (make-instantiate-binding a (create-type-variable)))
	     as)))
  (let loop ((t t))
   (cond ((eq? t 'boolean) t)
	 ((eq? t 'real) t)
	 ((type-variable? t)
	  (if (bound? t)
	      (loop (type-variable-type t))
	      (let ((instantiate-binding
		     (find-if
		      (lambda (instantiate-binding)
		       (eq? (instantiate-binding-old instantiate-binding) t))
		      instantiate-bindings)))
	       (if instantiate-binding
		   (instantiate-binding-new instantiate-binding)
		   t))))
	 ((function-type? t)
	  (make-function-type (loop (function-type-parameter-type t))
			      (loop (function-type-result-type t))))
	 ((cons-type? t)
	  (make-cons-type (loop (cons-type-car-type t))
			  (loop (cons-type-cdr-type t))))
	 (else (fuck-up))))))

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
	 ((:) (let ((p1 (concrete->abstract-parameter (second p))))
	       (unify! (parameter-type p1) (concrete->abstract-type (third p)))
	       p1))
	 ((cons)
	  (let ((p1 (concrete->abstract-parameter (second p)))
		(p2 (concrete->abstract-parameter (third p))))
	   (make-cons-parameter
	    p1 p2 (make-cons-type (parameter-type p1) (parameter-type p2)))))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (binding-expression-parameter-bindings e)
 (let loop ((p (binding-expression-parameter e)) (e e) (path '()))
  (cond
   ((variable-parameter? p) (list (make-parameter-binding p e path)))
   ((cons-parameter? p)
    (append (loop (cons-parameter-car-parameter p) e (append path '(car)))
	    (loop (cons-parameter-cdr-parameter p) e (append path '(cdr)))))
   (else (fuck-up)))))

(define (concrete->abstract-expression e)
 (let loop ((e e) (parameter-bindings *parameter-bindings*))
  (cond
   ((boolean? e) (make-constant-expression e 'boolean))
   ((number? e) (make-constant-expression e 'real))
   ((symbol? e)
    (let ((parameter-binding
	   (find-if (lambda (parameter-binding)
		     (eq? (variable-parameter-variable
			   (parameter-binding-parameter parameter-binding))
			  e))
		    parameter-bindings)))
     (make-variable-access-expression
      (parameter-binding-binding-expression parameter-binding)
      (parameter-binding-path parameter-binding)
      (instantiate (binding-expression-quantified-type-variables
		    (parameter-binding-binding-expression parameter-binding))
		   (variable-parameter-type
		    (parameter-binding-parameter parameter-binding))))))
   ((list? e)
    (case (first e)
     ((:) (let ((e1 (loop (second e) parameter-bindings)))
	   (unify! (expression-type e1) (concrete->abstract-type (third e)))
	   e1))
     ((lambda)
      (case (length (second e))
       ;; needs work: To implement thunks.
       ((0) (panic (format #f "Thunks not (yet) implemented: ~s" e)))
       ((1)
	(let* ((p (concrete->abstract-parameter (first (second e))))
	       (e-prime (make-lambda-expression p #f #f))
	       (e1 (loop
		    (third e)
		    (append (binding-expression-parameter-bindings e-prime)
			    parameter-bindings))))
	 (set-lambda-expression-body! e-prime e1)
	 (set-lambda-expression-type!
	  e-prime (make-function-type (parameter-type p) (expression-type e1)))
	 e-prime))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   parameter-bindings))))
     ((let*)
      (case (length (second e))
       ((0) (loop (third e) parameter-bindings))
       ((1)
	(let* ((e1 (loop (second (first (second e))) parameter-bindings))
	       (e-prime
		(make-let-expression
		 (concrete->abstract-parameter (first (first (second e))))
		 (set-differenceq
		  (abstract-type-variables-in (expression-type e1))
		  (reduce
		   unionq
		   (map (lambda (parameter-binding)
			 (abstract-type-variables-in
			  (parameter-type
			   (parameter-binding-parameter parameter-binding))))
			parameter-bindings)
		   '()))
		 e1
		 #f
		 #f)))
	 (unify! (parameter-type (binding-expression-parameter e-prime))
		 (expression-type e1))
	 (let ((e2 (loop
		    (third e)
		    (append (binding-expression-parameter-bindings e-prime)
			    parameter-bindings))))
	  (set-let-expression-body! e-prime e2)
	  (set-let-expression-type! e-prime (expression-type e2))
	  e-prime)))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 parameter-bindings))))
     ((if) (let ((e1 (loop (second e) parameter-bindings))
		 (e2 (loop (third e) parameter-bindings))
		 (e3 (loop (fourth e) parameter-bindings)))
	    (unify! (expression-type e1) 'boolean)
	    (unify! (expression-type e2) (expression-type e3))
	    (make-if-expression e1 e2 e3 (expression-type e3))))
     ((cons)
      (let ((e1 (loop (second e) parameter-bindings))
	    (e2 (loop (third e) parameter-bindings)))
       (make-cons-expression
	e1 e2 (make-cons-type (expression-type e1) (expression-type e2)))))
     ((cond) (loop (if (null? (rest (rest e)))
		       (second (second e))
		       `(if ,(first (second e))
			    ,(second (second e))
			    (cond ,@(rest (rest e)))))
		   parameter-bindings))
     (else
      (case (length (rest e))
       ;; needs work: To implement thunks.
       ((0) (panic (format #f "Thunks not (yet) implemented: ~s" e)))
       ((1) (let ((e1 (loop (first e) parameter-bindings))
		  (e2 (loop (second e) parameter-bindings))
		  (a (create-type-variable)))
	     (unify!
	      (expression-type e1) (make-function-type (expression-type e2) a))
	     (make-application e1 e2 a)))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 parameter-bindings))))))
   (else (fuck-up)))))

(define (evaluate e)
 (let loop ((e e) (value-bindings *value-bindings*))
  (cond
   ((constant-expression? e) (constant-expression-value e))
   ((variable-access-expression? e)
    (let loop ((path (variable-access-expression-path e))
	       (value
		(value-binding-value
		 (find-if
		  (lambda (value-binding)
		   (eq? (value-binding-binding-expression value-binding)
			(variable-access-expression-binding-expression e)))
		  value-bindings))))
     (if (null? path)
	 value
	 (loop (rest path)
	       (case (first path)
		((car) (car value))
		((cdr) (cdr value))
		(else (fuck-up)))))))
   ((application? e)
    ((loop (application-callee e) value-bindings)
     (loop (application-argument e) value-bindings)))
   ((lambda-expression? e)
    (lambda (value)
     (loop (lambda-expression-body e)
	   (cons (make-value-binding e value) value-bindings))))
   ((let-expression? e)
    (let ((value (loop (let-expression-expression e) value-bindings)))
     (loop (let-expression-body e)
	   (cons (make-value-binding e value) value-bindings))))
   ((if-expression? e)
    (if (loop (if-expression-antecedent e) value-bindings)
	(loop (if-expression-consequent e) value-bindings)
	(loop (if-expression-alternate e) value-bindings)))
   ((cons-expression? e)
    (cons (loop (cons-expression-car-argument e) value-bindings)
	  (loop (cons-expression-cdr-argument e) value-bindings)))
   (else (fuck-up)))))

(define (define-basis-constant name value t)
 (let* ((basis-constant
	 (make-basis-constant name value (concrete->abstract-type t)))
	(parameter
	 (make-variable-parameter (basis-constant-name basis-constant)
				  (basis-constant-type basis-constant)))
	(let-expression
	 (make-let-expression
	  parameter
	  (abstract-type-variables-in (basis-constant-type basis-constant))
	  #f
	  #f
	  #f)))
  (set! *basis-constants* (cons basis-constant *basis-constants*))
  (set! *parameter-bindings*
	(cons (make-parameter-binding parameter let-expression '())
	      *parameter-bindings*))
  (set! *value-bindings*
	(cons (make-value-binding
	       let-expression (basis-constant-value basis-constant))
	      *value-bindings*))))

(define (intialize-basis!)
 (define-basis-constant
  'y
  (lambda (f)
   ((lambda (g) (lambda (x) ((f (g g)) x)))
    (lambda (g) (lambda (x) ((f (g g)) x)))))
  '(=> (=> (=> 'a 'b) (=> 'a 'b)) (=> 'a 'b)))
 (define-basis-constant
  '+
  (lambda (x) (+ (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant
  '-
  (lambda (x) (- (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant
  '*
  (lambda (x) (* (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant
  '/
  (lambda (x) (/ (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant 'sqrt sqrt '(=> real real))
 (define-basis-constant 'exp exp '(=> real real))
 (define-basis-constant 'log log '(=> real real))
 (define-basis-constant
  'expt
  (lambda (x) (expt (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant 'sin sin '(=> real real))
 (define-basis-constant 'cos cos '(=> real real))
 (define-basis-constant
  'atan
  (lambda (x) (atan (car x) (cdr x)))
  '(=> (cons real real) real))
 (define-basis-constant
  '=
  (lambda (x) (= (car x) (cdr x)))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<
  (lambda (x) (< (car x) (cdr x)))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>
  (lambda (x) (> (car x) (cdr x)))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<=
  (lambda (x) (<= (car x) (cdr x)))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>=
  (lambda (x) (>= (car x) (cdr x)))
  '(=> (cons real real) boolean))
 (define-basis-constant 'zero? zero? '(=> real boolean))
 (define-basis-constant 'positive? positive? '(=> real boolean))
 (define-basis-constant 'negative? negative? '(=> real boolean)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
