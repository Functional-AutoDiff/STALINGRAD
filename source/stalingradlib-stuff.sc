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

(define-structure type-variable type differentiations clone)

(define-structure function-type parameter-type result-type)

(define-structure cons-type car-type cdr-type)

(define-structure variable-parameter variable type)

(define-structure cons-parameter car-parameter cdr-parameter type)

(define-structure constant-expression value type)

(define-structure variable-access-expression variable type)

(define-structure application callee argument type)

(define-structure lambda-expression parameter body type)

(define-structure let-expression parameter expression body type)

(define-structure if-expression antecedent consequent alternate type)

(define-structure cons-expression car-argument cdr-argument type)

(define-structure variable-binding variable type quantified-type-variables)

(define-structure type-binding concrete abstract)

(define-structure instantiate-binding old new)

(define-structure value-binding variable value)

(define-structure closure value-bindings lambda-expression)

(define-structure primitive-function procedure forward-value)

;;; Variables

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

;;; Parameters

;;; Procedures

(define (parameter-type e)
 (cond ((variable-parameter? e) (variable-parameter-type e))
       ((cons-parameter? e) (cons-parameter-type e))
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

(define (syntax-check-type! t)
 (cond ((eq? t 'unit) #f)
       ((eq? t 'boolean) #f)
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
	 ((_>)
	  (unless (= (length t) 2) (panic (format #f "Invalid type: ~s" t)))
	  (syntax-check-type! (second t)))
	 (else (panic (format #f "Invalid type: ~s" t)))))
       (else (panic (format #f "Invalid type: ~s" t)))))

(define (syntax-check-parameter! p)
 (cond
  ((symbol? p)
   (when (memq p '(: lambda let* if cons cond else unit))
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
     ((:)
      (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
      (loop (second e) xs)
      (syntax-check-type! (third e)))
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop `(lambda ((: ,(gensym) unit)) ,(third e)) xs))
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
       ((0) (loop `(,(first e) unit) xs))
       ((1) (loop (first e) xs)
	    (loop (second e) xs))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (create-type-variable differentiations)
 (let ((a (make-type-variable #f differentiations #f)))
  (set-type-variable-type! a a)
  (set-type-variable-clone! a a)
  a))

(define (clone-type-variable a differentiations)
 (let loop ((a1 a))
  (cond ((equal? (type-variable-differentiations a1) differentiations) a1)
	((eq? (type-variable-clone a1) a)
	 (let ((a2 (make-type-variable #f differentiations #f)))
	  (set-type-variable-type! a2 a2)
	  (set-type-variable-clone! a2 a)
	  (set-type-variable-clone! a a2)
	  a2))
	(else (loop (type-variable-clone a1))))))

(define (bound? a) (not (eq? (type-variable-type a) a)))

(define (clones? a1 a2)
 (let loop ((a a1))
  (or (eq? a a2)
      (and (not (eq? (type-variable-clone a) a1))
	   (loop (type-variable-clone a))))))

(define (abstract-type-variables-in t)
 (cond ((eq? t 'unit) '())
       ((eq? t 'boolean) '())
       ((eq? t 'real) '())
       ((type-variable? t)
	(if (bound? t)
	    (abstract-type-variables-in (type-variable-type t))
	    (list t)))
       ((function-type? t)
	(unionp clones?
		(abstract-type-variables-in (function-type-parameter-type t))
		(abstract-type-variables-in (function-type-result-type t))))
       ((cons-type? t)
	(unionp clones?
		(abstract-type-variables-in (cons-type-car-type t))
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
   (cond
    ((eq? t 'unit) 'unit)
    ((eq? t 'boolean) 'boolean)
    ((eq? t 'real) 'real)
    ((type-variable? t)
     (if (bound? t)
	 (loop (type-variable-type t))
	 (let loop ((differentiations (type-variable-differentiations t)))
	  (if (null? differentiations)
	      `',(type-binding-concrete
		  (find-if (lambda (type-binding)
			    (clones? (type-binding-abstract type-binding) t))
			   type-bindings))
	      `(_> ,(loop (rest differentiations)))))))
    ((function-type? t)
     `(=> ,(loop (function-type-parameter-type t))
	  ,(loop (function-type-result-type t))))
    ((cons-type? t)
     `(cons ,(loop (cons-type-car-type t))
	    ,(loop (cons-type-cdr-type t))))
    (else (fuck-up))))))

(define (abstract->undecorated-concrete-parameter p)
 (cond ((variable-parameter? p) (variable-parameter-variable p))
       ((cons-parameter? p)
	`(cons ,(abstract->undecorated-concrete-parameter
		 (cons-parameter-car-parameter p))
	       ,(abstract->undecorated-concrete-parameter
		 (cons-parameter-cdr-parameter p))))
       (else (fuck-up))))

(define (abstract->decorated-concrete-parameter p)
 `(: ,(cond ((variable-parameter? p) (variable-parameter-variable p))
	    ((cons-parameter? p)
	     `(cons ,(abstract->decorated-concrete-parameter
		      (cons-parameter-car-parameter p))
		    ,(abstract->decorated-concrete-parameter
		      (cons-parameter-cdr-parameter p))))
	    (else (fuck-up)))
     ,(abstract->concrete-type (parameter-type p))))

(define (abstract->undecorated-concrete-expression e)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e) (variable-access-expression-variable e))
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
 `(:
   ,(cond
     ((constant-expression? e) (constant-expression-value e))
     ((variable-access-expression? e) (variable-access-expression-variable e))
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
 (cond ((eq? t 'unit) '())
       ((eq? t 'boolean) '())
       ((eq? t 'real) '())
       ((list? t)
	(case (first t)
	 ((quote) (list (second t)))
	 ((=>) (unionq (concrete-type-variables-in (second t))
		       (concrete-type-variables-in (third t))))
	 ((cons) (unionq (concrete-type-variables-in (second t))
			 (concrete-type-variables-in (third t))))
	 ((_>) (concrete-type-variables-in (second t)))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (occurs? a t)
 (or (eq? a t)
     (and (type-variable? t) (bound? t) (occurs? a (type-variable-type t)))
     (and (function-type? t)
	  (or (occurs? a (function-type-parameter-type t))
	      (occurs? a (function-type-result-type t))))
     (and (cons-type? t)
	  (or (occurs? a (cons-type-car-type t))
	      (occurs? a (cons-type-cdr-type t))))))

(define (unwind-differentiations t differentiations)
 (if (null? differentiations)
     t
     (case (first differentiations)
      ((_>)
       (unwind-differentiations (forwardize-type t) (rest differentiations)))
      (else (fuck-up)))))

(define (bind-all-clones! a t)
 (let loop ()
  (let ((again? #f))
   (let loop ((a1 a))
    (let ((t (unwind-differentiations
	      t (reverse (type-variable-differentiations a1)))))
     (unless (bound? a1)
      (set-type-variable-type! a1 t)
      (set! again? #t)))
    (unless (eq? (type-variable-clone a1) a) (loop (type-variable-clone a1))))
   (when again? (loop)))))

(define (share-all-clones! a1 a2)
 (let loop ()
  (let ((again? #f))
   (let loop ((a3 a1))
    (unless (bound? a2)
     (when (negative?
	    (+ (- (length (type-variable-differentiations a3))
		  (length (type-variable-differentiations a1)))
	       (length (type-variable-differentiations a2))))
      (fuck-up))
     (let ((a4 (clone-type-variable
		a2
		;; needs work: This is hardwired to forward mode.
		(map-n (lambda (i) '_>)
		       (+ (- (length (type-variable-differentiations a3))
			     (length (type-variable-differentiations a1)))
			  (length (type-variable-differentiations a2)))))))
      (unless (bound? a3)
       (set-type-variable-type! a3 a4)
       (set! again? #t))))
    (unless (eq? (type-variable-clone a3) a1) (loop (type-variable-clone a3))))
   (let loop ((a3 a2))
    (unless (bound? a1)
     (when (negative?
	    (+ (- (length (type-variable-differentiations a3))
		  (length (type-variable-differentiations a2)))
	       (length (type-variable-differentiations a1))))
      (fuck-up))
     (let ((a4 (clone-type-variable
		a1
		;; needs work: This is hardwired to forward mode.
		(map-n (lambda (i) '_>)
		       (+ (- (length (type-variable-differentiations a3))
			     (length (type-variable-differentiations a2)))
			  (length (type-variable-differentiations a1)))))))
      (unless (bound? a3)
       (set-type-variable-type! a3 a4)
       (set! again? #t))))
    (unless (eq? (type-variable-clone a3) a2) (loop (type-variable-clone a3))))
   (when again? (loop)))))

(define (unify! t1 t2)
 (cond
  ((type-variable? t1)
   (cond ((bound? t1) (unify! (type-variable-type t1) t2))
	 (else (when (occurs? t1 t2)
		(format #f "Cannot unify types ~s and ~s"
			(abstract->concrete-type t1)
			(abstract->concrete-type t2)))
	       (if (type-variable? t2)
		   (if (bound? t2)
		       (unify! t1 (type-variable-type t2))
		       (share-all-clones! t1 t2))
		   (bind-all-clones! t1 t2)))))
  ((type-variable? t2)
   (cond ((bound? t2) (unify! t1 (type-variable-type t2)))
	 (else (when (occurs? t2 t1)
		(format #f "Cannot unify types ~s and ~s"
			(abstract->concrete-type t1)
			(abstract->concrete-type t2)))
	       (bind-all-clones! t2 t1))))
  ((and (eq? t1 'unit) (eq? t2 'unit)) #f)
  ((and (eq? t1 'boolean) (eq? t2 'boolean)) #f)
  ((and (eq? t1 'real) (eq? t2 'real)) #f)
  ((and (function-type? t1) (function-type? t2))
   (unify! (function-type-parameter-type t1) (function-type-parameter-type t2))
   (unify! (function-type-result-type t1) (function-type-result-type t2)))
  ((and (cons-type? t1) (cons-type? t2))
   (unify! (cons-type-car-type t1) (cons-type-car-type t2))
   (unify! (cons-type-cdr-type t1) (cons-type-cdr-type t2)))
  (else (panic (format #f "Cannot unify types ~s and ~s"
		       (abstract->concrete-type t1)
		       (abstract->concrete-type t2))))))

(define (instantiate as t)
 (let ((instantiate-bindings
	(map (lambda (a)
	      (make-instantiate-binding
	       a (create-type-variable (type-variable-differentiations a))))
	     as)))
  (let loop ((t t))
   (cond
    ((eq? t 'unit) t)
    ((eq? t 'boolean) t)
    ((eq? t 'real) t)
    ((type-variable? t)
     (if (bound? t)
	 (loop (type-variable-type t))
	 (let ((instantiate-binding
		(find-if
		 (lambda (instantiate-binding)
		  (clones? (instantiate-binding-old instantiate-binding) t))
		 instantiate-bindings)))
	  (if instantiate-binding
	      (clone-type-variable
	       (instantiate-binding-new instantiate-binding)
	       (type-variable-differentiations t))
	      t))))
    ((function-type? t)
     (make-function-type (loop (function-type-parameter-type t))
			 (loop (function-type-result-type t))))
    ((cons-type? t)
     (make-cons-type (loop (cons-type-car-type t))
		     (loop (cons-type-cdr-type t))))
    (else (fuck-up))))))

(define (forwardize-type t)
 (cond
  ((eq? t 'unit) (make-cons-type 'unit 'unit))
  ((eq? t 'boolean) (make-cons-type 'boolean 'unit))
  ((eq? t 'real) (make-cons-type 'real 'real))
  ((type-variable? t)
   (if (bound? t)
       (forwardize-type (type-variable-type t))
       (clone-type-variable t (cons '_> (type-variable-differentiations t)))))
  ((function-type? t)
   (make-function-type (forwardize-type (function-type-parameter-type t))
		       (forwardize-type (function-type-result-type t))))
  ((cons-type? t)
   (make-cons-type (forwardize-type (cons-type-car-type t))
		   (forwardize-type (cons-type-cdr-type t))))
  (else (fuck-up))))

(define (concrete->abstract-type t)
 (let ((type-bindings
	(map (lambda (a) (make-type-binding a (create-type-variable '())))
	     (concrete-type-variables-in t))))
  (let loop ((t t))
   (cond ((eq? t 'unit) 'unit)
	 ((eq? t 'boolean) 'boolean)
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
	   ((_>) (forwardize-type (loop (second t))))
	   (else (fuck-up))))
	 (else (fuck-up))))))

(define (concrete->abstract-parameter p)
 (cond ((symbol? p) (make-variable-parameter p (create-type-variable '())))
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

(define (forwardize-parameter p)
 (cond
  ((variable-parameter? p)
   (make-variable-parameter (variable-parameter-variable p)
			    (forwardize-type (parameter-type p))))
  ((cons-parameter? p)
   (make-cons-parameter (forwardize-parameter (cons-parameter-car-parameter p))
			(forwardize-parameter (cons-parameter-cdr-parameter p))
			(forwardize-type (parameter-type p))))
  (else (fuck-up))))

(define (forwardize-expression e)
 (cond
  ((constant-expression? e)
   (make-constant-expression (j-forward (constant-expression-value e))
			     (forwardize-type (expression-type e))))
  ((variable-access-expression? e)
   (make-variable-access-expression (variable-access-expression-variable e)
				    (forwardize-type (expression-type e))))
  ((application? e)
   (make-application (forwardize-expression (application-callee e))
		     (forwardize-expression (application-argument e))
		     (forwardize-type (expression-type e))))
  ((lambda-expression? e)
   (make-lambda-expression
    (forwardize-parameter (lambda-expression-parameter e))
    (forwardize-expression (lambda-expression-body e))
    (forwardize-type (expression-type e))))
  ((let-expression? e)
   (make-let-expression (forwardize-parameter (let-expression-parameter e))
			(forwardize-expression (let-expression-expression e))
			(forwardize-expression (let-expression-body e))
			(forwardize-type (expression-type e))))
  ((if-expression? e)
   (make-if-expression
    (make-application
     (make-lambda-expression
      (make-cons-parameter (make-variable-parameter 'x 'boolean)
			   (make-variable-parameter 'x-hat 'unit)
			   (make-cons-type 'boolean 'unit))
      (make-variable-access-expression 'x 'boolean)
      (make-function-type (make-cons-type 'boolean 'unit) 'boolean))
     (forwardize-expression (if-expression-antecedent e))
     'boolean)
    (forwardize-expression (if-expression-consequent e))
    (forwardize-expression (if-expression-alternate e))
    (forwardize-type (expression-type e))))
  ((cons-expression? e)
   (make-cons-expression
    (forwardize-expression (cons-expression-car-argument e))
    (forwardize-expression (cons-expression-cdr-argument e))
    (forwardize-type (expression-type e))))
  (else (fuck-up))))

(define (j-forward value)
 (cond
  ((eq? value 'unit) (cons 'value 'unit))
  ((boolean? value) (cons value 'unit))
  ((real? value) (cons value 0))
  ((pair? value) (cons (j-forward (car value)) (j-forward (cdr value))))
  ((primitive-function? value) (primitive-function-forward-value value))
  ((closure? value)
   (make-closure
    (map (lambda (value-binding)
	  (make-value-binding (value-binding-variable value-binding)
			      (j-forward (value-binding-value value-binding))))
	 (closure-value-bindings value))
    (forwardize-expression (closure-lambda-expression value))))
  (else (fuck-up))))

(define (parameter-variable-bindings p quantified-type-variables)
 (let loop ((p p))
  (cond ((cons-parameter? p)
	 (append (loop (cons-parameter-car-parameter p))
		 (loop (cons-parameter-cdr-parameter p))))
	((variable-parameter? p)
	 (list (make-variable-binding (variable-parameter-variable p)
				      (variable-parameter-type p)
				      quantified-type-variables)))
	(else (fuck-up)))))

(define (concrete->abstract-expression e)
 (let loop ((e e) (variable-bindings *variable-bindings*))
  (cond
   ((boolean? e) (make-constant-expression e 'boolean))
   ((number? e) (make-constant-expression e 'real))
   ((symbol? e)
    (if (eq? e 'unit)
	(make-constant-expression e 'unit)
	(let ((variable-binding
	       (find-if	(lambda (variable-binding)
			 (eq? (variable-binding-variable variable-binding) e))
			variable-bindings)))
	 (make-variable-access-expression
	  e
	  (instantiate
	   (variable-binding-quantified-type-variables variable-binding)
	   (variable-binding-type variable-binding))))))
   ((list? e)
    (case (first e)
     ((:) (let ((e1 (loop (second e) variable-bindings)))
	   (unify! (expression-type e1) (concrete->abstract-type (third e)))
	   e1))
     ((lambda)
      (case (length (second e))
       ((0) (loop `(lambda ((: ,(gensym) unit)) ,(third e)) variable-bindings))
       ((1)
	(let* ((p (concrete->abstract-parameter (first (second e))))
	       (e1 (loop (third e)
			 (append (parameter-variable-bindings p '())
				 variable-bindings))))
	 (make-lambda-expression
	  p e1 (make-function-type (parameter-type p) (expression-type e1)))))
       (else (loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
			     ,@(rest (rest (second e))))
		     ,(third e))
		   variable-bindings))))
     ((let*)
      (case (length (second e))
       ((0) (loop (third e) variable-bindings))
       ((1)
	(let ((p (concrete->abstract-parameter (first (first (second e)))))
	      (e1 (loop (second (first (second e))) variable-bindings)))
	 (unify! (parameter-type p) (expression-type e1))
	 (let ((e2 (loop (third e)
			 (append
			  (parameter-variable-bindings
			   p
			   (set-differencep
			    clones?
			    (abstract-type-variables-in (expression-type e1))
			    (reduce
			     (lambda (as1 as2) (unionp clones? as1 as2))
			     (map (lambda (variable-binding)
				   (abstract-type-variables-in
				    (variable-binding-type variable-binding)))
				  variable-bindings)
			     '())))
			  variable-bindings))))
	  (make-let-expression p e1 e2 (expression-type e2)))))
       (else
	(loop
	 `(let* (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	 variable-bindings))))
     ((if) (let ((e1 (loop (second e) variable-bindings))
		 (e2 (loop (third e) variable-bindings))
		 (e3 (loop (fourth e) variable-bindings)))
	    (unify! (expression-type e1) 'boolean)
	    (unify! (expression-type e2) (expression-type e3))
	    (make-if-expression e1 e2 e3 (expression-type e3))))
     ((cons)
      (let ((e1 (loop (second e) variable-bindings))
	    (e2 (loop (third e) variable-bindings)))
       (make-cons-expression
	e1 e2 (make-cons-type (expression-type e1) (expression-type e2)))))
     ((cond) (loop (if (null? (rest (rest e)))
		       (second (second e))
		       `(if ,(first (second e))
			    ,(second (second e))
			    (cond ,@(rest (rest e)))))
		   variable-bindings))
     (else
      (case (length (rest e))
       ((0) (loop `(,(first e) unit) variable-bindings))
       ((1) (let ((e1 (loop (first e) variable-bindings))
		  (e2 (loop (second e) variable-bindings))
		  (a (create-type-variable '())))
	     (unify!
	      (expression-type e1) (make-function-type (expression-type e2) a))
	     (make-application e1 e2 a)))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 variable-bindings))))))
   (else (fuck-up)))))

(define (parameter-value-bindings p value)
 (let loop ((p p) (value value))
  (cond ((variable-parameter? p)
	 (list (make-value-binding (variable-parameter-variable p) value)))
	((cons-parameter? p)
	 (append (loop (cons-parameter-car-parameter p) (car value))
		 (loop (cons-parameter-cdr-parameter p) (cdr value))))
	(else (fuck-up)))))

(define (call callee argument)
 (cond
  ((primitive-function? callee)
   ((primitive-function-procedure callee) argument))
  ((closure? callee)
   (evaluate-internal
    (lambda-expression-body (closure-lambda-expression callee))
    (append (parameter-value-bindings
	     (lambda-expression-parameter (closure-lambda-expression callee))
	     argument)
	    (closure-value-bindings callee))))
  (else (fuck-up))))

(define (evaluate-internal e value-bindings)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e)
   (value-binding-value
    (find-if (lambda (value-binding)
	      (eq? (value-binding-variable value-binding)
		   (variable-access-expression-variable e)))
	     value-bindings)))
  ((application? e)
   (call (evaluate-internal (application-callee e) value-bindings)
	 (evaluate-internal (application-argument e) value-bindings)))
  ((lambda-expression? e) (make-closure value-bindings e))
  ((let-expression? e)
   (evaluate-internal
    (let-expression-body e)
    (append (parameter-value-bindings
	     (let-expression-parameter e)
	     (evaluate-internal (let-expression-expression e) value-bindings))
	    value-bindings)))
  ((if-expression? e)
   (if (evaluate-internal (if-expression-antecedent e) value-bindings)
       (evaluate-internal (if-expression-consequent e) value-bindings)
       (evaluate-internal (if-expression-alternate e) value-bindings)))
  ((cons-expression? e)
   (cons (evaluate-internal (cons-expression-car-argument e) value-bindings)
	 (evaluate-internal (cons-expression-cdr-argument e) value-bindings)))
  (else (fuck-up))))

(define (evaluate e) (evaluate-internal e *value-bindings*))

(define (define-basis-constant variable value forward-value t)
 (let ((t (concrete->abstract-type t)))
  (set! *basis-constants* (cons variable *basis-constants*))
  (set! *variable-bindings*
	(cons (make-variable-binding variable t (abstract-type-variables-in t))
	      *variable-bindings*))
  (set! *value-bindings*
	(cons (make-value-binding
	       variable (make-primitive-function value forward-value))
	      *value-bindings*))))

(define (make-circular-primitive-function value)
 (let ((primitive-function (make-primitive-function value #f)))
  (set-primitive-function-forward-value! primitive-function primitive-function)
  primitive-function))

(define (define-circular-basis-constant variable value t)
 (let ((t (concrete->abstract-type t)))
  (set! *basis-constants* (cons variable *basis-constants*))
  (set! *variable-bindings*
	(cons (make-variable-binding variable t (abstract-type-variables-in t))
	      *variable-bindings*))
  (set! *value-bindings*
	(cons (make-value-binding
	       variable (make-circular-primitive-function value))
	      *value-bindings*))))

(define (forwardize-basis!)
 (for-each (lambda (value-binding)
	    (let* ((primitive-function (value-binding-value value-binding))
		   (forward-value
		    (primitive-function-forward-value primitive-function)))
	     (syntax-check-expression! forward-value)
	     (set-primitive-function-forward-value!
	      primitive-function
	      (evaluate (concrete->abstract-expression forward-value)))))
	   *value-bindings*))

(define (intialize-basis!)
 (define-basis-constant
  '+
  (lambda (x) (+ (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (+ x y) (+ x-hat y-hat)))
  '(=> (cons real real) real))
 (define-basis-constant
  '-
  (lambda (x) (- (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (- x y) (- x-hat y-hat)))
  '(=> (cons real real) real))
 (define-basis-constant
  '*
  (lambda (x) (* (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat))
    (cons (* x y) (+ (* x y-hat) (* y x-hat))))
  '(=> (cons real real) real))
 (define-basis-constant
  '/
  (lambda (x) (/ (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat))
    (cons (/ x y) (/ (- (* y x-hat) (* x y-hat)) (* y y))))
  '(=> (cons real real) real))
 (define-basis-constant
  'sqrt
  sqrt
  '(lambda (x x-hat) (cons (sqrt x) (/ x (* 2 (sqrt x)))))
  '(=> real real))
 (define-basis-constant
  'exp
  exp
  '(lambda (x x-hat) (cons (exp x) (* x-hat (exp x))))
  '(=> real real))
 (define-basis-constant
  'log
  log
  '(lambda (x x-hat) (cons (log x) (/ x-hat x)))
  '(=> real real))
 (define-basis-constant
  'sin
  sin
  '(lambda (x x-hat) (cons (sin x) (* x-hat (cos x))))
  '(=> real real))
 (define-basis-constant
  'cos
  cos
  '(lambda (x x-hat) (cons (cos x) (- 0 (* x-hat (sin x)))))
  '(=> real real))
 (define-basis-constant
  'atan
  (lambda (x) (atan (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat))
    (cons (atan y x) (/ (- (* x y-hat) (* y x-hat)) (+ (* x x) (* y y)))))
  '(=> (cons real real) real))
 (define-basis-constant
  '=
  (lambda (x) (= (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (= x y) unit))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<
  (lambda (x) (< (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (< x y) unit))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>
  (lambda (x) (> (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (> x y) unit))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<=
  (lambda (x) (<= (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (<= x y) unit))
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>=
  (lambda (x) (>= (car x) (cdr x)))
  '(lambda ((cons x x-hat) (cons y y-hat)) (cons (>= x y) unit))
  '(=> (cons real real) boolean))
 (define-basis-constant
  'zero?
  zero?
  '(lambda (x x-hat) (cons (zero? x) unit))
  '(=> real boolean))
 (define-basis-constant
  'positive?
  positive?
  '(lambda (x x-hat) (cons (positive? x) unit))
  '(=> real boolean))
 (define-basis-constant
  'negative?
  negative?
  '(lambda (x x-hat) (cons (negative? x) unit))
  '(=> real boolean))
 (forwardize-basis!)
 (define-circular-basis-constant
  'y
  (lambda (f)
   (call (make-circular-primitive-function
	  (lambda (g)
	   (make-circular-primitive-function
	    (lambda (x) (call (call f (call g g)) x)))))
	 (make-circular-primitive-function
	  (lambda (g)
	   (make-circular-primitive-function
	    (lambda (x) (call (call f (call g g)) x)))))))
  '(=> (=> (=> 'a 'b) (=> 'a 'b)) (=> 'a 'b)))
 ;; needs work: I'm not sure that J-forward is actually circular.
 (define-circular-basis-constant 'j-forward j-forward '(=> 'a (_> 'a))))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
