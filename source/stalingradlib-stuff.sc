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
;;;  d: differentiation

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

(define-structure primitive-function procedure forward-value reverse-value)

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
	 ((<_)
	  (unless (= (length t) 3) (panic (format #f "Invalid type: ~s" t)))
	  (syntax-check-type! (second t))
	  (syntax-check-type! (third t)))
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

(define (create-type-variable ds)
 (let ((a (make-type-variable #f ds #f)))
  (set-type-variable-type! a a)
  (set-type-variable-clone! a a)
  a))

(define (clone-type-variable a ds)
 (when (bound? a) (fuck-up))
 (let loop ((a1 a))
  (cond
   ((equal? (map first (type-variable-differentiations a1))
	    (map first ds))
    (for-each (lambda (d1 d2)
	       ;; I'm not sure whether there is a need to backtrack over
	       ;; unification failures.
	       (when (eq? (first d1) '<_) (unify! (second d1) (second d2))))
	      (type-variable-differentiations a1)
	      ds)
    a1)
   ((eq? (type-variable-clone a1) a)
    (let ((a2 (make-type-variable #f ds #f)))
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
  (let outer ((t t))
   (cond
    ((eq? t 'unit) 'unit)
    ((eq? t 'boolean) 'boolean)
    ((eq? t 'real) 'real)
    ((type-variable? t)
     (if (bound? t)
	 (outer (type-variable-type t))
	 (let inner ((ds (type-variable-differentiations t)))
	  (if (null? ds)
	      `',(type-binding-concrete
		  (find-if (lambda (type-binding)
			    (clones? (type-binding-abstract type-binding) t))
			   type-bindings))
	      (case (first (first ds))
	       ((_>) `(_> ,(inner (rest ds))))
	       ((<_) `(<_ ,(outer (second (first ds))) ,(inner (rest ds))))
	       (else (fuck-up)))))))
    ((function-type? t)
     `(=> ,(outer (function-type-parameter-type t))
	  ,(outer (function-type-result-type t))))
    ((cons-type? t)
     `(cons ,(outer (cons-type-car-type t))
	    ,(outer (cons-type-cdr-type t))))
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
	 ((<_) (unionq (concrete-type-variables-in (second t))
		       (concrete-type-variables-in (third t))))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (occurs? a t)
 (or
  (eq? a t)
  (and (type-variable? t)
       (if (bound? t)
	   (occurs? a (type-variable-type t))
	   (some (lambda (d) (and (eq? (first d) '<_) (occurs? a (second d))))
		 (type-variable-differentiations t))))
  (and (function-type? t)
       (or (occurs? a (function-type-parameter-type t))
	   (occurs? a (function-type-result-type t))))
  (and (cons-type? t)
       (or (occurs? a (cons-type-car-type t))
	   (occurs? a (cons-type-cdr-type t))))))

(define (unwind-differentiations t ds)
 (if (null? ds)
     t
     (let ((t (unwind-differentiations t (rest ds))))
      (case (first (first ds))
       ((_>) (forwardize-type t))
       ((<_) (reversize-type t (second (first ds))))
       (else (fuck-up))))))

(define (bind-all-clones! a t)
 (let loop ()
  (let ((again? #f))
   (let loop ((a1 a))
    (let ((t (unwind-differentiations t (type-variable-differentiations a1))))
     (unless (bound? a1)
      (set-type-variable-type! a1 t)
      (set! again? #t)))
    (unless (eq? (type-variable-clone a1) a) (loop (type-variable-clone a1))))
   (when again? (loop)))))

(define (appropriate-clone a1 a2 a3)
 ;; The appropriate clone differentiation is illustrated by the following
 ;; example. Suppose you unify (_> a1) and a2. And a1 has a clone
 ;; (_> (_> a1)). Then you share (_> (_> a1)) with the clone (_> a2) of a2. Or
 ;; if you unify (_> a1) and (_> (_> a2)). And (_> a1) has a clone a1. Then
 ;; you share a1 with the clone (_> a2) of (_> (_> a2)). More generally,
 ;; suppose (F1 (G a1)) has a clone (F2 (G a1)), where G is maximal. Then you
 ;; can only unify (F1 (G a1)) with (F1 (H a2)). When you do so, you share
 ;; (F2 (G a1)) with the clone (F2 (H a2)) of (F1 (H a2)).
 (let loop ((ds1 (reverse (type-variable-differentiations a1)))
	    (ds3 (reverse (type-variable-differentiations a3))))
  (cond
   ((and (not (null? ds1))
	 (not (null? ds3))
	 (eq? (first (first ds1)) (first (first ds3))))
    (when (eq? (first (first ds1)) '<_)
     ;; I'm not sure whether there is a need to backtrack over unification
     ;; failures.
     (unify! (second (first ds1)) (second (first ds3))))
    (loop (rest ds1) (rest ds3)))
   (else
    (let loop ((ds1 (reverse ds1)) (ds2 (type-variable-differentiations a2)))
     (cond ((and (not (null? ds1))
		 (not (null? ds2))
		 (eq? (first (first ds1)) (first (first ds2))))
	    (when (eq? (first (first ds1)) '<_)
	     ;; I'm not sure whether there is a need to backtrack over
	     ;; unification failures.
	     (unify! (second (first ds1)) (second (first ds2))))
	    (loop (rest ds1) (rest ds2)))
	   ((not (null? ds1)) (panic "Unification failure"))
	   (else (clone-type-variable a2 (append (reverse ds3) ds2)))))))))

(define (share-all-clones! a1 a2)
 ;; a1 and a2 are unbound type variables that are to be unified. We loop over
 ;; all of the clones a3 of a1 and share a3 with the appropriate clone
 ;; differentiation a4 of a2. And we loop over all of the clones a3 of a2 and
 ;; share a3 with the appropriate clone differentiation a4 of a1.
 (let loop ()
  (let ((again? #f))
   (let loop ((a3 a1))
    ;; I'm not sure whether you need to follow the binding of a3 if it is
    ;; bound.
    (unless (bound? a3)
     (let ((a4 (appropriate-clone a1 a2 a3)))
      ;; This is in case creating the clone a4 can bind a3. I'm not sure that
      ;; this can happen.
      ;; I'm not sure whether you need to follow the binding of a3 if it is
      ;; bound.
      (unless (bound? a3)
       (set-type-variable-type! a3 a4)
       (set! again? #t))))
    (unless (eq? (type-variable-clone a3) a1)
     (loop (type-variable-clone a3))))
   (let loop ((a3 a2))
    ;; I'm not sure whether you need to follow the binding of a3 if it is
    ;; bound.
    (unless (bound? a3)
     (let ((a4 (appropriate-clone a2 a1 a3)))
      ;; This is in case creating the clone a4 can bind a3. I'm not sure this
      ;; this can happen.
      ;; I'm not sure whether you need to follow the binding of a3 if it is
      ;; bound.
      (unless (bound? a3)
       (set-type-variable-type! a3 a4)
       (set! again? #t))))
    (unless (eq? (type-variable-clone a3) a2)
     (loop (type-variable-clone a3))))
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
 (cond ((eq? t 'unit) (make-cons-type 'unit 'unit))
       ((eq? t 'boolean) (make-cons-type 'boolean 'unit))
       ((eq? t 'real) (make-cons-type 'real 'real))
       ((type-variable? t)
	(if (bound? t)
	    (forwardize-type (type-variable-type t))
	    (clone-type-variable
	     t (cons '(_>) (type-variable-differentiations t)))))
       ((function-type? t)
	(make-function-type (forwardize-type (function-type-parameter-type t))
			    (forwardize-type (function-type-result-type t))))
       ((cons-type? t)
	(make-cons-type (forwardize-type (cons-type-car-type t))
			(forwardize-type (cons-type-cdr-type t))))
       (else (fuck-up))))

(define (reversize-type t1 t2)
 (cond
  ((eq? t2 'unit) (make-cons-type 'unit (make-function-type 'unit t1)))
  ((eq? t2 'boolean) (make-cons-type 'boolean (make-function-type 'unit t1)))
  ((eq? t2 'real) (make-cons-type 'real (make-function-type 'real t1)))
  ((type-variable? t2)
   (if (bound? t2)
       (reversize-type t1 (type-variable-type t2))
       (clone-type-variable
	t2 (cons `(<_ ,t1) (type-variable-differentiations t2)))))
  ((function-type? t2)
   (make-function-type (reversize-type t1 (function-type-parameter-type t2))
		       (reversize-type t1 (function-type-result-type t2))))
  ((cons-type? t2)
   (make-cons-type (reversize-type t1 (cons-type-car-type t2))
		   (reversize-type t1 (cons-type-cdr-type t2))))
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
	   ((<_) (reversize-type (loop (second t)) (loop (third t))))
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
			   (make-variable-parameter 'x-forward 'unit)
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
  ((eq? value 'unit) (cons value 'unit))
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

(define (reversize-parameter t p)
 (cond ((variable-parameter? p)
	(make-variable-parameter (variable-parameter-variable p)
				 (reversize-type t (parameter-type p))))
       ((cons-parameter? p)
	(make-cons-parameter
	 (reversize-parameter t (cons-parameter-car-parameter p))
	 (reversize-parameter t (cons-parameter-cdr-parameter p))
	 (reversize-type t (parameter-type p))))
       (else (fuck-up))))

(define (reversize-expression t e)
 (cond
  ((constant-expression? e)
   (make-constant-expression (j-reverse t (constant-expression-value e))
			     (reversize-type t (expression-type e))))
  ((variable-access-expression? e)
   (make-variable-access-expression (variable-access-expression-variable e)
				    (reversize-type t (expression-type e))))
  ((application? e)
   (make-application (reversize-expression t (application-callee e))
		     (reversize-expression t (application-argument e))
		     (reversize-type t (expression-type e))))
  ;; needs work
  ((lambda-expression? e)
   (make-lambda-expression
    (reversize-parameter t (lambda-expression-parameter e))
    (reversize-expression t (lambda-expression-body e))
    (reversize-type t (expression-type e))))
  ;; needs work
  ((let-expression? e)
   (make-let-expression (reversize-parameter t (let-expression-parameter e))
			(reversize-expression t (let-expression-expression e))
			(reversize-expression t (let-expression-body e))
			(reversize-type t (expression-type e))))
  ((if-expression? e)
   (make-if-expression
    (make-application
     ;; needs work: t1 is the type of x-backpropagator
     (let ((t1 'needs-work))
      (make-lambda-expression
       (make-cons-parameter
	(make-variable-parameter 'x 'boolean)
	(make-variable-parameter 'x-backpropagator t1)
	(make-cons-type 'boolean t1))
       (make-variable-access-expression 'x 'boolean)
       (make-function-type (make-cons-type 'boolean t1) 'boolean)))
     (reversize-expression t (if-expression-antecedent e))
     'boolean)
    (reversize-expression t (if-expression-consequent e))
    (reversize-expression t (if-expression-alternate e))
    (reversize-type t (expression-type e))))
  ((cons-expression? e)
   (make-cons-expression
    (reversize-expression t (cons-expression-car-argument e))
    (reversize-expression t (cons-expression-cdr-argument e))
    (reversize-type t (expression-type e))))
  (else (fuck-up))))

(define (zero-of-type t)
 (cond
  ;; I'm not sure that this can happen.
  ((eq? t 'unit) (make-constant-expression 'unit t))
  ;; I'm not sure that this can happen.
  ((eq? t 'boolean) (make-constant-expression #f t))
  ((eq? t 'real) (make-constant-expression 0 t))
  ((type-variable? t)
   (unless (bound? t) (panic "Cannot create a zero of polymorphic type"))
   (zero-of-type (type-variable-type t)))
  ((function-type? t)
   ;; I'm not sure that this is correct.
   (make-lambda-expression
    (make-variable-parameter 'x-reverse (function-type-parameter-type t))
    (zero-of-type (function-type-result-type t))
    t))
  ((cons-type? t)
   (make-cons-expression (zero-of-type (cons-type-car-type t))
			 (zero-of-type (cons-type-cdr-type t))
			 t))
  (else (fuck-up))))

(define (j-reverse t value)
 (cond
  ((eq? value 'unit)
   (cons value (make-closure '() (zero-of-type (make-function-type 'unit t)))))
  ((boolean? value)
   (cons
    value (make-closure '() (zero-of-type (make-function-type 'boolean t)))))
  ((real? value)
   (cons value (make-closure '() (zero-of-type (make-function-type 'real t)))))
  ((pair? value) (cons (j-reverse t (car value)) (j-reverse t (cdr value))))
  ((primitive-function? value) (primitive-function-reverse-value value))
  ((closure? value)
   (make-closure (map (lambda (value-binding)
		       (make-value-binding
			(value-binding-variable value-binding)
			(j-reverse t (value-binding-value value-binding))))
		      (closure-value-bindings value))
		 (reversize-expression t (closure-lambda-expression value))))
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

(define (define-basis-constant variable value forward-value reverse-value t)
 (let ((t (concrete->abstract-type t)))
  (set! *basis-constants* (cons variable *basis-constants*))
  (set! *variable-bindings*
	(cons (make-variable-binding variable t (abstract-type-variables-in t))
	      *variable-bindings*))
  (set! *value-bindings*
	(cons (make-value-binding
	       variable
	       (make-primitive-function value forward-value reverse-value))
	      *value-bindings*))))

(define (make-circular-primitive-function value)
 (let ((primitive-function (make-primitive-function value #f #f)))
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

(define (forwardize-and-reversize-basis!)
 (for-each (lambda (value-binding)
	    (let* ((primitive-function (value-binding-value value-binding))
		   (forward-value
		    (primitive-function-forward-value primitive-function))
		   (reverse-value
		    (primitive-function-reverse-value primitive-function)))
	     (syntax-check-expression! forward-value)
	     (syntax-check-expression! reverse-value)
	     (set-primitive-function-forward-value!
	      primitive-function
	      (evaluate (concrete->abstract-expression forward-value)))
	     (set-primitive-function-reverse-value!
	      primitive-function
	      (evaluate (concrete->abstract-expression reverse-value)))))
	   *value-bindings*))

(define (initialize-basis!)
 ;; needs work: reversize
 (define-basis-constant
  '+
  (lambda (x) (+ (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward))
    (cons (+ x y) (+ x-forward y-forward)))
  'needs-work
  '(=> (cons real real) real))
 (define-basis-constant
  '-
  (lambda (x) (- (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward))
    (cons (- x y) (- x-forward y-forward)))
  'needs-work
  '(=> (cons real real) real))
 (define-basis-constant
  '*
  (lambda (x) (* (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward))
    (cons (* x y) (+ (* y-forward x) (* x-forward y))))
  'needs-work
  '(=> (cons real real) real))
 (define-basis-constant
  '/
  (lambda (x) (/ (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward))
    (cons (/ x y) (/ (- (* x-forward y) (* y-forward x)) (* y y))))
  'needs-work
  '(=> (cons real real) real))
 (define-basis-constant
  'sqrt
  sqrt
  '(lambda (x x-forward) (cons (sqrt x) (/ x-forward (* 2 (sqrt x)))))
  'needs-work
  '(=> real real))
 (define-basis-constant
  'exp
  exp
  '(lambda (x x-forward) (cons (exp x) (* x-forward (exp x))))
  'needs-work
  '(=> real real))
 (define-basis-constant
  'log
  log
  '(lambda (x x-forward) (cons (log x) (/ x-forward x)))
  'needs-work
  '(=> real real))
 (define-basis-constant
  'sin
  sin
  '(lambda (x x-forward) (cons (sin x) (* x-forward (cos x))))
  'needs-work
  '(=> real real))
 (define-basis-constant
  'cos
  cos
  '(lambda (x x-forward) (cons (cos x) (- 0 (* x-forward (sin x)))))
  'needs-work
  '(=> real real))
 (define-basis-constant
  'atan
  (lambda (x) (atan (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward))
    (cons (atan y x)
	  (/ (- (* y-forward x) (* x-forward y)) (+ (* x x) (* y y)))))
  'needs-work
  '(=> (cons real real) real))
 (define-basis-constant
  '=
  (lambda (x) (= (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward)) (cons (= x y) unit))
  'needs-work
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<
  (lambda (x) (< (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward)) (cons (< x y) unit))
  'needs-work
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>
  (lambda (x) (> (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward)) (cons (> x y) unit))
  'needs-work
  '(=> (cons real real) boolean))
 (define-basis-constant
  '<=
  (lambda (x) (<= (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward)) (cons (<= x y) unit))
  'needs-work
  '(=> (cons real real) boolean))
 (define-basis-constant
  '>=
  (lambda (x) (>= (car x) (cdr x)))
  '(lambda ((cons x x-forward) (cons y y-forward)) (cons (>= x y) unit))
  'needs-work
  '(=> (cons real real) boolean))
 (define-basis-constant
  'zero?
  zero?
  '(lambda (x x-forward) (cons (zero? x) unit))
  'needs-work
  '(=> real boolean))
 (define-basis-constant
  'positive?
  positive?
  '(lambda (x x-forward) (cons (positive? x) unit))
  'needs-work
  '(=> real boolean))
 (define-basis-constant
  'negative?
  negative?
  '(lambda (x x-forward) (cons (negative? x) unit))
  'needs-work
  '(=> real boolean))
 (forwardize-and-reversize-basis!)
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
 ;; I'm not sure that J-forward is actually circular.
 (define-circular-basis-constant 'j-forward j-forward '(=> 'a (_> 'a)))
 ;; I'm not sure that J-reverse is actually circular.
 ;; needs work: j-reverse needs to take the type argument.
 (define-circular-basis-constant 'j-reverse j-reverse '(=> 'a (<_ 'a 'a))))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
