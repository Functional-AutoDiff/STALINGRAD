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
;;;  1. list as parameter
;;;  2. list* or multiarg cons both as expression and as parameter
;;;  3. spread arguments should be lists
;;;  4. unary -
;;;  5. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  6. chars, ports, eof object, symbols, continuations, strings, vectors

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: value
;;;  d: definition
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

;;; Structures

(define-structure variable-access-expression variable index)

(define-structure application callee argument)

(define-structure lambda-expression name variable free-variables body)

(define-structure letrec-expression
 procedure-variables
 argument-variables
 bodies-free-variables
 body-free-variables
 bodies
 body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure closure name values variable body)

(define-structure recursive-closure
 values procedure-variables argument-variables bodies index)

(define-structure primitive-procedure name procedure)

;;; needs work: Is a real generic zero a positive IEEE zero or a negative IEEE
;;;             zero?
(define-structure generic-zero
 index binding not-null? not-real? not-pair? not-procedure?)

;;; Variables

(define *gensym* 0)

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *generic-zero-index* -1)

(define *error-message* #f)

(define *error-v* #f)

(define *error-stack* #f)

;;; Parameters

(define *include-path* '())

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *n* #f)

;;; Procedures

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
 (call-with-input-file (default-extension pathname "vlad")
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
      (else (loop (cons e es)))))))))

(define (definition? d)
 (and (list? d)
      (= (length d) 3)
      (eq? (first d) 'define)
      (or (symbol? (second d))
	  (and (list? (second d))
	       (not (null? (second d)))
	       (symbol? (first (second d)))))))

(define (expand-definitions ds e)
 (for-each (lambda (d)
	    (unless (definition? d)
	     (panic (format #t "Invalid definition: ~s" d))))
	   ds)
 `(letrec ,(map (lambda (d)
		 (if (symbol? (second d))
		     `(,(second d) ,(third d))
		     `(,(first (second d))
		       (lambda ,(rest (second d)) ,(third d)))))
		ds)
   ,e))

(define (syntax-check-parameter! p)
 (cond
  ((symbol? p)
   (when (memq p '(quote lambda letrec let let* if cons list cond else and or))
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

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs *basis-constants*))
  (cond
   ((null? e) (panic (format #f "Invalid expression: ~s" e)))
   ((boolean? e) #f)
   ((real? e) #f)
   ((symbol? e)
    (unless (memq e xs) (panic (format #f "Unbound variable: ~s" e)))
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
     ((let) (unless (and (= (length e) 3)
			 (list? (second e))
			 (every (lambda (b) (and (list? b) (= (length b) 2)))
				(second e)))
	     (panic (format #f "Invalid expression: ~s" e)))
	    (loop `((lambda ,(map first (second e)) ,(third e))
		    ,@(map second (second e)))
		  xs))
     ((let*)
      (unless (and (= (length e) 3)
		   (list? (second e))
		   (every (lambda (b) (and (list? b) (= (length b) 2)))
			  (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (third e) xs))
       ((1) (loop `(let ,(second e) ,(third e)) xs))
       (else
	(loop `(let (,(first (second e))) (let* ,(rest (second e)) ,(third e)))
	      xs))))
     ;; needs work: to ensure that you don't shadow if-procedure
     ((if) (loop `((((if-procedure ,(second e)) (lambda () ,(third e)))
		    (lambda () ,(fourth e))))
		 xs))
     ;; needs work: to ensure that you don't shadow cons-procedure
     ((cons) (loop `((cons-procedure ,(second e)) ,(third e)) xs))
     ((list) (loop (if (null? (rest e))
		       ''()
		       `(cons ,(second e) (list ,@(rest (rest e)))))
		   xs))
     ;; note: We don't allow (cond ... (e) ...) or (cond ... (e1 => e2) ...).
     ((cond) (unless (and (>= (length e) 2)
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
     ((and) (loop (case (length (rest e))
		   ((0) #t)
		   ((1) (second e))
		   (else `(if ,(second e) (and ,@(rest (rest e))) #f)))
		  xs))
     ((or)
      (loop (case (length (rest e))
	     ((0) #f)
	     ((1) (second e))
	     (else
	      (let ((x (gensym)))
	       `(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e))))))))
	    xs))
     (else
      (case (length (rest e))
       ((0) (loop `(,(first e) '()) xs))
       ((1) (loop (first e) xs)
	    (loop (second e) xs))
       (else
	(loop
	 `(,(first e) (cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
	 xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (abstract->concrete e)
 (cond
  ((variable-access-expression? e)
   (if *show-access-indices?*
       `(access ,(variable-access-expression-variable e)
		,(variable-access-expression-index e))
       (variable-access-expression-variable e)))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  ((lambda-expression? e)
   `(lambda (,(lambda-expression-variable e))
     ,(abstract->concrete (lambda-expression-body e))))
  ((letrec-expression? e)
   `(letrec ,(vector->list
	      (map-vector (lambda (x1 x2 e)
			   `(,x1 (lambda (,x2) ,(abstract->concrete e))))
			  (letrec-expression-procedure-variables e)
			  (letrec-expression-argument-variables e)
			  (letrec-expression-bodies e)))
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
 (let loop ((p p) (e (make-variable-access-expression x #f)))
  (cond ((symbol? p) (list (make-variable-binding p e)))
	((list? p)
	 (case (first p)
	  ((cons)
	   (append (loop (second p)
			 (make-application
			  ;; needs work: to ensure that you don't shadow car
			  (make-variable-access-expression 'car #f) e))
		   (loop (third p)
			 (make-application
			  ;; needs work: to ensure that you don't shadow cdr
			  (make-variable-access-expression 'cdr #f) e))))
	  (else (fuck-up))))
	(else (fuck-up)))))

(define (free-variables-in e)
 (cond
  ((variable-access-expression? e)
   (list (variable-access-expression-variable e)))
  ((application? e)
   (unionq (free-variables-in (application-callee e))
	   (free-variables-in (application-argument e))))
  ((lambda-expression? e) (vector->list (lambda-expression-free-variables e)))
  ((letrec-expression? e)
   (vector->list (letrec-expression-body-free-variables e)))
  (else (fuck-up))))

(define (remove-duplicatesq-vector xs)
 (list->vector (remove-duplicatesq (vector->list xs))))

(define (coalesce-constants result)
 (let ((bss (transitive-equivalence-classesp
	     (lambda (b1 b2)
	      (same? (value-binding-value b1) (value-binding-value b2)))
	     (second result))))
  (define (rename x)
   (let ((bs (find-if
	      (lambda (bs)
	       (some (lambda (b) (eq? (value-binding-variable b) x)) bs))
	      bss)))
    (if bs (value-binding-variable (first bs)) x)))
  (list
   (let loop ((e (first result)))
    (cond
     ((variable-access-expression? e)
      (make-variable-access-expression
       (rename (variable-access-expression-variable e)) #f))
     ((application? e)
      (make-application (loop (application-callee e))
			(loop (application-argument e))))
     ((lambda-expression? e)
      (make-lambda-expression
       (lambda-expression-name e)
       (lambda-expression-variable e)
       (remove-duplicatesq-vector
	(map-vector rename (lambda-expression-free-variables e)))
       (loop (lambda-expression-body e))))
     ((letrec-expression? e)
      (make-letrec-expression
       (letrec-expression-procedure-variables e)
       (letrec-expression-argument-variables e)
       (remove-duplicatesq-vector
	(map-vector rename (letrec-expression-bodies-free-variables e)))
       (remove-duplicatesq-vector
	(map-vector rename (letrec-expression-body-free-variables e)))
       (map-vector loop (letrec-expression-bodies e))
       (loop (letrec-expression-body e))))
     (else (fuck-up))))
   (map first bss))))

(define (vector-append vs1 vs2)
 (list->vector (append (vector->list vs1) (vector->list vs2))))

(define (index x xs e)
 (define (lookup x-prime)
  (if (eq? x-prime x) -1 (positionq x-prime (vector->list xs))))
 (cond
  ((variable-access-expression? e)
   (make-variable-access-expression
    (variable-access-expression-variable e)
    (lookup (variable-access-expression-variable e))))
  ((application? e)
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))))
  ((lambda-expression? e)
   (let ((xs (lambda-expression-free-variables e)))
    (make-lambda-expression
     (lambda-expression-name e)
     (lambda-expression-variable e)
     (map-vector lookup xs)
     (index (lambda-expression-variable e) xs (lambda-expression-body e)))))
  ((letrec-expression? e)
   (let ((xs1 (letrec-expression-bodies-free-variables e))
	 (xs2 (letrec-expression-body-free-variables e)))
    (make-letrec-expression
     (letrec-expression-procedure-variables e)
     (letrec-expression-argument-variables e)
     (map-vector lookup xs1)
     (map-vector lookup xs2)
     (let ((xs (vector-append (letrec-expression-procedure-variables e) xs1)))
      (map-vector (lambda (x e) (index x xs e))
		  (letrec-expression-argument-variables e)
		  (letrec-expression-bodies e)))
     (index x
	    (vector-append (letrec-expression-procedure-variables e) xs2)
	    (letrec-expression-body e)))))
  (else (fuck-up))))

(define (concrete->abstract-expression e)
 (let* ((result
	 (let loop ((e e) (bs *variable-bindings*) (name "top level"))
	  (cond
	   ((boolean? e)
	    (let ((x (gensym)))
	     (list (make-variable-access-expression x #f)
		   (list (make-value-binding x e)))))
	   ((real? e)
	    (let ((x (gensym)))
	     (list (make-variable-access-expression x #f)
		   (list (make-value-binding x e)))))
	   ((symbol? e)
	    (list
	     (variable-binding-expression
	      (find-if (lambda (b) (eq? (variable-binding-variable b) e)) bs))
	     '()))
	   ((list? e)
	    (case (first e)
	     ((quote) (let ((x (gensym)))
		       (list (make-variable-access-expression x #f)
			     (list (make-value-binding x (second e))))))
	     ((lambda)
	      (case (length (second e))
	       ((0) (loop `(lambda (,(gensym)) ,(third e)) bs name))
	       ((1)
		(let* ((x (concrete->abstract-parameter (first (second e))))
		       (result (loop (third e)
				     (append
				      (parameter-variable-bindings
				       x (first (second e)))
				      bs)
				     `(inside ,name))))
		 (list (make-lambda-expression
			name
			x
			(list->vector
			 (removeq x (free-variables-in (first result))))
			(first result))
		       (second result))))
	       (else
		(loop `(lambda ((cons ,(first (second e)) ,(second (second e)))
				,@(rest (rest (second e))))
			,(third e))
		      bs
		      name))))
	     ((letrec)
	      (let* ((bs
		      (append
		       (map (lambda (b)
			     (make-variable-binding
			      (first b)
			      (make-variable-access-expression (first b) #f)))
			    (second e))
		       bs))
		     (results (map (lambda (b) (loop (second b) bs (first b)))
				   (second e)))
		     (result (loop (third e) bs name))
		     (xs1 (map first (second e)))
		     (xs2 (map (lambda (result)
				(lambda-expression-variable (first result)))
			       results))
		     (es (map (lambda (result)
			       (lambda-expression-body (first result)))
			      results))
		     (e (first result)))
	       (list
		(make-letrec-expression
		 (list->vector xs1)
		 (list->vector xs2)
		 (list->vector
		  (set-differenceq
		   (reduce
		    unionq
		    (map (lambda (x e) (removeq x (free-variables-in e)))
			 xs2 es)
		    '())
		   xs1))
		 (list->vector
		  (set-differenceq
		   (unionq
		    (reduce
		     unionq
		     (map (lambda (x e) (removeq x (free-variables-in e)))
			  xs2 es)
		     '())
		    (free-variables-in e))
		   xs1))
		 (list->vector es)
		 e)
		(append
		 (second result) (reduce append (map second results) '())))))
	     ((let) (loop `((lambda ,(map first (second e)) ,(third e))
			    ,@(map second (second e)))
			  bs
			  name))
	     ((let*) (case (length (second e))
		      ((0) (loop (third e) bs name))
		      ((1) (loop `(let ,(second e) ,(third e))  bs name))
		      (else (loop `(let (,(first (second e)))
				    (let* ,(rest (second e)) ,(third e)))
				  bs
				  name))))
	     ;; needs work: to ensure that you don't shadow if-procedure
	     ((if) (loop `((((if-procedure ,(second e)) (lambda () ,(third e)))
			    (lambda () ,(fourth e))))
			 bs
			 name))
	     ;; needs work: to ensure that you don't shadow cons-procedure
	     ((cons) (loop `((cons-procedure ,(second e)) ,(third e)) bs name))
	     ((list) (loop (if (null? (rest e))
			       ''()
			       `(cons ,(second e) (list ,@(rest (rest e)))))
			   bs
			   name))
	     ((cond) (loop (if (null? (rest (rest e)))
			       (second (second e))
			       `(if ,(first (second e))
				    ,(second (second e))
				    (cond ,@(rest (rest e)))))
			   bs
			   name))
	     ((and) (loop (case (length (rest e))
			   ((0) #t)
			   ((1) (second e))
			   (else `(if ,(second e) (and ,@(rest (rest e))) #f)))
			  bs
			  name))
	     ((or) (loop (case (length (rest e))
			  ((0) #f)
			  ((1) (second e))
			  (else (let ((x (gensym)))
				 `(let ((,x ,(second e)))
				   (if ,x ,x (or ,@(rest (rest e))))))))
			 bs
			 name))
	     (else
	      (case (length (rest e))
	       ((0) (loop `(,(first e) '()) bs name))
	       ((1) (let ((result1 (loop (first e) bs name))
			  (result2 (loop (second e) bs name)))
		     (list (make-application (first result1) (first result2))
			   (append (second result1) (second result2)))))
	       (else
		(loop `(,(first e)
			(cons ,(second e) ,(third e)) ,@(rest (rest (rest e))))
		      bs
		      name))))))
	   (else (fuck-up)))))
	(xs (free-variables-in (first result)))
	(bs (remove-if-not (lambda (b) (memq (value-binding-variable b) xs))
			   (append *value-bindings* (second result))))
	(result (coalesce-constants (list (first result) bs)))
	(xs (list->vector (map value-binding-variable (second result)))))
  (list (index #f xs (first result))
	(list->vector (map value-binding-value (second result))))))

(define (create-generic-zero)
 (set! *generic-zero-index* (+ *generic-zero-index* 1))
 (make-generic-zero *generic-zero-index* #f #f #f #f #f))

(define (generic-zero-bound? v) (not (eq? (generic-zero-binding v) #f)))

(define (generic-zero-dereference-as-null v)
 (cond ((generic-zero? v)
	(unless (generic-zero-bound? v)
	 (when (generic-zero-not-null? v) (fail))
	 (local-set-generic-zero-binding! v '()))
	(generic-zero-dereference-as-null (generic-zero-binding v)))
       (else v)))

(define (generic-zero-dereference-as-real v)
 (cond ((generic-zero? v)
	(unless (generic-zero-bound? v)
	 (when (generic-zero-not-real? v) (fail))
	 (local-set-generic-zero-binding! v 0))
	(generic-zero-dereference-as-real (generic-zero-binding v)))
       (else v)))

(define (generic-zero-dereference-as-pair v)
 (cond ((generic-zero? v)
	(unless (generic-zero-bound? v)
	 (when (generic-zero-not-pair? v) (fail))
	 (local-set-generic-zero-binding!
	  v (cons (create-generic-zero) (create-generic-zero))))
	(generic-zero-dereference-as-pair (generic-zero-binding v)))
       (else v)))

(define (generic-zero-dereference-as-procedure v)
 (cond ((generic-zero? v)
	(unless (generic-zero-bound? v)
	 (when (generic-zero-not-procedure? v) (fail))
	 (local-set-generic-zero-binding!
	  v
	  (make-closure "generic zero"
			(vector (create-generic-zero))
			'x
			(make-variable-access-expression 'zero 0))))
	(generic-zero-dereference-as-procedure (generic-zero-binding v)))
       (else v)))

(define (generic-zero-conforming-dereference v1 v2)
 (cond
  ((and (generic-zero? v1) (generic-zero-bound? v1))
   (generic-zero-conforming-dereference (generic-zero-binding v1) v2))
  ((and (generic-zero? v2) (generic-zero-bound? v2))
   (generic-zero-conforming-dereference v1 (generic-zero-binding v2)))
  ((and (generic-zero? v1) (generic-zero? v2))
   (unless (eq? v1 v2) (set-generic-zero-binding! v1 v2))
   (cons v1 v2))
  ((generic-zero? v1)
   (cond
    ((null? v2)
     (generic-zero-conforming-dereference
      (generic-zero-dereference-as-null v1) v2))
    ((real? v2)
     (generic-zero-conforming-dereference
      (generic-zero-dereference-as-real v1) v2))
    ((pair? v2)
     (generic-zero-conforming-dereference
      (generic-zero-dereference-as-pair v1) v2))
    ((vlad-procedure? v2)
     (generic-zero-conforming-dereference
      (generic-zero-dereference-as-procedure v1) v2))
    (else (run-time-error "Invalid argument to plus-primitive" (cons v1 v2)))))
  ((generic-zero? v2)
   (cond
    ((null? v1)
     (generic-zero-conforming-dereference
      v1 (generic-zero-dereference-as-null v2)))
    ((real? v1)
     (generic-zero-conforming-dereference
      v1 (generic-zero-dereference-as-real v2)))
    ((pair? v1)
     (generic-zero-conforming-dereference
      v1 (generic-zero-dereference-as-pair v2)))
    ((vlad-procedure? v1)
     (generic-zero-conforming-dereference
      v1 (generic-zero-dereference-as-procedure v2)))
    (else (run-time-error "Invalid argument to plus-primitive" (cons v1 v2)))))
  ((and (null? v1) (null? v2)) (cons v1 v2))
  ((and (real? v1) (real? v2)) (cons v1 v2))
  ((and (pair? v1) (pair? v2))
   (let ((v3 (generic-zero-conforming-dereference (car v1) (car v2)))
	 (v4 (generic-zero-conforming-dereference (cdr v1) (cdr v2))))
    (cons (cons (car v3) (car v4)) (cons (cdr v3) (cdr v4)))))
  ((and (vlad-procedure? v1) (vlad-procedure? v2)) (cons v1 v2))
  (else (run-time-error "Invalid argument to plus-primitive" (cons v1 v2)))))

(define (generic-zero-dereference v)
 (cond ((generic-zero? v)
	(unless (generic-zero-bound? v)
	 (run-time-error
	  "Cannot apply this primitive to an unbound generic zero" v))
	(generic-zero-dereference (generic-zero-binding v)))
       (else v)))

(define (generic-zero-dereference-maybe-null? v)
 (if (generic-zero? v)
     (cond
      ((generic-zero-bound? v)
       (generic-zero-dereference-maybe-null? (generic-zero-binding v)))
      (else
       (either
	(begin (when (generic-zero-not-null? v) (fail))
	       (local-set-generic-zero-binding! v '())
	       #t)
	(begin (local-set-generic-zero-not-null?! v #t)
	       (cond ((and (generic-zero-not-pair? v)
			   (generic-zero-not-procedure? v))
		      (local-set-generic-zero-binding! v 0))
		     ((and (generic-zero-not-real? v)
			   (generic-zero-not-procedure? v))
		      (local-set-generic-zero-binding!
		       v
		       (cons (create-generic-zero) (create-generic-zero))))
		     ((and (generic-zero-not-real? v)
			   (generic-zero-not-pair? v))
		      (local-set-generic-zero-binding!
		       v
		       (make-closure
			"generic zero"
			(vector (create-generic-zero))
			'x
			(make-variable-access-expression 'zero 0)))))
	       #f))))
     (null? v)))

(define (generic-zero-dereference-maybe-real? v)
 (if (generic-zero? v)
     (cond
      ((generic-zero-bound? v)
       (generic-zero-dereference-maybe-real? (generic-zero-binding v)))
      (else
       (either (begin (when (generic-zero-not-real? v) (fail))
		      (local-set-generic-zero-binding! v 0)
		      #t)
	       (begin (local-set-generic-zero-not-real?! v #t)
		      (cond ((and (generic-zero-not-pair? v)
				  (generic-zero-not-procedure? v))
			     (local-set-generic-zero-binding! v '()))
			    ((and (generic-zero-not-null? v)
				  (generic-zero-not-procedure? v))
			     (local-set-generic-zero-binding!
			      v
			      (cons (create-generic-zero)
				    (create-generic-zero))))
			    ((and (generic-zero-not-null? v)
				  (generic-zero-not-pair? v))
			     (local-set-generic-zero-binding!
			      v
			      (make-closure
			       "generic zero"
			       (vector (create-generic-zero))
			       'x
			       (make-variable-access-expression 'zero 0)))))
		      #f))))
     (real? v)))

(define (generic-zero-dereference-maybe-pair? v)
 (if (generic-zero? v)
     (cond
      ((generic-zero-bound? v)
       (generic-zero-dereference-maybe-pair? (generic-zero-binding v)))
      (else
       (either (begin (when (generic-zero-not-pair? v) (fail))
		      (local-set-generic-zero-binding!
		       v (cons (create-generic-zero) (create-generic-zero)))
		      #t)
	       (begin (local-set-generic-zero-not-pair?! v #t)
		      (cond ((and (generic-zero-not-real? v)
				  (generic-zero-not-procedure? v))
			     (local-set-generic-zero-binding! v '()))
			    ((and (generic-zero-not-null? v)
				  (generic-zero-not-procedure? v))
			     (local-set-generic-zero-binding! v 0))
			    ((and (generic-zero-not-null? v)
				  (generic-zero-not-real? v))
			     (local-set-generic-zero-binding!
			      v
			      (make-closure
			       "generic zero"
			       (vector (create-generic-zero))
			       'x
			       (make-variable-access-expression 'zero 0)))))
		      #f))))
     (pair? v)))

(define (generic-zero-dereference-maybe-procedure? v)
 (if (generic-zero? v)
     (cond
      ((generic-zero-bound? v)
       (generic-zero-dereference-maybe-procedure? (generic-zero-binding v)))
      (else
       (either
	(begin (when (generic-zero-not-procedure? v) (fail))
	       (local-set-generic-zero-binding!
		v
		(make-closure "generic zero"
			      (vector (create-generic-zero))
			      'x
			      (make-variable-access-expression 'zero 0)))
	       #t)
	(begin (local-set-generic-zero-not-procedure?! v #t)
	       (cond ((and (generic-zero-not-real? v)
			   (generic-zero-not-pair? v))
		      (local-set-generic-zero-binding! v '()))
		     ((and (generic-zero-not-null? v)
			   (generic-zero-not-pair? v))
		      (local-set-generic-zero-binding! v 0))
		     ((and (generic-zero-not-null? v)
			   (generic-zero-not-real? v))
		      (local-set-generic-zero-binding!
		       v (cons (create-generic-zero) (create-generic-zero)))))
	       #f))))
     (vlad-procedure? v)))

(define (generic-zero-unbound? v)
 (or (and (generic-zero? v)
	  (or (not (generic-zero-bound? v))
	      (generic-zero-unbound? (generic-zero-binding v))))
     (and (pair? v)
	  (generic-zero-unbound? (car v))
	  (generic-zero-unbound? (cdr v)))))

(define (name callee)
 (cond ((primitive-procedure? callee) (primitive-procedure-name callee))
       ((closure? callee)
	(if *unabbreviate-closures?*
	    (if #f			;debugging
		`(closure
		  ,(map-n (lambda (i)
			   ;; needs work: to reconstruct free variables
			   (list i
				 (externalize
				  (vector-ref (closure-values callee) i))))
			  (vector-length (closure-values callee)))
		  (lambda (,(closure-variable callee))
		   ,(abstract->concrete (closure-body callee))))
		`(lambda (,(closure-variable callee))
		  ,(abstract->concrete (closure-body callee))))
	    (closure-name callee)))
       ((recursive-closure? callee)	
	(if *unabbreviate-recursive-closures?*
	    `(recursive-closure
	      ,(vector-ref (recursive-closure-procedure-variables callee)
			   (recursive-closure-index callee))
	      ,(map-n
		(lambda (i)
		 ;; needs work: to reconstruct free variables
		 (list i
		       (externalize
			(vector-ref (recursive-closure-values callee) i))))
		(vector-length (recursive-closure-values callee)))
	      ,(vector->list
		(map-vector
		 (lambda (x1 x2 e)
		  `(,x1 (lambda (,x2) ,(abstract->concrete e))))
		 (recursive-closure-procedure-variables callee)
		 (recursive-closure-argument-variables callee)
		 (recursive-closure-bodies callee))))
	    (vector-ref (recursive-closure-procedure-variables callee)
			(recursive-closure-index callee))))
       (else (fuck-up))))

(define (externalize v)
 (cond ((generic-zero? v)
	(if (generic-zero-bound? v)
	    (externalize (generic-zero-binding v))
	    `(generic-zero ,(generic-zero-index v))))
       ((null? v) '())
       ((boolean? v) v)
       ((real? v) v)
       ((pair? v) (cons (externalize (car v)) (externalize (cdr v))))
       ((vlad-procedure? v) (name v))
       (else (fuck-up))))

(define (with-write-level n thunk)
 (let ((m (write-level)))
  (set-write-level! n)
  (thunk)
  (set-write-level! m)))

(define (run-time-error message v)
 (set! *error-message* message)
 ;; needs work: Backtracking can undo bindings to *error-v* and values on
 ;;             *error-stack*.
 (set! *error-v* v)
 (set! *error-stack* (map identity *stack*))
 (fail))

(define (call callee argument)
 (let ((callee (generic-zero-dereference-as-procedure callee)))
  (unless (vlad-procedure? callee)
   (run-time-error "Target is not a procedure" callee))
  ;; needs work
  ;;(set! *stack* (cons (list callee argument) *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((closure? callee) *trace-closures?*)
	      ((recursive-closure? callee) *trace-recursive-closures?*)
	      (else (fuck-up)))
   (if *trace-argument/result?*
       (format #t "~aentering ~a ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee)
	       (externalize argument))
       (format #t "~aentering ~a~%"
	       (make-string *trace-level* #\space)
	       (name callee)))
   ;; needs work
   ;;(set! *trace-level* (+ *trace-level* 1))
   )
  (let ((result
	 (cond
	  ((primitive-procedure? callee)
	   ((primitive-procedure-procedure callee) argument))
	  ((closure? callee)
	   (evaluate (closure-body callee) argument (closure-values callee)))
	  ((recursive-closure? callee)
	   (evaluate
	    (vector-ref (recursive-closure-bodies callee)
			(recursive-closure-index callee))
	    argument
	    (vector-append (map-n-vector
			    (lambda (i)
			     (make-recursive-closure
			      (recursive-closure-values callee)
			      (recursive-closure-procedure-variables callee)
			      (recursive-closure-argument-variables callee)
			      (recursive-closure-bodies callee)
			      i))
			    (vector-length (recursive-closure-bodies callee)))
			   (recursive-closure-values callee))))
	  (else (fuck-up)))))
   ;; needs work
   ;;(set! *stack* (rest *stack*))
   (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	       ((closure? callee) *trace-closures?*)
	       ((recursive-closure? callee) *trace-recursive-closures?*)
	       (else (fuck-up)))
    ;; needs work
    ;;(set! *trace-level* (- *trace-level* 1))
    (if *trace-argument/result?*
	(format #t "~aexiting ~a ~s~%"
		(make-string *trace-level* #\space)
		(name callee)
		(externalize result))
	(format #t "~aexiting ~a~%"
		(make-string *trace-level* #\space)
		(name callee))))
   result)))

(define (evaluate e v vs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (cond
  ((variable-access-expression? e)
   (lookup (variable-access-expression-index e)))
  ((application? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((callee (evaluate (application-callee e) v vs))
	  (argument (evaluate (application-argument e) v vs)))
    (call callee argument)))
  ((lambda-expression? e)
   (make-closure (lambda-expression-name e)
		 (map-vector lookup (lambda-expression-free-variables e))
		 (lambda-expression-variable e)
		 (lambda-expression-body e)))
  ((letrec-expression? e)
   (evaluate (letrec-expression-body e)
	     v
	     (vector-append
	      (let ((vs (map-vector
			 lookup (letrec-expression-bodies-free-variables e))))
	       (map-n-vector (lambda (i)
			      (make-recursive-closure
			       vs
			       (letrec-expression-procedure-variables e)
			       (letrec-expression-argument-variables e)
			       (letrec-expression-bodies e)
			       i))
			     (vector-length (letrec-expression-bodies e))))
	      (map-vector lookup (letrec-expression-body-free-variables e)))))
  (else (fuck-up))))

(define (divide x1 x2)
 ;; An approximation of IEEE since Scheme->C hides it. Doesn't handle positive
 ;; vs. negative zero x2.
 (if (zero? x2)
     (cond ((positive? x1) infinity)
	   ((negative? x1) minus-infinity)
	   ;; Both zeros and nan.
	   (else nan))
     (/ x1 x2)))

(define (unary-real f s)
 (lambda (x)
  (let ((x (generic-zero-dereference-as-real x)))
   (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x))))

(define (binary f s)
 (lambda (x)
  (let ((x (generic-zero-dereference-as-pair x)))
   (unless (pair? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f (car x) (cdr x)))))

(define (binary-real f s)
 (lambda (x)
  (let ((x (generic-zero-dereference-as-pair x)))
   (unless (pair? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
   (let ((x1 (generic-zero-dereference-as-real (car x)))
	 (x2 (generic-zero-dereference-as-real (cdr x))))
    (unless (and (real? x1) (real? x2))
     (run-time-error (format #f "Invalid argument to ~a" s) x))
    (f x1 x2)))))

(define (same? v1 v2)
 (or (and (null? v1) (null? v2))
     (and (boolean? v1) (boolean? v2) (eq? v1 v2))
     (and (real? v1) (real? v2) (= v1 v2))
     (and (pair? v1)
	  (pair? v2)
	  (same? (car v1) (car v2))
	  (same? (cdr v1) (cdr v2)))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (closure? v1)
	  (closure? v2)
	  (eq? (closure-body v1) (closure-body v2))
	  (every-vector same? (closure-values v1) (closure-values v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (= (vector-length (recursive-closure-bodies v1))
	     (vector-length (recursive-closure-bodies v2)))
	  (= (recursive-closure-index v1) (recursive-closure-index v2))
	  (every-vector eq?
			(recursive-closure-bodies v1)
			(recursive-closure-bodies v2))
	  (every-vector same?
			(recursive-closure-values v1)
			(recursive-closure-values v2)))))

(define (equal?-primitive curried-equal?
			  =
			  null?
			  boolean?
			  real?
			  pair?
			  car
			  cdr
			  cons-procedure
			  if-procedure
			  true
			  false
			  v1
			  v2)
 (cond
  ((generic-zero? v1)
   (equal?-primitive curried-equal?
		     =
		     null?
		     boolean?
		     real?
		     pair?
		     car
		     cdr
		     cons-procedure
		     if-procedure
		     true
		     false
		     (generic-zero-dereference v1)
		     v2))
  ((generic-zero? v2)
   (equal?-primitive curried-equal?
		     =
		     null?
		     boolean?
		     real?
		     pair?
		     car
		     cdr
		     cons-procedure
		     if-procedure
		     true
		     false
		     v1
		     (generic-zero-dereference v2)))
  (else
   ;; The expansion of or here is nonstandard and particular to the case where
   ;; all of the subexpressions return a boolean.
   (if
    (call (call (call (call if-procedure (call null? v1))
		      (make-primitive-procedure
		       "equal?-primitive internal 0"
		       (lambda (x)
			(call (call (call (call if-procedure (call null? v2))
					  (make-primitive-procedure
					   "equal?-primitive internal 1"
					   (lambda (x) #t)))
				    (make-primitive-procedure
				     "equal?-primitive internal 2"
				     (lambda (x) #f)))
			      '()))))
		(make-primitive-procedure
		 "equal?-primitive internal 3"
		 (lambda (x) #f)))
	  '())
    (call true '())
    (if
     (call
      (call
       (call
	(call if-procedure (call boolean? v1))
	(make-primitive-procedure
	 "equal?-primitive internal 4"
	 (lambda (x)
	  (call
	   (call
	    (call
	     (call if-procedure (call boolean? v2))
	     (make-primitive-procedure
	      "equal?-primitive internal 5"
	      (lambda (x)
	       (call
		(call (call (call if-procedure v1)
			    (make-primitive-procedure
			     "equal?-primitive internal 6"
			     (lambda (x)
			      (call (call (call (call if-procedure v2)
						(make-primitive-procedure
						 "equal?-primitive internal 7"
						 (lambda (x) #t)))
					  (make-primitive-procedure
					   "equal?-primitive internal 8"
					   (lambda (x) #f)))
				    '()))))
		      (make-primitive-procedure
		       "equal?-primitive internal 9"
		       (lambda (x)
			(call (call (call (call if-procedure v2)
					  (make-primitive-procedure
					   "equal?-primitive internal 10"
					   (lambda (x) #f)))
				    (make-primitive-procedure
				     "equal?-primitive internal 11"
				     (lambda (x) #t)))
			      '()))))
		'()))))
	    (make-primitive-procedure
	     "equal?-primitive internal 12"
	     (lambda (x) #f)))
	   '()))))
       (make-primitive-procedure
	"equal?-primitive internal 13"
	(lambda (x) #f)))
      '())
     (call true '())
     (if
      (call
       (call
	(call
	 (call if-procedure (call real? v1))
	 (make-primitive-procedure
	  "equal?-primitive internal 14"
	  (lambda (x)
	   (call
	    (call
	     (call
	      (call if-procedure (call real? v2))
	      (make-primitive-procedure
	       "equal?-primitive internal 15"
	       (lambda (x)
		(call
		 (call (call (call if-procedure
				   (call = (call (call cons-procedure v1) v2)))
			     (make-primitive-procedure
			      "equal?-primitive internal 16"
			      (lambda (x) #t)))
		       (make-primitive-procedure
			"equal?-primitive internal 17"
			(lambda (x) #f)))
		 '()))))
	     (make-primitive-procedure
	      "equal?-primitive internal 18"
	      (lambda (x) #f)))
	    '()))))
	(make-primitive-procedure
	 "equal?-primitive internal 19"
	 (lambda (x) #f)))
       '())
      (call true '())
      (if
       (call
	(call
	 (call
	  (call if-procedure (call pair? v1))
	  (make-primitive-procedure
	   "equal?-primitive internal 20"
	   (lambda (x)
	    (call
	     (call
	      (call
	       (call if-procedure (call pair? v2))
	       (make-primitive-procedure
		"equal?-primitive internal 21"
		(lambda (x)
		 (call
		  (call
		   (call
		    (call if-procedure
			  (call (call curried-equal? (call car v1))
				(call car v2)))
		    (make-primitive-procedure
		     "equal?-primitive internal 22"
		     (lambda (x)
		      (call
		       (call
			(call (call if-procedure
				    (call (call curried-equal? (call cdr v1))
					  (call cdr v2)))
			      (make-primitive-procedure
			       "equal?-primitive internal 23"
			       (lambda (x) #t)))
			(make-primitive-procedure
			 "equal?-primitive internal 24"
			 (lambda (x) #f)))
		       '()))))
		   (make-primitive-procedure
		    "equal?-primitive internal 25"
		    (lambda (x) #f)))
		  '()))))
	      (make-primitive-procedure
	       "equal?-primitive internal 26"
	       (lambda (x) #f)))
	     '()))))
	 (make-primitive-procedure
	  "equal?-primitive internal 27"
	  (lambda (x) #f)))
	'())
       (call true '())
       (if
	(and (primitive-procedure? v1)
	     (primitive-procedure? v2)
	     (eq? v1 v2))
	(call true '())
	(if
	 (if (and (closure? v1)
		  (closure? v2)
		  (eq? (closure-body v1) (closure-body v2)))
	     (let loop ((i 0))
	      (if (>= i (vector-length (closure-values v1)))
		  #t
		  (call
		   (call
		    (call
		     (call
		      if-procedure
		      (call
		       (call curried-equal? (vector-ref (closure-values v1) i))
		       (vector-ref (closure-values v2) i)))
		     (make-primitive-procedure
		      "equal?-primitive internal 28"
		      (lambda (x) (loop (+ i 1)))))
		    (make-primitive-procedure
		     "equal?-primitive internal 29"
		     (lambda (x) #f)))
		   '())))
	     #f)
	 (call true '())
	 (if (and (recursive-closure? v1)
		  (recursive-closure? v2)
		  (= (vector-length (recursive-closure-bodies v1))
		     (vector-length (recursive-closure-bodies v2)))
		  (= (recursive-closure-index v1) (recursive-closure-index v2))
		  (every-vector eq?
				(recursive-closure-bodies v1)
				(recursive-closure-bodies v2)))
	     (let loop ((i 0))
	      (if (>= i (vector-length (recursive-closure-values v1)))
		  (call true '())
		  (call
		   (call
		    (call
		     (call
		      if-procedure
		      (call (call curried-equal?
				  (vector-ref (recursive-closure-values v1) i))
			    (vector-ref (recursive-closure-values v2) i)))
		     (make-primitive-procedure
		      "equal?-primitive internal 30"
		      (lambda (x) (loop (+ i 1)))))
		    (make-primitive-procedure
		     "equal?-primitive internal 31"
		     (lambda (x) (call false '()))))
		   '())))
	     (call false '())))))))))))

(define (vlad-procedure? v)
 (or (primitive-procedure? v) (closure? v) (recursive-closure? v)))

(define (plus-primitive
	 curried-plus
	 +
	 null?
	 real?
	 pair?
	 procedure?
	 car
	 cdr
	 cons-procedure
	 if-procedure
	 ;; Can't use null because it is defined as the constant 0.
	 null-procedure
	 false
	 v1
	 v2)
 (let* ((v (generic-zero-conforming-dereference v1 v2))
	(v1 (car v))
	(v2 (cdr v)))
  (if (and (generic-zero-unbound? v1) (generic-zero-unbound? v2))
      v1
      (call
       (call
	(call (call if-procedure
		    (call (call (call (call if-procedure (call null? v1))
				      (make-primitive-procedure
				       "plus-primitive internal 0"
				       (lambda (x) (call null? v2))))
				(make-primitive-procedure
				 "plus-primitive internal 1"
				 (lambda (x) (call false '()))))
			  '()))
	      (make-primitive-procedure
	       "plus-primitive internal 2"
	       (lambda (x) (call null-procedure '()))))
	(make-primitive-procedure
	 "plus-primitive internal 3"
	 (lambda (x)
	  (call
	   (call
	    (call (call if-procedure
			(call (call (call (call if-procedure (call real? v1))
					  (make-primitive-procedure
					   "plus-primitive internal 4"
					   (lambda (x) (call real? v2))))
				    (make-primitive-procedure
				     "plus-primitive internal 5"
				     (lambda (x) (call false '()))))
			      '()))
		  (make-primitive-procedure
		   "plus-primitive internal 6"
		   (lambda (x) (call + (call (call cons-procedure v1) v2)))))
	    (make-primitive-procedure
	     "plus-primitive internal 7"
	     (lambda (x)
	      (call
	       (call
		(call
		 (call
		  if-procedure
		  (call
		   (call
		    (call
		     (call if-procedure (call pair? v1))
		     (make-primitive-procedure
		      "plus-primitive internal 8"
		      (lambda (x) (call pair? v2))))
		    (make-primitive-procedure
		     "plus-primitive internal 9"
		     (lambda (x) (call false '()))))
		   '()))
		 (make-primitive-procedure
		  "plus-primitive internal 10"
		  (lambda (x)
		   (call
		    (call
		     cons-procedure
		     (call (call curried-plus (call car v1)) (call car v2)))
		    (call (call curried-plus (call cdr v1)) (call cdr v2))))))
		(make-primitive-procedure
		 "plus-primitive internal 11"
		 (lambda (x)
		  (call
		   (call
		    (call
		     (call
		      if-procedure
		      (call
		       (call
			(call
			 (call if-procedure (call procedure? v1))
			 (make-primitive-procedure
			  "plus-primitive internal 12"
			  (lambda (x) (call procedure? v2))))
			(make-primitive-procedure
			 "plus-primitive internal 13"
			 (lambda (x) (call false '()))))
		       '()))
		     (make-primitive-procedure
		      "plus-primitive internal 14"
		      (lambda (x)
		       (make-closure
			"plus primitive"
			(vector curried-plus v1 v2)
			'y
			(make-application
			 (make-application
			  (make-variable-access-expression 'curried-plus 0)
			  (make-application
			   (make-variable-access-expression 'v1 1)
			   (make-variable-access-expression 'y -1)))
			 (make-application
			  (make-variable-access-expression 'v2 2)
			  (make-variable-access-expression 'y -1)))))))
		    (make-primitive-procedure
		     "plus-primitive internal 15"
		     (lambda (x)
		      (run-time-error
		       "Invalid argument to plus-primitive" (cons v1 v2)))))
		   '()))))
	       '()))))
	   '()))))
       '()))))

(define (define-primitive-constant x value)
 (set! *basis-constants* (cons x *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding x (make-variable-access-expression x #f))
	     *variable-bindings*))
 (set! *value-bindings* (cons (make-value-binding x value) *value-bindings*)))

(define (define-primitive-procedure x procedure)
 (define-primitive-constant x (make-primitive-procedure x procedure)))

(define (initialize-basis!)
 (define-primitive-procedure '+ (binary-real + "+"))
 (define-primitive-procedure '- (binary-real - "-"))
 (define-primitive-procedure '* (binary-real * "/"))
 (define-primitive-procedure '/ (binary-real divide "/"))
 (define-primitive-procedure 'sqrt (unary-real sqrt "sqrt"))
 (define-primitive-procedure 'exp (unary-real exp "exp"))
 (define-primitive-procedure 'log (unary-real log "log"))
 (define-primitive-procedure 'sin (unary-real sin "sin"))
 (define-primitive-procedure 'cos (unary-real cos "cos"))
 (define-primitive-procedure 'atan (binary-real atan "atan"))
 (define-primitive-procedure '= (binary-real = "="))
 (define-primitive-procedure '< (binary-real < "<"))
 (define-primitive-procedure '> (binary-real > ">"))
 (define-primitive-procedure '<= (binary-real <= "<="))
 (define-primitive-procedure '>= (binary-real >= ">="))
 (define-primitive-procedure 'zero? (unary-real zero? "zero?"))
 (define-primitive-procedure 'positive? (unary-real positive? "positive?"))
 (define-primitive-procedure 'negative? (unary-real negative? "negative?"))
 (define-primitive-procedure 'null? generic-zero-dereference-maybe-null?)
 (define-primitive-procedure 'boolean? boolean?)
 (define-primitive-procedure 'real? generic-zero-dereference-maybe-real?)
 (define-primitive-procedure 'pair? generic-zero-dereference-maybe-pair?)
 (define-primitive-procedure 'procedure?
  generic-zero-dereference-maybe-procedure?)
 (define-primitive-procedure 'car (binary (lambda (x1 x2) x1) "car"))
 (define-primitive-procedure 'cdr (binary (lambda (x1 x2) x2) "cdr"))
 (define-primitive-procedure 'cons-procedure
  ;; Note that we can't apply a j operator to the result of (cons-procedure e)
  ;; or compare results of (cons-procedure e) with equal?-primitive.
  (lambda (x1)
   (make-primitive-procedure "cons-procedure" (lambda (x2) (cons x1 x2)))))
 (define-primitive-procedure 'if-procedure
  ;; Note that we can't apply a j operator to the result of (if-procedure e1)
  ;; or ((if-procedure e1) e2) or compare results of (if-procedure e1) or
  ;; ((if-procedure e1) e2) with equal?-primitive.
  (lambda (x1)
   (make-primitive-procedure
    "if-procedure 0"
    (lambda (x2)
     (make-primitive-procedure
      "if-procedure 1" (lambda (x3) (if x1 x2 x3)))))))
 (define-primitive-procedure 'equal?-primitive
  ;; Note that we can't apply a j operator to the result of
  ;; (equal?-primitive e1), ... or compare results of (equal?-primitive e1),
  ;; ... with equal?-primitive.
  (lambda (x1)
   (make-primitive-procedure
    "equal?-primitive 0"
    (lambda (x2)
     (make-primitive-procedure
      "equal?-primitive 1"
      (lambda (x3)
       (make-primitive-procedure
	"equal?-primitive 2"
	(lambda (x4)
	 (make-primitive-procedure
	  "equal?-primitive 3"
	  (lambda (x5)
	   (make-primitive-procedure
	    "equal?-primitive 4"
	    (lambda (x6)
	     (make-primitive-procedure
	      "equal?-primitive 5"
	      (lambda (x7)
	       (make-primitive-procedure
		"equal?-primitive 6"
		(lambda (x8)
		 (make-primitive-procedure
		  "equal?-primitive 7"
		  (lambda (x9)
		   (make-primitive-procedure
		    "equal?-primitive 8"
		    (lambda (x10)
		     (make-primitive-procedure
		      "equal?-primitive 9"
		      (lambda (x11)
		       (make-primitive-procedure
			"equal?-primitive 10"
			(lambda (x12)
			 (make-primitive-procedure
			  "equal?-primitive 11"
			  (lambda (x13)
			   (make-primitive-procedure
			    "equal?-primitive 12"
			    (lambda (x14)
			     (equal?-primitive
			      x1
			      x2
			      x3
			      x4
			      x5
			      x6
			      x7
			      x8
			      x9
			      x10
			      x11
			      x12
			      x13
			      x14)))))))))))))))))))))))))))))
 (define-primitive-procedure 'map-closure
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure" x))
   (cond ((closure? (cdr x))
	  (make-closure
	   `(map-closure ,(name (car x)) ,(closure-name (cdr x)))
	   (map-vector (lambda (v) (call (car x) v)) (closure-values (cdr x)))
	   (closure-variable (cdr x))
	   (closure-body (cdr x))))
	 ((recursive-closure? (cdr x))
	  (make-recursive-closure
	   (map-vector (lambda (v) (call (car x) v))
		       (recursive-closure-values (cdr x)))
	   (recursive-closure-procedure-variables (cdr x))
	   (recursive-closure-argument-variables (cdr x))
	   (recursive-closure-bodies (cdr x))
	   (recursive-closure-index (cdr x))))
	 (else (run-time-error "Invalid argument to map-closure" x)))))
 (define-primitive-procedure 'zero (lambda (x) (create-generic-zero)))
 (define-primitive-procedure 'plus-primitive
  ;; Note that we can't apply a j operator to the result of
  ;; (plus-primitive e1), ... or compare results of (plus-primitive e1), ...
  ;; with equal?-primitive.
  (lambda (x1)
   (make-primitive-procedure
    "plus-primitive 0"
    (lambda (x2)
     (make-primitive-procedure
      "plus-primitive 1"
      (lambda (x3)
       (make-primitive-procedure
	"plus-primitive 2"
	(lambda (x4)
	 (make-primitive-procedure
	  "plus-primitive 3"
	  (lambda (x5)
	   (make-primitive-procedure
	    "plus-primitive 4"
	    (lambda (x6)
	     (make-primitive-procedure
	      "plus-primitive 5"
	      (lambda (x7)
	       (make-primitive-procedure
		"plus-primitive 6"
		(lambda (x8)
		 (make-primitive-procedure
		  "plus-primitive 7"
		  (lambda (x9)
		   (make-primitive-procedure
		    "plus-primitive 8"
		    (lambda (x10)
		     (make-primitive-procedure
		      "plus-primitive 9"
		      (lambda (x11)
		       (make-primitive-procedure
			"plus-primitive 10"
			(lambda (x12)
			 (make-primitive-procedure
			  "plus-primitive 11"
			  (lambda (x13)
			   (make-primitive-procedure
			    "plus-primitive 12"
			    (lambda (x14)
			     (plus-primitive
			      x1
			      x2
			      x3
			      x4
			      x5
			      x6
			      x7
			      x8
			      x9
			      x10
			      x11
			      x12
			      x13
			      x14)))))))))))))))))))))))))))))
 (define-primitive-procedure 'write
  (lambda (x) (write (externalize x)) (newline) x)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
