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
;;;  1. list* or multiarg cons both as expression and as parameter
;;;  2. spread arguments should be lists
;;;  3. unary -
;;;  4. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  5. chars, ports, eof object, symbols, continuations, strings, vectors
;;;  6. enforce don't shadow: car, cdr, cons-procedure, and if-procedure

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

(define-structure lambda-expression
 variable free-variables free-variable-indices body)

(define-structure letrec-expression
 procedure-variables
 argument-variables
 bodies-free-variables
 bodies-free-variable-indices
 body-free-variables
 body-free-variable-indices
 bodies
 body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure closure variables values variable body)

(define-structure recursive-closure
 variables values procedure-variables argument-variables bodies index)

(define-structure primitive-procedure name procedure meter)

;;; Variables

(define *gensym* 0)

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

;;; Parameters

(define *include-path* '())

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

;;; Procedures

(define (create-primitive-procedure name procedure)
 (make-primitive-procedure name procedure 0))

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

(define (consify-parameters ps)
 (cond ((null? ps) (gensym))
       ((null? (rest ps)) (first ps))
       (else `(cons ,(first ps) ,(consify-parameters (rest ps))))))

(define (consify-expressions es)
 (cond ((null? es) ''())
       ((null? (rest es)) (first es))
       (else `(cons ,(first es) ,(consify-expressions (rest es))))))

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
       ((0) (loop `(lambda (,(consify-parameters (second e))) ,(third e)) xs))
       ((1) (syntax-check-parameter! (first (second e)))
	    (let ((xs0 (parameter-variables (first (second e)))))
	     (when (duplicatesq? xs0)
	      (panic (format #f "Duplicate variables: ~s" e)))
	     (loop (third e) (append xs0 xs))))
       (else
	(loop `(lambda (,(consify-parameters (second e))) ,(third e)) xs))))
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
     ((if)
      (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
      (loop `((((if-procedure ,(second e)) (lambda () ,(third e)))
	       (lambda () ,(fourth e))))
	    xs))
     ;; needs work: to ensure that you don't shadow cons-procedure
     ((cons)
      (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
      (loop `((cons-procedure ,(second e)) ,(third e)) xs))
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
     (else (case (length (rest e))
	    ((0) (loop `(,(first e) ,(consify-expressions (rest e))) xs))
	    ((1) (loop (first e) xs)
		 (loop (second e) xs))
	    (else (loop `(,(first e) ,(consify-expressions (rest e))) xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (abstract->concrete e)
 (cond ((variable-access-expression? e)
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
       (lambda-expression-variable e) #f #f (loop (lambda-expression-body e))))
     ((letrec-expression? e)
      (make-letrec-expression (letrec-expression-procedure-variables e)
			      (letrec-expression-argument-variables e)
			      #f
			      #f
			      #f
			      #f
			      (map-vector loop (letrec-expression-bodies e))
			      (loop (letrec-expression-body e))))
     (else (fuck-up))))
   (map first bss))))

(define (unionq-vector xs1 xs2)
 (list->vector (unionq (vector->list xs1) (vector->list xs2))))

(define (removeq-vector x xs) (list->vector (removeq x (vector->list xs))))

(define (set-differenceq-vector xs1 xs2)
 (list->vector (set-differenceq (vector->list xs1) (vector->list xs2))))

(define (annotate-free-variables e)
 (first
  (let loop ((e e))
   (cond ((variable-access-expression? e)
	  (list e (vector (variable-access-expression-variable e))))
	 ((application? e)
	  (let ((result1 (loop (application-callee e)))
		(result2 (loop (application-argument e))))
	   (list (make-application (first result1) (first result2))
		 (unionq-vector (second result1) (second result2)))))
	 ((lambda-expression? e)
	  (let* ((result (loop (lambda-expression-body e)))
		 (xs (removeq-vector (lambda-expression-variable e)
				     (second result))))
	   (list (make-lambda-expression
		  (lambda-expression-variable e) xs #f (first result))
		 xs)))
	 ((letrec-expression? e)
	  (let* ((results (map-vector loop (letrec-expression-bodies e)))
		 (result (loop (letrec-expression-body e)))
		 (xs (set-differenceq-vector
		      (unionq-vector
		       (reduce-vector
			unionq-vector
			(map-vector
			 (lambda (x result)
			  (removeq-vector x (second result)))
			 (letrec-expression-argument-variables e)
			 results)
			'#())
		       (second result))
		      (letrec-expression-procedure-variables e))))
	   (list (make-letrec-expression
		  (letrec-expression-procedure-variables e)
		  (letrec-expression-argument-variables e)
		  (set-differenceq-vector
		   (reduce-vector
		    unionq-vector
		    (map-vector
		     (lambda (x result) (removeq-vector x (second result)))
		     (letrec-expression-argument-variables e)
		     results)
		    '#())
		   (letrec-expression-procedure-variables e))
		  #f
		  xs
		  #f
		  (map-vector first results)
		  (first result))
		 xs)))
	 (else (fuck-up))))))

(define (free-variables-in e)
 (cond ((variable-access-expression? e)
	(vector (variable-access-expression-variable e)))
       ((application? e)
	(unionq-vector (free-variables-in (application-callee e))
		       (free-variables-in (application-argument e))))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       ((letrec-expression? e) (letrec-expression-body-free-variables e))
       (else (fuck-up))))

(define (vector-append vs1 vs2)
 (list->vector (append (vector->list vs1) (vector->list vs2))))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (eq? x-prime x) (memq x-prime (vector->list xs))) (fuck-up))
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
     (lambda-expression-variable e)
     xs
     (map-vector lookup xs)
     (index (lambda-expression-variable e) xs (lambda-expression-body e)))))
  ((letrec-expression? e)
   (let ((xs1 (letrec-expression-bodies-free-variables e))
	 (xs2 (letrec-expression-body-free-variables e)))
    (make-letrec-expression
     (letrec-expression-procedure-variables e)
     (letrec-expression-argument-variables e)
     xs1
     (map-vector lookup xs1)
     xs2
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
	 (let loop ((e e) (bs *variable-bindings*))
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
	       ((0)
		(loop `(lambda (,(consify-parameters (second e))) ,(third e))
		      bs))
	       ((1)
		(let* ((x (concrete->abstract-parameter (first (second e))))
		       (result (loop (third e)
				     (append (parameter-variable-bindings
					      x (first (second e)))
					     bs))))
		 (list (make-lambda-expression x #f #f (first result))
		       (second result))))
	       (else
		(loop `(lambda (,(consify-parameters (second e))) ,(third e))
		      bs))))
	     ((letrec)
	      (let* ((bs
		      (append
		       (map (lambda (b)
			     (make-variable-binding
			      (first b)
			      (make-variable-access-expression (first b) #f)))
			    (second e))
		       bs))
		     (results (map (lambda (b) (loop (second b) bs))
				   (second e)))
		     (result (loop (third e) bs))
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
		 #f
		 #f
		 #f
		 #f
		 (list->vector es)
		 e)
		(append
		 (second result) (reduce append (map second results) '())))))
	     ((let) (loop `((lambda ,(map first (second e)) ,(third e))
			    ,@(map second (second e)))
			  bs))
	     ((let*) (case (length (second e))
		      ((0) (loop (third e) bs))
		      ((1) (loop `(let ,(second e) ,(third e)) bs))
		      (else (loop `(let (,(first (second e)))
				    (let* ,(rest (second e)) ,(third e)))
				  bs))))
	     ;; needs work: to ensure that you don't shadow if-procedure
	     ((if) (loop `((((if-procedure ,(second e)) (lambda () ,(third e)))
			    (lambda () ,(fourth e))))
			 bs))
	     ;; needs work: to ensure that you don't shadow cons-procedure
	     ((cons) (loop `((cons-procedure ,(second e)) ,(third e)) bs))
	     ((list) (loop (if (null? (rest e))
			       ''()
			       `(cons ,(second e) (list ,@(rest (rest e)))))
			   bs))
	     ((cond) (loop (if (null? (rest (rest e)))
			       (second (second e))
			       `(if ,(first (second e))
				    ,(second (second e))
				    (cond ,@(rest (rest e)))))
			   bs))
	     ((and) (loop (case (length (rest e))
			   ((0) #t)
			   ((1) (second e))
			   (else `(if ,(second e) (and ,@(rest (rest e))) #f)))
			  bs))
	     ((or) (loop (case (length (rest e))
			  ((0) #f)
			  ((1) (second e))
			  (else (let ((x (gensym)))
				 `(let ((,x ,(second e)))
				   (if ,x ,x (or ,@(rest (rest e))))))))
			 bs))
	     (else
	      (case (length (rest e))
	       ((0) (loop `(,(first e) ,(consify-expressions (rest e))) bs))
	       ((1) (let ((result1 (loop (first e) bs))
			  (result2 (loop (second e) bs)))
		     (list (make-application (first result1) (first result2))
			   (append (second result1) (second result2)))))
	       (else
		(loop `(,(first e) ,(consify-expressions (rest e))) bs))))))
	   (else (fuck-up)))))
	(e (annotate-free-variables (first result)))
	(xs (vector->list (free-variables-in e)))
	(bs (remove-if-not (lambda (b) (memq (value-binding-variable b) xs))
			   (append *value-bindings* (second result))))
	(result (coalesce-constants (list e bs)))
	(e (annotate-free-variables (first result)))
	(xs (list->vector (map value-binding-variable (second result)))))
  (list (index 'argv xs e)
	(list->vector (map value-binding-value (second result))))))

;;; J* and *J

(define (basis-value x)
 (value-binding-value
  (find-if (lambda (b) (eq? (value-binding-variable b) x)) *value-bindings*)))

(define (make-car e)
 ;; This is a simple optimization.
 (if (and (application? e)
	  (application? (application-callee e))
	  (variable-access-expression?
	   (application-callee (application-callee e)))
	  (eq? (variable-access-expression-variable
		(application-callee (application-callee e)))
	       (basis-value 'cons-procedure)))
     (application-argument (application-callee e))
     (make-application
      (make-variable-access-expression (basis-value 'car) #f) e)))

(define (make-cdr e)
 (make-application (make-variable-access-expression (basis-value 'cdr) #f) e))

(define (make-cons e1 e2)
 (make-application
  (make-application
   (make-variable-access-expression (basis-value 'cons-procedure) #f) e1)
  e2))

(define (make-zero e)
 (make-application (make-variable-access-expression (basis-value 'zero) #f) e))

(define (basis-values e)
 (cond ((variable-access-expression? e)
	(if (symbol? (variable-access-expression-variable e))
	    '()
	    (list (variable-access-expression-variable e))))
       ((application? e)
	(unionq (basis-values (application-callee e))
		(basis-values (application-argument e))))
       ((lambda-expression? e) (basis-values (lambda-expression-body e)))
       ((letrec-expression? e)
	(unionq
	 (reduce-vector unionq
			(map-vector basis-values (letrec-expression-bodies e))
			'())
	 (basis-values (letrec-expression-body e))))
       (else (fuck-up))))

(define (replace-basis-values e bs)
 (let loop ((e e))
  (cond ((variable-access-expression? e)
	 (if (symbol? (variable-access-expression-variable e))
	     e
	     (make-variable-access-expression
	      (value-binding-variable
	       (find-if (lambda (b)
			 (eq? (value-binding-value b)
			      (variable-access-expression-variable e)))
			bs))
	      #f)))
	((application? e)
	 (make-application (loop (application-callee e))
			   (loop (application-argument e))))
	((lambda-expression? e)
	 (make-lambda-expression
	  (lambda-expression-variable e)
	  (lambda-expression-free-variables e)
	  (lambda-expression-free-variable-indices e)
	  (loop (lambda-expression-body e))))
	((letrec-expression? e)
	 (make-letrec-expression
	  (letrec-expression-procedure-variables e)
	  (letrec-expression-argument-variables e)
	  (letrec-expression-bodies-free-variables e)
	  (letrec-expression-bodies-free-variable-indices e)
	  (letrec-expression-body-free-variables e)
	  (letrec-expression-body-free-variable-indices e)
	  (map-vector loop (letrec-expression-bodies e))
	  (loop (letrec-expression-body e))))
	(else (fuck-up)))))

(define (forward-transform e x0 xs)
 (define (bound? x) (or (eq? x x0) (memq x xs)))
 (cond ((variable-access-expression? e)
	(if (bound? (variable-access-expression-variable e))
	    e
	    (make-cons e (make-zero e))))
       ((application? e)
	(make-application
	 (make-car (forward-transform (application-callee e) x0 xs))
	 (forward-transform (application-argument e) x0 xs)))
       ((lambda-expression? e)
	(make-cons (make-lambda-expression
		    (lambda-expression-variable e)
		    #f
		    #f
		    (forward-transform (lambda-expression-body e)
				       (lambda-expression-variable e)
				       (cons x0 xs)))
		   (make-variable-access-expression '() #f)))
       ((letrec-expression? e)
	(make-letrec-expression
	 (letrec-expression-procedure-variables e)
	 (letrec-expression-argument-variables e)
	 #f
	 #f
	 #f
	 #f
	 (map-vector (lambda (x e) (forward-transform e x (cons x0 xs)))
		     (letrec-expression-argument-variables e)
		     (letrec-expression-bodies e))
	 (forward-transform (letrec-expression-body e) x0 xs)))
       (else (fuck-up))))

(define (reverse-transform e x0 xs)
 (define (bound? x) (or (eq? x x0) (memq x xs)))
 (cond ((variable-access-expression? e)
	(if (bound? (variable-access-expression-variable e))
	    e
	    (make-cons
	     e
	     (make-lambda-expression
	      (gensym)
	      #f
	      #f
	      ;; This is just to create a zero of the shape of the ultimate
	      ;; input.
	      (make-application
	       ;; The destructuring is implicit in the document.
	       (make-cdr (make-variable-access-expression x0 #f))
	       (make-zero
		;; The destructuring is implicit in the document.
		(make-car (make-variable-access-expression x0 #f))))))))
       ((application? e)
	(make-application
	 (make-car (reverse-transform (application-callee e) x0 xs))
	 (reverse-transform (application-argument e) x0 xs)))
       ((lambda-expression? e)
	(make-cons
	 (make-lambda-expression
	  (lambda-expression-variable e)
	  #f
	  #f
	  (reverse-transform (lambda-expression-body e)
			     (lambda-expression-variable e)
			     (cons x0 xs)))
	 (make-lambda-expression
	  (gensym)
	  #f
	  #f
	  ;; This is just to create a zero of the shape of the ultimate
	  ;; input.
	  (make-application
	   ;; The destructuring is implicit in the document.
	   (make-cdr (make-variable-access-expression x0 #f))
	   ;; The destructuring is implicit in the document.
	   (make-zero (make-car (make-variable-access-expression x0 #f)))))))
       ((letrec-expression? e)
	(make-letrec-expression
	 (letrec-expression-procedure-variables e)
	 (letrec-expression-argument-variables e)
	 #f
	 #f
	 #f
	 #f
	 (map-vector (lambda (x e) (reverse-transform e x (cons x0 xs)))
		     (letrec-expression-argument-variables e)
		     (letrec-expression-bodies e))
	 (reverse-transform (letrec-expression-body e) x0 xs)))
       (else (fuck-up))))

(define (transform-expression x e xs bs)
 (index x xs (annotate-free-variables (replace-basis-values e bs))))

;;; Evaluator

(define (name v)
 (cond ((primitive-procedure? v) (primitive-procedure-name v))
       ((closure? v)
	(if *unabbreviate-closures?*
	    `(closure
	      ,(map-n (lambda (i)
		       (list (vector-ref (closure-variables v) i)
			     (externalize (vector-ref (closure-values v) i))))
		      (vector-length (closure-values v)))
	      (lambda (,(closure-variable v))
	       ,(abstract->concrete (closure-body v))))
	    `(lambda (,(closure-variable v))
	      ,(abstract->concrete (closure-body v)))))
       ((recursive-closure? v)	
	(if *unabbreviate-recursive-closures?*
	    `(recursive-closure
	      ,(map-n
		(lambda (i)
		 (list (vector-ref (recursive-closure-variables v) i)
		       (externalize
			(vector-ref (recursive-closure-values v) i))))
		(vector-length (recursive-closure-values v)))
	      ,(vector-ref (recursive-closure-procedure-variables v)
			   (recursive-closure-index v)))
	    (vector-ref (recursive-closure-procedure-variables v)
			(recursive-closure-index v))))
       (else (fuck-up))))

(define (externalize v)
 (cond ((null? v) v)
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

(define (with-write-length n thunk)
 (let ((m (write-level)))
  (set-write-length! n)
  (thunk)
  (set-write-length! m)))

(define (run-time-error message v)
 (format #t "Stack trace~%")
 (for-each (lambda (record)
	    (display "Procedure: ")
	    ((if *pp?* pp write) (name (first record)))
	    (newline)
	    (display "Argument: ")
	    ((if *pp?* pp write) (externalize (second record)))
	    (newline)
	    (newline))
	   *stack*)
 (newline)
 ((if *pp?* pp write) (externalize v))
 (newline)
 (panic message))

(define (call callee argument)
 (unless (vlad-procedure? callee)
  (run-time-error "Target is not a procedure" callee))
 (set! *stack* (cons (list callee argument) *stack*))
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
  (set! *trace-level* (+ *trace-level* 1)))
 (when (and *metered?* (primitive-procedure? callee))
  (set-primitive-procedure-meter!
   callee (+ (primitive-procedure-meter callee) 1)))
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
			     (recursive-closure-variables callee)
			     (recursive-closure-values callee)
			     (recursive-closure-procedure-variables callee)
			     (recursive-closure-argument-variables callee)
			     (recursive-closure-bodies callee)
			     i))
			   (vector-length (recursive-closure-bodies callee)))
			  (recursive-closure-values callee))))
	 (else (fuck-up)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((closure? callee) *trace-closures?*)
	      ((recursive-closure? callee) *trace-recursive-closures?*)
	      (else (fuck-up)))
   (set! *trace-level* (- *trace-level* 1))
   (if *trace-argument/result?*
       (format #t "~aexiting ~a ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee)
	       (externalize result))
       (format #t "~aexiting ~a~%"
	       (make-string *trace-level* #\space)
	       (name callee))))
  result))

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
   (make-closure
    (lambda-expression-free-variables e)
    (map-vector lookup (lambda-expression-free-variable-indices e))
    (lambda-expression-variable e)
    (lambda-expression-body e)))
  ((letrec-expression? e)
   (evaluate
    (letrec-expression-body e)
    v
    (vector-append
     (let ((xs (letrec-expression-bodies-free-variables e))
	   (vs (map-vector
		lookup (letrec-expression-bodies-free-variable-indices e))))
      (map-n-vector (lambda (i)
		     (make-recursive-closure
		      xs
		      vs
		      (letrec-expression-procedure-variables e)
		      (letrec-expression-argument-variables e)
		      (letrec-expression-bodies e)
		      i))
		    (vector-length (letrec-expression-bodies e))))
     (map-vector lookup (letrec-expression-body-free-variable-indices e)))))
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
  (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f x)))

(define (binary f s)
 (lambda (x)
  (unless (pair? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f (car x) (cdr x))))

(define (binary-real f s)
 (lambda (x)
  (unless (pair? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (car x)) (x2 (cdr x)))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 x2))))

(define (equal?-primitive =
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
 ;; The expansion of or here is nonstandard and particular to the case where
 ;; all of the subexpressions return a boolean.
 (if
  (call (call (call (call if-procedure (call null? v1))
		    (create-primitive-procedure
		     "equal?-primitive internal 0"
		     (lambda (x)
		      (call (call (call (call if-procedure (call null? v2))
					(create-primitive-procedure
					 "equal?-primitive internal 1"
					 (lambda (x) #t)))
				  (create-primitive-procedure
				   "equal?-primitive internal 2"
				   (lambda (x) #f)))
			    '()))))
	      (create-primitive-procedure
	       "equal?-primitive internal 3"
	       (lambda (x) #f)))
	'())
  (call true '())
  (if
   (call
    (call
     (call
      (call if-procedure (call boolean? v1))
      (create-primitive-procedure
       "equal?-primitive internal 4"
       (lambda (x)
	(call
	 (call
	  (call
	   (call if-procedure (call boolean? v2))
	   (create-primitive-procedure
	    "equal?-primitive internal 5"
	    (lambda (x)
	     (call
	      (call (call (call if-procedure v1)
			  (create-primitive-procedure
			   "equal?-primitive internal 6"
			   (lambda (x)
			    (call (call (call (call if-procedure v2)
					      (create-primitive-procedure
					       "equal?-primitive internal 7"
					       (lambda (x) #t)))
					(create-primitive-procedure
					 "equal?-primitive internal 8"
					 (lambda (x) #f)))
				  '()))))
		    (create-primitive-procedure
		     "equal?-primitive internal 9"
		     (lambda (x)
		      (call (call (call (call if-procedure v2)
					(create-primitive-procedure
					 "equal?-primitive internal 10"
					 (lambda (x) #f)))
				  (create-primitive-procedure
				   "equal?-primitive internal 11"
				   (lambda (x) #t)))
			    '()))))
	      '()))))
	  (create-primitive-procedure
	   "equal?-primitive internal 12"
	   (lambda (x) #f)))
	 '()))))
     (create-primitive-procedure
      "equal?-primitive internal 13"
      (lambda (x) #f)))
    '())
   (call true '())
   (if
    (call
     (call
      (call
       (call if-procedure (call real? v1))
       (create-primitive-procedure
	"equal?-primitive internal 14"
	(lambda (x)
	 (call
	  (call
	   (call
	    (call if-procedure (call real? v2))
	    (create-primitive-procedure
	     "equal?-primitive internal 15"
	     (lambda (x)
	      (call
	       (call (call (call if-procedure
				 (call = (call (call cons-procedure v1) v2)))
			   (create-primitive-procedure
			    "equal?-primitive internal 16"
			    (lambda (x) #t)))
		     (create-primitive-procedure
		      "equal?-primitive internal 17"
		      (lambda (x) #f)))
	       '()))))
	   (create-primitive-procedure
	    "equal?-primitive internal 18"
	    (lambda (x) #f)))
	  '()))))
      (create-primitive-procedure
       "equal?-primitive internal 19"
       (lambda (x) #f)))
     '())
    (call true '())
    (if
     (call
      (call
       (call
	(call if-procedure (call pair? v1))
	(create-primitive-procedure
	 "equal?-primitive internal 20"
	 (lambda (x)
	  (call
	   (call
	    (call
	     (call if-procedure (call pair? v2))
	     (create-primitive-procedure
	      "equal?-primitive internal 21"
	      (lambda (x)
	       (call
		(call
		 (call
		  (call if-procedure
			(equal?-primitive =
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
					  (call car v1)
					  (call car v2)))
		  (create-primitive-procedure
		   "equal?-primitive internal 22"
		   (lambda (x)
		    (call
		     (call
		      (call (call if-procedure
				  (equal?-primitive =
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
						    (call cdr v1)
						    (call cdr v2)))
			    (create-primitive-procedure
			     "equal?-primitive internal 23"
			     (lambda (x) #t)))
		      (create-primitive-procedure
		       "equal?-primitive internal 24"
		       (lambda (x) #f)))
		     '()))))
		 (create-primitive-procedure
		  "equal?-primitive internal 25"
		  (lambda (x) #f)))
		'()))))
	    (create-primitive-procedure
	     "equal?-primitive internal 26"
	     (lambda (x) #f)))
	   '()))))
       (create-primitive-procedure
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
		    (equal?-primitive =
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
				      (vector-ref (closure-values v1) i)
				      (vector-ref (closure-values v2) i)))
		   (create-primitive-procedure
		    "equal?-primitive internal 28"
		    (lambda (x) (loop (+ i 1)))))
		  (create-primitive-procedure
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
		    (equal?-primitive
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
		     (vector-ref (recursive-closure-values v1) i)
		     (vector-ref (recursive-closure-values v2) i)))
		   (create-primitive-procedure
		    "equal?-primitive internal 30"
		    (lambda (x) (loop (+ i 1)))))
		  (create-primitive-procedure
		   "equal?-primitive internal 31"
		   (lambda (x) (call false '()))))
		 '())))
	   (call false '())))))))))

(define (vlad-procedure? v)
 (or (primitive-procedure? v) (closure? v) (recursive-closure? v)))

(define (zero x)
 (cond ((real? x) 0)
       ((pair? x) (cons (zero (car x)) (zero (cdr x))))
       (else '())))

(define (conform? x1 x2)
 (or (and (null? x1) (null? x2))
     (and (real? x1) (real? x2))
     (and (pair? x1)
	  (pair? x2)
	  (conform? (car x1) (car x2))
	  (conform? (cdr x1) (cdr x2)))))

(define (plus x1 x2)
 (unless (conform? x1 x2) (run-time-error "nonconformance" (cons x1 x2)))
 (cond ((null? x1) '())
       ((real? x1) (+ x1 x2))
       (else (cons (plus (car x1) (car x2)) (plus (cdr x1) (cdr x2))))))

(define (define-primitive-procedure x procedure)
 (set! *basis-constants* (cons x *basis-constants*))
 (set! *variable-bindings*
       (cons (make-variable-binding x (make-variable-access-expression x #f))
	     *variable-bindings*))
 (set! *value-bindings*
       (cons (make-value-binding x (create-primitive-procedure x procedure))
	     *value-bindings*)))

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
 (define-primitive-procedure 'null? null?)
 (define-primitive-procedure 'boolean? boolean?)
 (define-primitive-procedure 'real? real?)
 (define-primitive-procedure 'pair? pair?)
 (define-primitive-procedure 'procedure? vlad-procedure?)
 (define-primitive-procedure 'car (binary (lambda (x1 x2) x1) "car"))
 (define-primitive-procedure 'cdr (binary (lambda (x1 x2) x2) "cdr"))
 (define-primitive-procedure 'cons-procedure
  ;; Note that we can't apply a j operator to the result of (cons-procedure e)
  ;; or compare results of (cons-procedure e) with equal?-primitive.
  (lambda (x1)
   (create-primitive-procedure "cons-procedure" (lambda (x2) (cons x1 x2)))))
 (define-primitive-procedure 'if-procedure
  ;; Note that we can't apply a j operator to the result of (if-procedure e1)
  ;; or ((if-procedure e1) e2) or compare results of (if-procedure e1) or
  ;; ((if-procedure e1) e2) with equal?-primitive.
  (lambda (x1)
   (create-primitive-procedure
    "if-procedure 0"
    (lambda (x2)
     (create-primitive-procedure
      "if-procedure 1" (lambda (x3) (if x1 x2 x3)))))))
 (define-primitive-procedure 'equal?-primitive
  ;; Note that we can't apply a j operator to the result of
  ;; (equal?-primitive e1), ... or compare results of (equal?-primitive e1),
  ;; ... with equal?-primitive.
  (lambda (x1)
   (create-primitive-procedure
    "equal?-primitive 0"
    (lambda (x2)
     (create-primitive-procedure
      "equal?-primitive 1"
      (lambda (x3)
       (create-primitive-procedure
	"equal?-primitive 2"
	(lambda (x4)
	 (create-primitive-procedure
	  "equal?-primitive 3"
	  (lambda (x5)
	   (create-primitive-procedure
	    "equal?-primitive 4"
	    (lambda (x6)
	     (create-primitive-procedure
	      "equal?-primitive 5"
	      (lambda (x7)
	       (create-primitive-procedure
		"equal?-primitive 6"
		(lambda (x8)
		 (create-primitive-procedure
		  "equal?-primitive 7"
		  (lambda (x9)
		   (create-primitive-procedure
		    "equal?-primitive 8"
		    (lambda (x10)
		     (create-primitive-procedure
		      "equal?-primitive 9"
		      (lambda (x11)
		       (create-primitive-procedure
			"equal?-primitive 10"
			(lambda (x12)
			 (create-primitive-procedure
			  "equal?-primitive 11"
			  (lambda (x13)
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
			    x13)))))))))))))))))))))))))))
 (define-primitive-procedure 'zero zero)
 (define-primitive-procedure 'plus (binary plus "plus"))
 (define-primitive-procedure 'map-closure-forward
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-forward" x))
   (let ((f (car x)) (g (cdr x)))
    (cond
     ((closure? g)
      (let* ((e (forward-transform (closure-body g) (closure-variable g) '()))
	     (bs (map (lambda (v) (make-value-binding (gensym) v))
		      (basis-values e)))
	     (xs (vector-append (list->vector (map value-binding-variable bs))
				(closure-variables g))))
       (make-closure
	xs
	(vector-append (list->vector (map value-binding-value bs))
		       (map-vector (lambda (v) (call f v)) (closure-values g)))
	(closure-variable g)
	(transform-expression (closure-variable g) e xs bs))))
     ((recursive-closure? g)
      (let* ((es (map-vector (lambda (x e) (forward-transform e x '()))
			     (recursive-closure-argument-variables g)
			     (recursive-closure-bodies g)))
	     (bs (map (lambda (v) (make-value-binding (gensym) v))
		      (reduce-vector unionq (map-vector basis-values es) '())))
	     (xs (vector-append (list->vector (map value-binding-variable bs))
				(recursive-closure-variables g))))
       (make-recursive-closure
	xs
	(vector-append (list->vector (map value-binding-value bs))
		       (map-vector (lambda (v) (call f v))
				   (recursive-closure-values g)))
	(recursive-closure-procedure-variables g)
	(recursive-closure-argument-variables g)
	(map-vector
	 (lambda (x e)
	  (transform-expression
	   x
	   e
	   (vector-append (recursive-closure-procedure-variables g) xs)
	   bs))
	 (recursive-closure-argument-variables g)
	 es)
	(recursive-closure-index g))))
     (else (run-time-error "Invalid argument to map-closure-forward" x))))))
 (define-primitive-procedure 'map-closure-reverse
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-reverse" x))
   (let ((f (car x)) (g (cdr x)))
    (cond
     ((closure? g)
      (let* ((e (reverse-transform (closure-body g) (closure-variable g) '()))
	     (bs (map (lambda (v) (make-value-binding (gensym) v))
		      (basis-values e)))
	     (xs (vector-append (list->vector (map value-binding-variable bs))
				(closure-variables g))))
       (make-closure
	xs
	(vector-append (list->vector (map value-binding-value bs))
		       (map-vector (lambda (v) (call f v)) (closure-values g)))
	(closure-variable g)
	(transform-expression (closure-variable g) e xs bs))))
     ((recursive-closure? g)
      (let* ((es (map-vector (lambda (x e) (reverse-transform e x '()))
			     (recursive-closure-argument-variables g)
			     (recursive-closure-bodies g)))
	     (bs (map (lambda (v) (make-value-binding (gensym) v))
		      (reduce-vector unionq (map-vector basis-values es) '())))
	     (xs (vector-append (list->vector (map value-binding-variable bs))
				(recursive-closure-variables g))))
       (make-recursive-closure
	xs
	(vector-append (list->vector (map value-binding-value bs))
		       (map-vector (lambda (v) (call f v))
				   (recursive-closure-values g)))
	(recursive-closure-procedure-variables g)
	(recursive-closure-argument-variables g)
	(map-vector
	 (lambda (x e)
	  (transform-expression
	   x
	   e
	   (vector-append (recursive-closure-procedure-variables g) xs)
	   bs))
	 (recursive-closure-argument-variables g)
	 es)
	(recursive-closure-index g))))
     (else (run-time-error "Invalid argument to map-closure-reverse" x))))))
 (define-primitive-procedure 'write
  (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
