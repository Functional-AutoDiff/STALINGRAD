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
;;;  1. unary -
;;;  2. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  3. chars, ports, eof object, symbols, continuations, strings, vectors
;;;  4. enforce don't shadow: car, cdr, cons-procedure, ys, and if-procedure

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete parameter
;;;  x: concrete variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: value
;;;  d: definition
;;;  n: key
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

;;; Structures

(define-structure variable-access-expression variable index)

(define-structure key-expression variable index)

(define-structure application callee argument)

(define-structure lambda-expression
 free-variables free-variable-indices variable body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure closure variables values keys variable body)

(define-structure primitive-procedure name procedure meter)

(define-structure key key)

;;; Variables

(define *gensym* 0)

(define *basis-constants* '())

(define *variable-bindings* '())

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *key* -1)

(define *y* #f)

(define *y-tilde* #f)

(define *y-grave* #f)

(define *r* #f)

(define *x1* #f)

(define *x1-tilde* #f)

(define *x2* #f)

(define *x2-tilde* #f)

;;; Parameters

(define *include-path* '())

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-closures?* #f)

(define *pp?* #f)

;;; Procedures

(define (new-lambda-expression x e)
 (let ((xs (removeq-vector x (free-variables e))))
  (make-lambda-expression xs #f x e)))

;;; needs work: We don't gc keys so there is a risk that we run out. We don't
;;;             check for running out of keys.
(define (create-key) (set! *key* (+ *key* 1)) (make-key *key*))

(define (create-primitive-procedure name procedure)
 (make-primitive-procedure name procedure 0))

(define (create-lambda-expression bs ps e)
 (case (length ps)
  ((0) (create-lambda-expression bs `((cons* ,@ps)) e))
  ((1) (let ((p (first ps)))
	(cond ((symbol? p) (new-lambda-expression p e))
	      ((and (list? p) (not (null? p)))
	       (case (first p)
		((cons)
		 (unless (= (length p) 3) (fuck-up))
		 (let ((x (gensym)))
		  (create-lambda-expression
		   bs
		   (list x)
		   (create-let*
		    bs
		    (list (second p) (third p))
		    (list (make-car bs (make-variable-access-expression x #f))
			  (make-cdr bs (make-variable-access-expression x #f)))
		    e))))
		((cons*)
		 (case (length (rest p))
		  ((0) (create-lambda-expression bs `(,(gensym)) e))
		  ((1) (create-lambda-expression bs `(,(second p)) e))
		  (else
		   (create-lambda-expression
		    bs `((cons ,(second p) (cons* ,@(rest (rest p))))) e))))
		((list)
		 (if (null? (rest p))
		     (create-lambda-expression bs `(,(gensym)) e)
		     (create-lambda-expression
		      bs `((cons ,(second p) (list ,@(rest (rest p))))) e)))
		(else (fuck-up))))
	      (else (fuck-up)))))
  (else (create-lambda-expression bs `((cons* ,@ps)) e))))

(define (create-application bs e . es)
 (make-application e (make-cons* bs es)))

(define (create-let bs p e1 e2)
 (create-application bs (create-lambda-expression bs (list p) e2) e1))

(define (create-let* bs ps es e)
 (if (null? ps)
     e
     (create-let
      bs (first ps) (first es) (create-let* bs (rest ps) (rest es) e))))

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

(define (standard-prelude e)
 `(let ((ys (let* ((y (lambda (f)
		       ((lambda (g) (lambda (x) ((f (g g)) x)))
			(lambda (g) (lambda (x) ((f (g g)) x))))))
		   (map (lambda (f)
			 (y (lambda (map)
			     (lambda (l)
			      (if (null? l)
				  '()
				  (cons (f (car l)) (map (cdr l))))))))))
	     (y (lambda (ys)
		 (lambda (fs)
		  ((map (lambda (f) (lambda (x) ((f (ys fs)) x)))) fs)))))))
   ,e))

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
 (standard-prelude
  `(letrec ,(map (lambda (d)
		  (if (symbol? (second d))
		      `(,(second d) ,(third d))
		      `(,(first (second d))
			(lambda ,(rest (second d)) ,(third d)))))
		 ds)
    ,e)))

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol (format #f "G~s" gensym))))

(define (genname . names)
 ;; debugging
 (string->uninterned-symbol
  (reduce (lambda (s1 s2) (string-append s1 "-" s2))
	  (map symbol->string names)
	  "")))

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

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
       ((symbol? p) e)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3)
	   (panic (format #f "Invalid parameter: ~s" p)))
	  (let ((x (gensym)))
	   `(lambda (,x)
	     ;; needs work: to ensure that you don't shadow car and cdr
	     (let* ((,(second p) (car ,x)) (,(third p) (cdr ,x)))
	      ,(third e)))))
	 ((cons*)
	  (case (length (rest p))
	   ((0) `(lambda (,(gensym)) ,(third e)))
	   ((1) `(lambda (,(second p)) ,(third e)))
	   (else `(lambda ((cons ,(second p) (cons* ,@(rest (rest p)))))
		   ,(third e)))))
	 ((list)
	  (if (null? (rest p))
	      `(lambda (,(gensym)) ,(third e))
	      `(lambda ((cons ,(second p) (list ,@(rest (rest p)))))
		,(third e))))
	 (else (panic (format #f "Invalid parameter: ~s" p)))))
       (else (panic (format #f "Invalid parameter: ~s" p))))))
    (else `(lambda ((cons* ,@(second e))) ,(third e)))))
  ((letrec)
   (unless (and (= (length e) 3)
		(list? (second e))
		(every
		 (lambda (b)
		  (and (list? b) (= (length b) 2) (symbol? (first b))))
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
  ;; needs work: to ensure that you don't shadow if-procedure
  ((if)
   (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
   `((((if-procedure ,(second e)) (lambda () ,(third e)))
      (lambda () ,(fourth e)))))
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
 (let loop ((e e) (xs *basis-constants*))
  (cond
   ((null? e) (panic (format #f "Invalid expression: ~s" e)))
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((symbol? e)
    (unless (memq e xs) (panic (format #f "Unbound variable: ~s" e)))
    #f)
   ((list? e)
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (panic (format #f "Invalid expression: ~s" e)))
	      #f)
     ((key)
      (unless (and (= (length e) 2) (symbol? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (unless (memq (second e) xs)
       (panic (format #f "Unbound variable: ~s" e)))
      #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (cond ((symbol? (first (second e)))
		   (when (memq p '(quote
				   key
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
				   or))
		    (panic (format #f "Invalid variable: ~s" p)))
		   ;; We no longer check for duplicate variables.
		   (loop (third e) (cons (first (second e)) xs)))
		  (else (loop (macro-expand e) xs))))
       (else (loop (macro-expand e) xs))))
     ((letrec) (loop (macro-expand e) xs))
     ((let) (loop (macro-expand e) xs))
     ((let*) (loop (macro-expand e) xs))
     ((if) (loop (macro-expand e) xs))
     ((cons) (loop (macro-expand e) xs))
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

(define (let? e)
 (and (application? e) (lambda-expression? (application-callee e))))

(define (let*-variables e)
 (if (let? e)
     (cons (lambda-expression-variable (application-callee e))
	   (let*-variables (lambda-expression-body (application-callee e))))
     '()))

(define (let*-expressions e)
 (if (let? e)
     (cons (application-argument e)
	   (let*-expressions (lambda-expression-body (application-callee e))))
     '()))

(define (let*-body e)
 (if (let? e) (let*-body (lambda-expression-body (application-callee e))) e))

(define (abstract->concrete e)
 (cond ((let? e)
	`(let* ,(map (lambda (x e) `(,x ,(abstract->concrete e)))
		     (let*-variables e)
		     (let*-expressions e))
	  ,(abstract->concrete (let*-body e))))
       ((variable-access-expression? e)
	(let* ((x (variable-access-expression-variable e))
	       (x (if (primitive-procedure? x)
		      (primitive-procedure-name x)
		      x)))
	 (if *show-access-indices?*
	     `(access ,x ,(variable-access-expression-index e))
	     x)))
       ((key-expression? e)
	(let* ((x (key-expression-variable e))
	       (x (if (primitive-procedure? x)
		      (primitive-procedure-name x)
		      x)))
	 (if *show-access-indices?*
	     `(key (access ,x ,(key-expression-index e)))
	     `(key ,x))))
       ((application? e)
	`(,(abstract->concrete (application-callee e))
	  ,(abstract->concrete (application-argument e))))
       ((lambda-expression? e)
	`(lambda (,(lambda-expression-variable e))
	  ,(abstract->concrete (lambda-expression-body e))))
       (else (fuck-up))))

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
	  (every-vector same? (closure-values v1) (closure-values v2)))))

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
  (list (let loop ((e (first result)))
	 (cond ((variable-access-expression? e)
		(make-variable-access-expression
		 (rename (variable-access-expression-variable e)) #f))
	       ((key-expression? e)
		(make-key-expression (rename (key-expression-variable e)) #f))
	       ((application? e)
		(make-application (loop (application-callee e))
				  (loop (application-argument e))))
	       ((lambda-expression? e)
		(new-lambda-expression (lambda-expression-variable e)
				       (loop (lambda-expression-body e))))
	       (else (fuck-up))))
	(map first bss))))

(define (unionq-vector xs1 xs2)
 (list->vector (unionq (vector->list xs1) (vector->list xs2))))

(define (removeq-vector x xs) (list->vector (removeq x (vector->list xs))))

;;; needs work: to make more efficient
(define (positionq-vector x xs) (positionq x (vector->list xs)))

(define (set-differenceq-vector xs1 xs2)
 (list->vector (set-differenceq (vector->list xs1) (vector->list xs2))))

(define (free-variables e)
 (cond ((variable-access-expression? e)
	(vector (variable-access-expression-variable e)))
       ((key-expression? e) (vector (key-expression-variable e)))
       ((application? e)
	(unionq-vector (free-variables (application-callee e))
		       (free-variables (application-argument e))))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       (else (fuck-up))))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (eq? x-prime x) (memq x-prime (vector->list xs))) (fuck-up))
  (if (eq? x-prime x) -1 (positionq-vector x-prime xs)))
 (cond ((variable-access-expression? e)
	(make-variable-access-expression
	 (variable-access-expression-variable e)
	 (lookup (variable-access-expression-variable e))))
       ((key-expression? e)
	(make-key-expression
	 (key-expression-variable e) (lookup (key-expression-variable e))))
       ((application? e)
	(make-application (index x xs (application-callee e))
			  (index x xs (application-argument e))))
       ((lambda-expression? e)
	(make-lambda-expression (free-variables e)
				(map-vector lookup (free-variables e))
				(lambda-expression-variable e)
				(index (lambda-expression-variable e)
				       (free-variables e)
				       (lambda-expression-body e))))
       (else (fuck-up))))

(define (concrete->abstract-expression e)
 (let* ((result
	 (let loop ((e e) (bs *variable-bindings*))
	  (cond
	   ((boolean? e) (loop `',e bs))
	   ((real? e) (loop `',e bs))
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
	     ((key)
	      (let loop ((e (variable-binding-expression
			     (find-if
			      (lambda (b)
			       (eq? (variable-binding-variable b) (second e)))
			      bs))))
	       (if (application? e)
		   (loop (application-argument e))
		   (list (make-key-expression
			  (variable-access-expression-variable e) #f)
			 '()))))
	     ((lambda)
	      (case (length (second e))
	       ((0) (loop (macro-expand e) bs))
	       ((1)
		(cond
		 ((symbol? (first (second e)))
		  (let* ((x (first (second e)))
			 (result
			  (loop (third e)
				(cons (make-variable-binding
				       x
				       (make-variable-access-expression x #f))
				      bs))))
		   (list (new-lambda-expression x (first result))
			 (second result))))
		 (else (loop (macro-expand e) bs))))
	       (else (loop (macro-expand e) bs))))
	     ((letrec) (loop (macro-expand e) bs))
	     ((let) (loop (macro-expand e) bs))
	     ((let*) (loop (macro-expand e) bs))
	     ((if) (loop (macro-expand e) bs))
	     ((cons) (loop (macro-expand e) bs))
	     ((cons*) (loop (macro-expand e) bs))
	     ((list) (loop (macro-expand e) bs))
	     ((cond) (loop (macro-expand e) bs))
	     ((and) (loop (macro-expand e) bs))
	     ((or) (loop (macro-expand e) bs))
	     (else
	      (case (length (rest e))
	       ((0) (loop (macro-expand e) bs))
	       ((1) (let ((result1 (loop (first e) bs))
			  (result2 (loop (second e) bs)))
		     (list (make-application (first result1) (first result2))
			   (append (second result1) (second result2)))))
	       (else (loop (macro-expand e) bs))))))
	   (else (fuck-up)))))
	(e (first result))
	(xs (vector->list (free-variables e)))
	(bs (remove-if-not (lambda (b) (memq (value-binding-variable b) xs))
			   (append *value-bindings* (second result))))
	(result (coalesce-constants (list e bs)))
	(e (first result))
	(xs (list->vector (map value-binding-variable (second result)))))
  (list (index #f xs e)
	(list->vector (map value-binding-value (second result))))))

;;; J* and *J

(define (basis-value x)
 (value-binding-value
  (find-if (lambda (b) (eq? (value-binding-variable b) x)) *value-bindings*)))

(define (make-constant bs v)
 (make-variable-access-expression
  (value-binding-variable
   (find-if (lambda (b) (eq? (value-binding-value b) v)) bs))
  #f))

(define (make-cons* bs es)
 (cond ((null? es) (make-constant bs '()))
       ((null? (rest es)) (first es))
       (else (make-cons bs (first es) (make-cons* bs (rest es))))))

(define (make-car bs e)
 (create-application bs (make-constant bs (basis-value 'car)) e))

(define (make-cdr bs e)
 (create-application bs (make-constant bs (basis-value 'cdr)) e))

(define (make-cons bs e1 e2)
 (create-application
  bs
  (create-application bs (make-constant bs (basis-value 'cons-procedure)) e1)
  e2))

(define (make-zero bs e)
 (create-application bs (make-constant bs (basis-value 'zero)) e))

(define (make-add bs e1 e2 e3)
 (create-application bs (make-constant bs (basis-value 'add)) e1 e2 e3))

(define (make-accumulate bs e1 e2 e3)
 (create-application bs (make-constant bs (basis-value 'accumulate)) e1 e2 e3))

(define (make-exit bs e1 e2)
 (create-application bs (make-constant bs (basis-value 'exit)) e1 e2))

(define (forward-transform bs e xs x-acutes)
 (cond
  ((variable-access-expression? e)
   (let ((x (variable-access-expression-variable e)))
    (if (memq x xs)
	(make-cons bs
		   e
		   (make-variable-access-expression
		    (list-ref x-acutes (positionq x xs))
		    #f))
	(make-cons bs e (make-zero bs e)))))
  ((key-expression? e) (make-cons bs e (make-zero bs e)))
  ((application? e)
   (create-application
    bs
    (make-car bs (forward-transform bs (application-callee e) xs x-acutes))
    (forward-transform bs (application-argument e) xs x-acutes)))
  ((lambda-expression? e)
   (let ((x (lambda-expression-variable e)) (x-acute (gensym)))
    (make-cons
     bs
     (create-lambda-expression
      bs
      `(,x ,x-acute)
      (forward-transform
       bs (lambda-expression-body e) (cons x xs) (cons x-acute x-acutes)))
     (make-constant bs '()))))
  (else (fuck-up))))

(define (wrap-partial-internal
	 bs
	 ;; This is an individual variable for the input.
	 x x-tilde x-grave
	 ;; This is a list of internal freely-referenced variables. This is
	 ;; the same both before and after the transformation since the
	 ;; transformation can only introduce external freely-referenced
	 ;; variables.
	 xs x-tildes x-graves
	 ;; This is a list of freely-referenced variables.
	 zs z-graves
	 e)
 ;; This is an individual variable for the composite backpropagator for the
 ;; freely-referenced variables.
 (let ((z-tilde (genname x 'z-tilde)))
  (create-lambda-expression
   bs
   `(,z-tilde ,x ,x-tilde)
   (create-let
    bs
    `(cons ,*y* ,*y-tilde*)
    ;; This could be a let.
    (create-let*
     bs
     `(,x-tilde ,@x-tildes)
     (cons
      (create-lambda-expression
       bs
       `(,x-grave ,*r*)
       (make-accumulate bs
			(make-key-expression x #f)
			(make-variable-access-expression *r* #f)
			(make-variable-access-expression x-grave #f)))
      (map (lambda (x-tilde x-grave)
	    (create-lambda-expression
	     bs
	     `(,x-grave ,*r*)
	     (make-accumulate bs
			      (make-key-expression x-tilde #f)
			      (make-variable-access-expression *r* #f)
			      (make-variable-access-expression x-grave #f))))
	   x-tildes
	   x-graves))
     e)
    (make-cons
     bs
     (make-variable-access-expression *y* #f)
     (create-lambda-expression
      bs
      `(,*y-grave* ,*r*)
      (create-let*
       bs
       (cons
	*r* (map (lambda (x-grave) `(cons ,x-grave ,*r*)) (reverse x-graves)))
       (cons
	(create-application
	 bs
	 (make-variable-access-expression x-tilde #f)
	 (make-exit
	  bs
	  (make-key-expression x #f)
	  (create-application
	   bs
	   (make-variable-access-expression *y-tilde* #f)
	   (make-variable-access-expression *y-grave* #f)
	   (make-add
	    bs
	    (make-key-expression x #f)
	    (let loop ((x-tildes (reverse x-tildes)) (xs (reverse xs)))
	     (if (null? x-tildes)
		 (make-variable-access-expression *r* #f)
		 (make-add bs
			   (make-key-expression (first x-tildes) #f)
			   (loop (rest x-tildes) (rest xs))
			   (make-variable-access-expression (first xs) #f))))
	    (make-variable-access-expression x #f)))))
	(map (lambda (x-tilde)
	      (make-exit bs
			 (make-key-expression x-tilde #f)
			 (make-variable-access-expression *r* #f)))
	     (reverse x-tildes)))
       (create-application
	bs
	(make-variable-access-expression z-tilde #f)
	(make-cons*
	 bs
	 (map (lambda (z z-grave)
	       (if (memq z-grave x-graves)
		   (make-variable-access-expression z-grave #f)
		   (make-zero bs (make-variable-access-expression z #f))))
	      zs
	      z-graves))
	(make-variable-access-expression *r* #f)))))))))

(define (wrap-full-internal
	 bs
	 ;; This is an individual variable for the input.
	 x x-tilde x-grave
	 ;; This is a list of internal freely-referenced variables. This is
	 ;; the same both before and after the transformation since the
	 ;; transformation can only introduce external freely-referenced
	 ;; variables.
	 xs x-tildes x-graves
	 ;; This is a list of freely-referenced variables.
	 zs z-graves
	 e)
 (make-cons bs
	    (wrap-partial-internal
	     bs x x-tilde x-grave xs x-tildes x-graves zs z-graves e)
	    (create-lambda-expression
	     bs
	     `((cons* ,@z-graves) ,*r*)
	     (let loop ((x-tildes x-tildes) (x-graves x-graves))
	      (cond ((null? x-tildes) (make-variable-access-expression *r* #f))
		    ((memq (first x-graves) z-graves)
		     (create-application
		      bs
		      (make-variable-access-expression (first x-tildes) #f)
		      (make-variable-access-expression (first x-graves) #f)
		      (loop (rest x-tildes) (rest x-graves))))
		    ;; This can only happen in the transient case before zs
		    ;; converges.
		    (else (loop (rest x-tildes) (rest x-graves))))))))

(define (wrap-partial
	 bs
	 ;; This is an individual variable for the input.
	 x x-tilde x-grave
	 ;; This is a list of internal freely-referenced variables. This is
	 ;; the same both before and after the transformation since the
	 ;; transformation can only introduce external freely-referenced
	 ;; variables.
	 xs x-tildes x-graves
	 e)
 (let loop ((zs '()) (z-graves '()))
  (let* ((e0 (wrap-partial-internal
	      bs x x-tilde x-grave xs x-tildes x-graves zs z-graves e))
	 (zs0 (vector->list (free-variables e0))))
   (if (equal? zs zs0)
       e0
       (loop zs0
	     (map (lambda (z)
		   (if (memq z xs)
		       (list-ref x-graves (positionq z xs))
		       (genname z 'z-grave)))
		  zs0))))))

(define (wrap-full
	 bs
	 ;; This is an individual variable for the input.
	 x x-tilde x-grave
	 ;; This is a list of internal freely-referenced variables. This is
	 ;; the same both before and after the transformation since the
	 ;; transformation can only introduce external freely-referenced
	 ;; variables.
	 xs x-tildes x-graves
	 e)
 (let loop ((zs '()) (z-graves '()))
  (let* ((e0 (wrap-partial-internal
	      bs x x-tilde x-grave xs x-tildes x-graves zs z-graves e))
	 (zs0 (vector->list (free-variables e0))))
   (if (equal? zs zs0)
       (wrap-full-internal
	bs x x-tilde x-grave xs x-tildes x-graves zs z-graves e)
       (loop zs0
	     (map (lambda (z)
		   (if (memq z xs)
		       (list-ref x-graves (positionq z xs))
		       (genname z 'z-grave)))
		  zs0))))))

(define (reverse-transform bs e xs x-tildes x-graves)
 ;; xs, x-tildes, and x-graves are the internal freely-referencable variables.
 (cond
  ((variable-access-expression? e)
   (let ((x (variable-access-expression-variable e)))
    (if (memq x xs)
	(make-cons bs
		   e
		   (make-variable-access-expression
		    (list-ref x-tildes (positionq x xs))
		    #f))
	(make-cons bs e (make-constant bs (basis-value 'cdr))))))
  ((key-expression? e) (make-cons bs e (make-constant bs (basis-value 'cdr))))
  ((application? e)
   ;; This could be a let.
   (create-let*
    bs
    `((cons ,*x1* ,*x1-tilde*) (cons ,*x2* ,*x2-tilde*))
    (list (reverse-transform bs (application-callee e) xs x-tildes x-graves)
	  (reverse-transform bs (application-argument e) xs x-tildes x-graves))
    (create-application bs
			(make-variable-access-expression *x1* #f)
			(make-variable-access-expression *x1-tilde* #f)
			(make-variable-access-expression *x2* #f)
			(make-variable-access-expression *x2-tilde* #f))))
  ((lambda-expression? e)
   ;; There is an asymmetry. If f returns (an object containing) a procedure
   ;; then (j* f) returns (an object containing) a transformed procedure that
   ;; can be called on a forward conjoint value. But (*j f) returns (an object
   ;; containing) a transformed procedure that is called on a pair of a
   ;; backpropagator cascade for the closed-over values and a reverse conjoint
   ;; value.
   (let* ((x (lambda-expression-variable e))
	  (x-tilde (genname x 'tilde))
	  (x-grave (genname x 'grave))
	  (zs (vector->list (free-variables e)))
	  (x-x-tilde-x-graves (remove-if-not
			       (lambda (x-x-tilde-x-grave)
				(memq (first x-x-tilde-x-grave) zs))
			       (map list xs x-tildes x-graves))))
    (wrap-full
     bs
     x
     x-tilde
     x-grave
     ;; We only shadow the backpropagators for internal freely-referenced
     ;; variables.
     (map first x-x-tilde-x-graves)
     (map second x-x-tilde-x-graves)
     (map third x-x-tilde-x-graves)
     (reverse-transform bs
			(lambda-expression-body e)
			(cons x xs)
			(cons x-tilde x-tildes)
			(cons x-grave x-graves)))))
  (else (fuck-up))))

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
       (else (fuck-up))))

(define (externalize v)
 (cond ((null? v) v)
       ((boolean? v) v)
       ((key? v) `(key ,(key-key v)))
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
	     (else (fuck-up)))
  (if *trace-argument/result?*
      (format #t "~aentering ~s ~s~%"
	      (make-string *trace-level* #\space)
	      (name callee)
	      (externalize argument))
      (format #t "~aentering ~s~%"
	      (make-string *trace-level* #\space)
	      (name callee)))
  (set! *trace-level* (+ *trace-level* 1)))
 (when (and *metered?* (primitive-procedure? callee))
  (set-primitive-procedure-meter!
   callee (+ (primitive-procedure-meter callee) 1)))
 (let ((result (cond ((primitive-procedure? callee)
		      ((primitive-procedure-procedure callee) argument))
		     ((closure? callee)
		      (evaluate (closure-body callee)
				argument
				(create-key)
				(closure-values callee)
				(closure-keys callee)))
		     (else (fuck-up)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((closure? callee) *trace-closures?*)
	      (else (fuck-up)))
   (set! *trace-level* (- *trace-level* 1))
   (if *trace-argument/result?*
       (format #t "~aexiting ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee)
	       (externalize result))
       (format #t "~aexiting ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee))))
  result))

(define (evaluate e v n vs ns)
 (define (lookup-value i) (if (= i -1) v (vector-ref vs i)))
 (define (lookup-key i) (if (= i -1) n (vector-ref ns i)))
 (cond ((variable-access-expression? e)
	(lookup-value (variable-access-expression-index e)))
       ((key-expression? e) (lookup-key (key-expression-index e)))
       ((application? e)
	;; This LET* is to specify the evaluation order.
	(let* ((callee (evaluate (application-callee e) v n vs ns))
	       (argument (evaluate (application-argument e) v n vs ns)))
	 (call callee argument)))
       ((lambda-expression? e)
	(make-closure
	 (free-variables e)
	 (map-vector lookup-value (lambda-expression-free-variable-indices e))
	 (map-vector lookup-key (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
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

(define (vlad-procedure? v) (or (primitive-procedure? v) (closure? v)))

(define (consify xs)
 (cond ((null? xs) '())
       ((null? (rest xs)) (first xs))
       (else (cons (first xs) (consify (rest xs))))))

(define (zero x)
 (cond ((null? x) '())
       ((boolean? x) '())
       ((key? x) '())
       ((real? x) 0)
       ((pair? x) (cons (zero (car x)) (zero (cdr x))))
       ((primitive-procedure? x) '())
       ((closure? x) (consify (map zero (vector->list (closure-values x)))))
       (else '())))

(define (conform? x1 x2)
 (or (and (null? x1) (null? x2))
     (and (real? x1) (real? x2))
     (and (pair? x1)
	  (pair? x2)
	  (conform? (car x1) (car x2))
	  (conform? (cdr x1) (cdr x2)))))

(define (plus x1 x2)
 (cond ((null? x1) '())
       ((real? x1) (+ x1 x2))
       (else (cons (plus (car x1) (car x2)) (plus (cdr x1) (cdr x2))))))

(define (key=? n1 n2) (= (key-key n1) (key-key n2)))

(define (store? x)
 (or (null? x)
     (and (pair? x) (pair? (car x)) (key? (car (car x))) (store? (cdr x)))))

(define (contains? n r)
 (and (not (null? r)) (or (key=? (car (car r)) n) (contains? n (cdr r)))))

(define (add n r x) (cons (cons n (zero x)) r))

(define (accumulate n r x)
 (if (key=? (car (car r)) n)
     (cons (cons n (plus x (cdr (car r)))) (cdr r))
     (cons (car r) (accumulate n (cdr r) x))))

(define (lookup n r)
 (if (key=? (car (car r)) n) (cdr (car r)) (lookup n (cdr r))))

(define (delete1 n r)
 (if (key=? (car (car r)) n) (cdr r) (cons (car r) (delete1 n (cdr r)))))

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
 (define-primitive-procedure 'key? key?)
 (define-primitive-procedure 'real? real?)
 (define-primitive-procedure 'pair? pair?)
 (define-primitive-procedure 'procedure? vlad-procedure?)
 (define-primitive-procedure 'car (binary (lambda (x1 x2) x1) "car"))
 (define-primitive-procedure 'cdr (binary (lambda (x1 x2) x2) "cdr"))
 (define-primitive-procedure 'cons-procedure
  ;; Note that we can't apply a j operator to the result of (cons-procedure e)
  ;; or compare results of (cons-procedure e) with the old equal?.
  (lambda (x1)
   (create-primitive-procedure "cons-procedure" (lambda (x2) (cons x1 x2)))))
 (define-primitive-procedure 'if-procedure
  ;; Note that we can't apply a j operator to the result of (if-procedure e1)
  ;; or ((if-procedure e1) e2) or compare results of (if-procedure e1) or
  ;; ((if-procedure e1) e2) with the old equal?.
  (lambda (x1)
   (create-primitive-procedure
    "if-procedure 0"
    (lambda (x2)
     (create-primitive-procedure
      "if-procedure 1" (lambda (x3) (if x1 x2 x3)))))))
 (define-primitive-procedure 'eq?
  (lambda (x)
   (unless (pair? x) (run-time-error "Invalid argument to eq?" x))
   (eq? (car x) (cdr x))))
 (define-primitive-procedure 'key=?
  (lambda (x)
   (unless (and (pair? x) (key? (car x)) (key? (cdr x)))
    (run-time-error "Invalid argument to key=?" x))
   (key=? (car x) (cdr x))))
 (define-primitive-procedure 'zero zero)
 (define-primitive-procedure 'add
  ;; (add key rho x) ==> rho[key|->(zero x)]
  (lambda (x)
   (unless (and (pair? x)
		(pair? (cdr x))
		(key? (car x))
		(store? (car (cdr x)))
		(not (contains? (car x) (car (cdr x)))))
    (run-time-error "Invalid argument to add" x))
   (add (car x) (car (cdr x)) (cdr (cdr x)))))
 (define-primitive-procedure 'accumulate
  ;; (accumulate key rho x-grave) ==> rho[key|->rho(key) o+ x-grave]
  (lambda (x)
   (unless (and (pair? x)
		(pair? (cdr x))
		(key? (car x))
		(store? (car (cdr x)))
		(contains? (car x) (car (cdr x)))
		(conform? (lookup (car x) (car (cdr x))) (cdr (cdr x))))
    ;; debugging
    (when (and (pair? x) (pair? (cdr x)) (key? (car x)) (store? (car (cdr x))))
     (write (lookup (car x) (car (cdr x))))
     (newline)
     (write (cdr (cdr x)))
     (newline)
     (run-time-error "Nonconforming arguments to accumulate" x))
    (run-time-error "Invalid argument to accumulate" x))
   (accumulate (car x) (car (cdr x)) (cdr (cdr x)))))
 ;; (exit key rho) => (cons (lookup key rho) (delete key rho))
 (define-primitive-procedure 'exit
  (lambda (x)
   (unless (and (pair? x)
		(key? (car x))
		(store? (cdr x))
		(contains? (car x) (cdr x)))
    (run-time-error "Invalid argument to exit" x))
   (cons (lookup (car x) (cdr x)) (delete1 (car x) (cdr x)))))
 (define-primitive-procedure 'map-closure-forward
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-forward" x))
   (let ((f (car x)) (g (cdr x)))
    (unless (closure? g)
     (run-time-error "Invalid argument to map-closure-forward" x))
    (let* ((x (closure-variable g))
	   (x-acute (gensym))
	   (bs (map (lambda (v) (make-value-binding (gensym) v))
		    (cons '() (map value-binding-value *value-bindings*))))
	   (e (create-lambda-expression
	       bs
	       `(,x ,x-acute)
	       (forward-transform
		bs (closure-body g) (list x) (list x-acute))))
	   (x (lambda-expression-variable e))
	   (e (lambda-expression-body e))
	   (xs (removeq-vector x (free-variables e))))
     (make-closure
      xs
      (map-vector
       (lambda (x)
	(let ((i (positionq-vector x (closure-variables g))))
	 (if i
	     (call f (vector-ref (closure-values g) i))
	     (value-binding-value
	      (find-if (lambda (b) (eq? (value-binding-variable b) x)) bs)))))
       xs)
      (map-vector (lambda (x)
		   (let ((i (positionq-vector x (closure-variables g))))
		    (if i (vector-ref (closure-keys g) i) (create-key))))
		  xs)
      x
      (index x xs e))))))
 (define-primitive-procedure 'map-closure-reverse
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-reverse" x))
   (let ((f (car x)) (g (cdr x)))
    (unless (closure? g)
     (run-time-error "Invalid argument to map-closure-reverse" x))
    (let* ((x (closure-variable g))
	   (x-tilde (genname x 'tilde))
	   (x-grave (genname x 'grave))
	   (bs (map (lambda (v) (make-value-binding (gensym) v))
		    (cons '() (map value-binding-value *value-bindings*))))
	   (e (wrap-partial
	       bs
	       x
	       x-tilde
	       x-grave
	       '()
	       '()
	       '()
	       (reverse-transform
		bs (closure-body g) (list x) (list x-tilde) (list x-grave))))
	   (x (lambda-expression-variable e))
	   (e (lambda-expression-body e))
	   (xs (removeq-vector x (free-variables e))))
     (make-closure
      xs
      (map-vector
       (lambda (x)
	(let ((i (positionq-vector x (closure-variables g))))
	 (if i
	     (call f (vector-ref (closure-values g) i))
	     (value-binding-value
	      (find-if (lambda (b) (eq? (value-binding-variable b) x)) bs)))))
       xs)
      (map-vector (lambda (x)
		   (let ((i (positionq-vector x (closure-variables g))))
		    (if i (vector-ref (closure-keys g) i) (create-key))))
		  xs)
      x
      (index x xs e))))))
 (define-primitive-procedure 'write
  (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
