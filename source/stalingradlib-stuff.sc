(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
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
;;;  4. enforce don't shadow: car, cdr, cons-procedure, if-procedure, and ys

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

(define-structure variable-access-expression variable index)

(define-structure lambda-expression
 free-variables
 free-variable-indices			;vector
 variable
 body)

(define-structure application callee argument)

(define-structure letrec-expression
 used-binding-maps			;vector vector
 procedure-variables
 argument-variables
 bodies-free-variables
 bodies-free-variable-indices		;vector
 body-free-variables
 body-free-variable-indices		;vector
 bodies
 body)

(define-structure variable-binding variable expression)

(define-structure value-binding variable value)

(define-structure anf variable letrec-bindings let-bindings)

(define-structure closure
 variables
 values					;vector
 variable
 body)

(define-structure recursive-closure
 variables
 values					;vector
 used-binding-maps			;vector vector
 procedure-variables			;vector
 argument-variables			;vector
 bodies					;vector
 index)

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

(define *letrec?* #f)

;;; Procedures

(define (sort-variables xs) (sort xs string<? symbol->string))

(define (new-lambda-expression x e)
 (make-lambda-expression (removeq x (free-variables e)) #f x e))

(define (new-letrec-expression procedure-variables argument-variables es e)
 (let* ((body-used-procedure-variables
	 (letrec-body-used-procedure-variables
	  procedure-variables argument-variables es e))
	(triples
	 (remove-if-not
	  (lambda (triple) (memq (first triple) body-used-procedure-variables))
	  (map list procedure-variables argument-variables es)))
	(procedure-variables (map first triples))
	(argument-variables (map second triples))
	(es (map third triples))
	(bodies-used-procedure-variables
	 (letrec-bodies-used-procedure-variables
	  procedure-variables argument-variables es)))
  (make-letrec-expression
   (list->vector
    (map (lambda (body-used-procedure-variables)
	  (list->vector
	   (removeq
	    #f
	    (map-indexed
	     (lambda (x i) (if (memq x body-used-procedure-variables) i #f))
	     procedure-variables))))
	 bodies-used-procedure-variables))
   procedure-variables
   argument-variables
   (letrec-free-variables procedure-variables argument-variables es)
   #f
   (sort-variables
    (set-differenceq
     (unionq (reduce unionq
		     (map (lambda (x e) (removeq x (free-variables e)))
			  argument-variables
			  es)
		     '())
	     (free-variables e))
     procedure-variables))
   #f
   es
   e)))

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
 (let ((e `(letrec ,(map (lambda (d)
			  (if (symbol? (second d))
			      `(,(second d) ,(third d))
			      `(,(first (second d))
				(lambda ,(rest (second d)) ,(third d)))))
			 ds)
	    ,e)))
  (if *letrec?* e (standard-prelude e))))

(define (duplicatesq? xs)
 (and (not (null? xs))
      (or (memq (first xs) (rest xs)) (duplicatesq? (rest xs)))))

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
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (cond ((symbol? (first (second e)))
		   (when (memq p '(quote
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
     ((letrec)
      (cond (*letrec?*
	     (unless (and (= (length e) 3)
			  (list? (second e))
			  (every (lambda (b)
				  (and (list? b)
				       (= (length b) 2)
				       (symbol? (first b))))
				 (second e)))
	      (panic (format #f "Invalid expression: ~s" e)))
	     (let ((xs0 (map first (second e))))
	      (when (duplicatesq? xs0)
	       (panic (format #f "Duplicate variables: ~s" e)))
	      (for-each (lambda (b)
			 (let ((e1 (macro-expand (second b))))
			  (unless (and (list? e1)
				       (= (length e1) 3)
				       (eq? (first e1) 'lambda))
			   (panic (format #f "Invalid expression: ~s" e)))
			  (loop e1  (append xs0 xs))))
			(second e))
	      (loop (third e) (append xs0 xs))))
	    (else (loop (macro-expand e) xs))))
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
    (cond ((variable-access-expression? e)
	   (make-variable-access-expression
	    (rename (variable-access-expression-variable e)) #f))
	  ((lambda-expression? e)
	   (new-lambda-expression (lambda-expression-variable e)
				  (loop (lambda-expression-body e))))
	  ((application? e)
	   (make-application (loop (application-callee e))
			     (loop (application-argument e))))
	  ((letrec-expression? e)
	   (new-letrec-expression (letrec-expression-procedure-variables e)
				  (letrec-expression-argument-variables e)
				  (map loop (letrec-expression-bodies e))
				  (loop (letrec-expression-body e))))
	  (else (fuck-up))))
   (map first bss))))

(define (letrec-body-used-procedure-variables
	 procedure-variables argument-variables es e)
 (let loop ((xs (intersectionq procedure-variables (free-variables e))))
  (let ((xs-prime
	 (unionq
	  (intersectionq procedure-variables (free-variables e))
	  (reduce unionq
		  (map (lambda (x1 x2 e)
			(if (memq x1 xs)
			    (intersectionq procedure-variables
					   (removeq x2 (free-variables e)))
			    '()))
		       procedure-variables
		       argument-variables
		       es)
		  '()))))
   (if (set-equalq? xs xs-prime) xs (loop xs-prime)))))

(define (letrec-bodies-used-procedure-variables
	 procedure-variables argument-variables es)
 ;; needs work: The (list x1) makes each recursive closure contain its own
 ;;             binding. This is not necessary if a recursive closure can't
 ;;             call itself. But then it doesn't need to be a recursive
 ;;             closure and can be converted into a closure. We don't do that
 ;;             optimization (yet). Because the current implementation of
 ;;             recursive closures has no other way to have a body except in
 ;;             bodies, we must make such a self binding even if the recursive
 ;;             closure can't call itself.
 (map
  (lambda (x1 x2 e)
   (let loop ((xs (unionq (list x1)
			  (intersectionq procedure-variables
					 (removeq x2 (free-variables e))))))
    (let ((xs-prime
	   (unionq
	    (unionq (list x1)
		    (intersectionq procedure-variables
				   (removeq x2 (free-variables e))))
	    (reduce unionq
		    (map (lambda (x1 x2 e)
			  (if (memq x1 xs)
			      (intersectionq procedure-variables
					     (removeq x2 (free-variables e)))
			      '()))
			 procedure-variables
			 argument-variables
			 es)
		    '()))))
     (if (set-equalq? xs xs-prime) xs (loop xs-prime)))))
  procedure-variables
  argument-variables
  es))

(define (letrec-free-variables procedure-variables argument-variables es)
 (sort-variables
  (set-differenceq
   (reduce
    unionq
    (map (lambda (x e) (removeq x (free-variables e))) argument-variables es)
    '())
   procedure-variables)))

(define (free-variables e)
 (define (free-variables e)
  (cond ((variable-access-expression? e)
	 (list (variable-access-expression-variable e)))
	((lambda-expression? e) (lambda-expression-free-variables e))
	((application? e)
	 (unionq (free-variables (application-callee e))
		 (free-variables (application-argument e))))
	((letrec-expression? e) (letrec-expression-body-free-variables e))
	(else (fuck-up))))
 (sort-variables (free-variables e)))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (eq? x-prime x) (memq x-prime xs)) (fuck-up))
  (if (eq? x-prime x) -1 (positionq x-prime xs)))
 (cond
  ((variable-access-expression? e)
   (make-variable-access-expression
    (variable-access-expression-variable e)
    (lookup (variable-access-expression-variable e))))
  ((lambda-expression? e)
   (make-lambda-expression (free-variables e)
			   (list->vector (map lookup (free-variables e)))
			   (lambda-expression-variable e)
			   (index (lambda-expression-variable e)
				  (free-variables e)
				  (lambda-expression-body e))))
  ((application? e)
   (make-application (index x xs (application-callee e))
		     (index x xs (application-argument e))))
  ((letrec-expression? e)
   (make-letrec-expression
    (letrec-expression-used-binding-maps e)
    (letrec-expression-procedure-variables e)
    (letrec-expression-argument-variables e)
    (letrec-expression-bodies-free-variables e)
    (list->vector (map lookup (letrec-expression-bodies-free-variables e)))
    (letrec-expression-body-free-variables e)
    (list->vector (map lookup (letrec-expression-body-free-variables e)))
    (let ((xs1 (list->vector (letrec-expression-procedure-variables e)))
	  (xs2 (letrec-expression-bodies-free-variables e)))
     (map
      (lambda (used-bindings x e)
       (index
	x
	(append (vector->list
		 (map-vector (lambda (i) (vector-ref xs1 i)) used-bindings))
		xs2)
	e))
      (vector->list (letrec-expression-used-binding-maps e))
      (letrec-expression-argument-variables e)
      (letrec-expression-bodies e)))
    (index x
	   (append (letrec-expression-procedure-variables e)
		   (letrec-expression-body-free-variables e))
	   (letrec-expression-body e))))
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
	     ((letrec)
	      (if *letrec?*
		  (let* ((bs
			  (append
			   (map
			    (lambda (b)
			     (make-variable-binding
			      (first b)
			      (make-variable-access-expression (first b) #f)))
			    (second e))
			   bs))
			 (results
			  (map (lambda (b) (loop (macro-expand (second b)) bs))
			       (second e)))
			 (result (loop (third e) bs))
			 (xs1 (map first (second e)))
			 (xs2
			  (map (lambda (result)
				(lambda-expression-variable (first result)))
			       results))
			 (es (map (lambda (result)
				   (lambda-expression-body (first result)))
				  results))
			 (e (first result)))
		   (list (new-letrec-expression xs1 xs2 es e)
			 (append (second result)
				 (reduce append (map second results) '()))))
		  (loop (macro-expand e) bs)))
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
	(xs (free-variables e))
	(bs (remove-if-not (lambda (b) (memq (value-binding-variable b) xs))
			   (append *value-bindings* (second result))))
	(result (coalesce-constants (list e bs)))
	(e (first result))
	(xs (map value-binding-variable (second result))))
  (list (index #f xs e) (map value-binding-value (second result)))))

;;; J* and *J

(define (clone-name x)
 ;; debugging
 (if #t
     (let ((gensym *gensym*))
      (set! *gensym* (+ *gensym* 1))
      (string->uninterned-symbol
       (string-append (symbol->string x) "-" (number->string *gensym*))))
     (string->uninterned-symbol (symbol->string x))))

(define (alpha-rename e)
 (let loop ((e e) (bs '()))
  (cond ((variable-access-expression? e)
	 (let ((b (find-if (lambda (b)
			    (eq? (variable-binding-variable b)
				 (variable-access-expression-variable e)))
			   bs)))
	  (if b (variable-binding-expression b) e)))
	((lambda-expression? e)
	 (let ((x (clone-name (lambda-expression-variable e))))
	  (new-lambda-expression
	   x
	   (loop (lambda-expression-body e)
		 (cons (make-variable-binding
			(lambda-expression-variable e)
			(make-variable-access-expression x #f))
		       bs)))))
	((application? e)
	 (make-application (loop (application-callee e) bs)
			   (loop (application-argument e) bs)))
	((letrec-expression? e)
	 (let ((xs1 (map clone-name (letrec-expression-procedure-variables e)))
	       (xs2 (map clone-name (letrec-expression-argument-variables e))))
	  (new-letrec-expression
	   xs1
	   xs2
	   (map
	    (lambda (e1 x x2)
	     (loop
	      e1
	      (cons (make-variable-binding
		     x (make-variable-access-expression x2 #f))
		    (append (map (lambda (x x1)
				  (make-variable-binding
				   x (make-variable-access-expression x1 #f)))
				 (letrec-expression-procedure-variables e)
				 xs1)
			    bs))))
	    (letrec-expression-bodies e)
	    (letrec-expression-argument-variables e)
	    xs2)
	   (loop
	    (letrec-expression-body e)
	    (append (map (lambda (x x1)
			  (make-variable-binding
			   x (make-variable-access-expression x1 #f)))
			 (letrec-expression-procedure-variables e)
			 xs1)
		    bs)))))
	(else (fuck-up)))))

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

(define (make-zero bs)
 (create-application bs (make-constant bs (basis-value 'zero))))

(define (make-plus bs e1 e2)
 (create-application bs (make-constant bs (basis-value 'plus)) e1 e2))

(define (anf bs e)
 (cond
  ((variable-access-expression? e)
   ;; needs work: can simplify
   (let ((x (gensym))) (make-anf x '() (list (make-variable-binding x e)))))
  ((lambda-expression? e)
   (let ((x (gensym)))
    (make-anf
     x '() (list (make-variable-binding x (reverse-transform bs e))))))
  ((application? e)
   (let* ((anf1 (anf bs (application-callee e)))
	  (anf2 (anf bs (application-argument e)))
	  (x (gensym)))
    (make-anf
     x
     (append (anf-letrec-bindings anf1) (anf-letrec-bindings anf2))
     (append
      (anf-let-bindings anf1)
      (anf-let-bindings anf2)
      (list (make-variable-binding
	     x
	     (make-application
	      (make-variable-access-expression (anf-variable anf1) #f)
	      (make-variable-access-expression (anf-variable anf2) #f))))))))
  ((letrec-expression? e)
   (let ((anf (anf bs (letrec-expression-body e))))
    (make-anf
     (anf-variable anf)
     (append (anf-letrec-bindings anf)
	     (map make-variable-binding
		  (letrec-expression-procedure-variables e)
		  (reverse-transforms
		   bs
		   (vector->list (letrec-expression-used-binding-maps e))
		   (letrec-expression-procedure-variables e)
		   (map new-lambda-expression
			(letrec-expression-argument-variables e)
			(letrec-expression-bodies e)))))
     (anf-let-bindings anf))))
  (else (fuck-up))))

(define (reverse-transform-internal
	 bs x x-grave y-grave anf t-twiddles t-graves fs f-graves xs)
 (let* ((ts (map variable-binding-variable (anf-let-bindings anf)))
	(es (map variable-binding-expression (anf-let-bindings anf)))
	(x-graves (map (lambda (x) (genname x 'grave)) xs))
	(ws
	 (letrec-free-variables
	  (map variable-binding-variable (anf-letrec-bindings anf))
	  (map (lambda (b)
		(lambda-expression-variable (variable-binding-expression b)))
	       (anf-letrec-bindings anf))
	  (map (lambda (b)
		(lambda-expression-body (variable-binding-expression b)))
	       (anf-letrec-bindings anf)))))
  (define (gravify z)
   (cond ((eq? z x) x-grave)
	 ((memq z xs) (list-ref x-graves (positionq z xs)))
	 ((memq z fs) (list-ref f-graves (positionq z fs)))
	 ((memq z ts) (list-ref t-graves (positionq z ts)))
	 ;; need before convergence to fixedpoint of free-variable
	 ;; calculation
	 (else z)))
  (let* ((bs0
	  (map
	   (lambda (t t-twiddle t-grave e)
	    (cond
	     ((variable-access-expression? e)
	      (let ((x-grave
		     (gravify (variable-access-expression-variable e))))
	       (make-variable-binding
		x-grave
		(make-plus bs
			   (make-variable-access-expression x-grave #f)
			   (make-variable-access-expression t-grave #f)))))
	     ((lambda-expression? e)
	      (let ((zs (free-variables e)))
	       (make-variable-binding
		`(cons* ,@(map gravify zs))
		(make-plus
		 bs
		 (make-cons*
		  bs
		  (map (lambda (z)
			(make-variable-access-expression (gravify z) #f))
		       zs))
		 (make-variable-access-expression t-grave #f)))))
	     ((application? e)
	      (make-variable-binding
	       `(cons ,(gravify (variable-access-expression-variable
				 (application-callee e)))
		      ,(gravify (variable-access-expression-variable
				 (application-argument e))))
	       (make-application
		(make-variable-access-expression t-twiddle #f)
		(make-variable-access-expression t-grave #f))))
	     (else (fuck-up))))
	   (reverse ts)
	   (reverse t-twiddles)
	   (reverse t-graves)
	   (reverse es)))
	 (e
	  (create-let*
	   bs
	   (map (lambda (t t-twiddle e)
		 (if (application? e) `(cons ,t ,t-twiddle) t))
		ts t-twiddles es)
	   es
	   (make-cons
	    bs
	    (make-variable-access-expression (anf-variable anf) #f)
	    (create-lambda-expression
	     bs
	     (list y-grave)
	     (create-let*
	      bs
	      `(,@x-graves
		,x-grave
		,@f-graves
		,(last t-graves)
		,@(map variable-binding-variable bs0)
		,@(if (null? (anf-letrec-bindings anf))
		      '()
		      (list `(cons* ,@(map gravify ws)))))
	      `(,@(map (lambda (x) (make-zero bs)) xs)
		,(make-zero bs)
		,@(map (lambda (f) (make-zero bs)) fs)
		,(make-variable-access-expression y-grave #f)
		,@(map variable-binding-expression bs0)
		,@(if (null? (anf-letrec-bindings anf))
		      '()
		      (list
		       (make-plus
			bs
			(make-cons*
			 bs
			 (map
			  (lambda (w)
			   (make-variable-access-expression (gravify w) #f))
			  ws))
			(let loop ((f-graves f-graves))
			 (if (null? (rest f-graves))
			     (make-variable-access-expression
			      (first f-graves) #f)
			     (make-plus bs
					(make-variable-access-expression
					 (first f-graves) #f)
					(loop (rest f-graves)))))))))
	      (make-cons bs
			 (make-cons*
			  bs
			  (map (lambda (x-grave)
				(make-variable-access-expression x-grave #f))
			       x-graves))
			 (make-variable-access-expression x-grave #f))))))))
   (create-lambda-expression
    bs
    (list x)
    (if (null? (anf-letrec-bindings anf))
	e
	(new-letrec-expression
	 (map variable-binding-variable (anf-letrec-bindings anf))
	 (map (lambda (b)
	       (lambda-expression-variable (variable-binding-expression b)))
	      (anf-letrec-bindings anf))
	 (map (lambda (b)
	       (lambda-expression-body (variable-binding-expression b)))
	      (anf-letrec-bindings anf))
	 e))))))

(define (reverse-transform bs e)
 (let* ((x (lambda-expression-variable e))
	(x-grave (genname x 'grave))
	(y-grave (genname x 'y-grave))
	(anf (anf bs (lambda-expression-body e)))
	(ts (map variable-binding-variable (anf-let-bindings anf)))
	(t-twiddles (map (lambda (t) (genname t 'twiddle)) ts))
	(t-graves (map (lambda (t) (genname t 'grave)) ts))
	(fs (map variable-binding-variable (anf-letrec-bindings anf)))
	(f-graves (map (lambda (f) (genname f 'grave)) fs)))
  (let loop ((xs (free-variables e)))
   (let* ((e (reverse-transform-internal
	      bs x x-grave y-grave anf t-twiddles t-graves fs f-graves xs))
	  (xs-prime (free-variables e)))
    (if (equal? xs xs-prime) e (loop xs-prime))))))

(define (reverse-transforms bs used-binding-maps gs es)
 (let* ((xs (map lambda-expression-variable es))
	(x-graves (map (lambda (x) (genname x 'grave)) xs))
	(y-graves (map (lambda (x) (genname x 'y-grave)) xs))
	(anfs (map (lambda (e) (anf bs (lambda-expression-body e))) es))
	(tss (map (lambda (anf)
		   (map variable-binding-variable (anf-let-bindings anf)))
		  anfs))
	(t-twiddless (map (lambda (ts)
			   (map (lambda (t) (genname t 'twiddle)) ts))
			  tss))
	(t-gravess (map (lambda (ts) (map (lambda (t) (genname t 'grave)) ts))
			tss))
	(fss (map (lambda (anf)
		   (map variable-binding-variable (anf-letrec-bindings anf)))
		  anfs))
	(f-gravess (map (lambda (fs) (map (lambda (f) (genname f 'grave)) fs))
			fss)))
  (let loop ((zs (letrec-free-variables gs xs es)))
   (let* ((es (map
	       (lambda (x x-grave y-grave anf t-twiddles t-graves fs f-graves
			  used-bindings)
		(reverse-transform-internal
		 bs x x-grave y-grave anf t-twiddles t-graves fs f-graves
		 (append (map (lambda (i) (list-ref gs i))
			      (vector->list used-bindings))
			 zs)))
	       xs x-graves y-graves anfs t-twiddless t-gravess fss f-gravess
	       used-binding-maps))
	  (zs-prime (letrec-free-variables gs xs es)))
    (if (equal? zs zs-prime) es (loop zs-prime))))))

;;; Evaluator

(define (generic-zero? v) (eq? v 'generic-zero))

(define (generic-zero-dereference-as-real v) (if (generic-zero? v) 0 v))

(define (generic-zero-dereference-as-pair v)
 (if (generic-zero? v) (cons 'generic-zero 'generic-zero) v))

(define (generic-zero-dereference v)
 (when (generic-zero? v)
  (run-time-error "Cannot apply this primitive to an unbound generic zero" v))
 v)

(define (name v)
 (cond
  ((primitive-procedure? v) (primitive-procedure-name v))
  ((closure? v)
   (if *unabbreviate-closures?*
       `(closure ,(map-indexed
		   (lambda (x i)
		    `(,x ,(externalize (vector-ref (closure-values v) i))))
		   (closure-variables v))
		 (lambda (,(closure-variable v))
		  ,(abstract->concrete (closure-body v))))
       `(lambda (,(closure-variable v))
	 ,(abstract->concrete (closure-body v)))))
  ((recursive-closure? v)
   ;; debugging
   (if *unabbreviate-recursive-closures?*
       (if #t
	   `(recursive-closure
	     ,(map-indexed
	       (lambda (x i)
		`(,x
		  ,(externalize (vector-ref (recursive-closure-values v) i))))
	       (recursive-closure-variables v))
	     ,(vector->list
	       (map-vector (lambda (x1 x2 e)
			    `(,x1 (lambda (,x2) ,(abstract->concrete e))))
			   (recursive-closure-procedure-variables v)
			   (recursive-closure-argument-variables v)
			   (recursive-closure-bodies v)))
	     ,(vector-ref (recursive-closure-procedure-variables v)
			  (recursive-closure-index v)))
	   `(recursive-closure
	     ,(map-indexed
	       (lambda (x i)
		`(,x
		  ,(externalize (vector-ref (recursive-closure-values v) i))))
	       (recursive-closure-variables v))
	     ,(vector-ref (recursive-closure-procedure-variables v)
			  (recursive-closure-index v))))
       (vector-ref (recursive-closure-procedure-variables v)
		   (recursive-closure-index v))))
  (else (fuck-up))))

(define (externalize v)
 (cond ((generic-zero? v) v)
       ((null? v) v)
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
	   (vector-append
	    ;; needs work: This is quartic in the number of bindings.
	    ;; needs work: Another optimization is possible. One can on a per
	    ;;             binding basis, filter the variables/values.
	    (map-n-vector
	     (lambda (i)
	      (let ((used-bindings
		     (vector-ref
		      (recursive-closure-used-binding-maps callee) i)))
	       (make-recursive-closure
		(recursive-closure-variables callee)
		(recursive-closure-values callee)
		(map-vector
		 (lambda (i)
		  (map-vector
		   (lambda (i) (positionq i (vector->list used-bindings)))
		   (vector-ref
		    (recursive-closure-used-binding-maps callee) i)))
		 used-bindings)
		(map-vector
		 (lambda (i)
		  (vector-ref
		   (recursive-closure-procedure-variables callee) i))
		 used-bindings)
		(map-vector
		 (lambda (i)
		  (vector-ref (recursive-closure-argument-variables callee) i))
		 used-bindings)
		(map-vector
		 (lambda (i) (vector-ref (recursive-closure-bodies callee) i))
		 used-bindings)
		(positionq i (vector->list used-bindings)))))
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
       (format #t "~aexiting ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee)
	       (externalize result))
       (format #t "~aexiting ~s~%"
	       (make-string *trace-level* #\space)
	       (name callee))))
  result))

(define (evaluate e v vs)
 (define (lookup-value i) (if (= i -1) v (vector-ref vs i)))
 (cond ((variable-access-expression? e)
	(lookup-value (variable-access-expression-index e)))
       ((lambda-expression? e)
	(make-closure
	 (free-variables e)
	 (map-vector lookup-value (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
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
		     lookup-value
		     (letrec-expression-bodies-free-variable-indices e)))
		(xs0 (list->vector (letrec-expression-procedure-variables e)))
		(xs1 (list->vector (letrec-expression-argument-variables e)))
		(es (list->vector (letrec-expression-bodies e))))
	   ;; needs work: This is quartic in the number of bindings.
	   ;; needs work: Another optimization is possible. One can on a per
	   ;;             binding basis, filter the variables/values.
	   (map-n-vector
	    (lambda (i)
	     (let ((used-bindings
		    (vector-ref (letrec-expression-used-binding-maps e) i)))
	      (make-recursive-closure
	       (letrec-expression-bodies-free-variables e)
	       vs
	       (map-vector
		(lambda (i)
		 (map-vector
		  (lambda (i) (positionq i (vector->list used-bindings)))
		  (vector-ref (letrec-expression-used-binding-maps e) i)))
		used-bindings)
	       (map-vector (lambda (i) (vector-ref xs0 i)) used-bindings)
	       (map-vector (lambda (i) (vector-ref xs1 i)) used-bindings)
	       (map-vector (lambda (i) (vector-ref es i)) used-bindings)
	       (positionq i (vector->list used-bindings)))))
	    (vector-length es)))
	  (map-vector lookup-value
		      (letrec-expression-body-free-variable-indices e)))))
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

(define (vlad-procedure? v)
 (or (primitive-procedure? v) (closure? v) (recursive-closure? v)))

(define (conform? x1 x2)
 (or (generic-zero? x1)
     (generic-zero? x2)
     (and (null? x1) (null? x2))
     (and (real? x1) (real? x2))
     (and (pair? x1)
	  (pair? x2)
	  (conform? (car x1) (car x2))
	  (conform? (cdr x1) (cdr x2)))))

(define (plus x1 x2)
 (define (plus x1 x2)
  (cond ((generic-zero? x1) x2)
	((generic-zero? x2) x1)
	((null? x1) '())
	((real? x1) (+ x1 x2))
	(else (cons (plus (car x1) (car x2)) (plus (cdr x1) (cdr x2))))))
 (unless (conform? x1 x2)
  ;; debugging
  (when #t
   (write (externalize x1))
   (newline)
   (write (externalize x2))
   (newline))
  (run-time-error "nonconformance" (cons x1 x2)))
 (plus x1 x2))

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
 (define-primitive-procedure 'null?
  (lambda (x) (null? (generic-zero-dereference x))))
 (define-primitive-procedure 'boolean? boolean?)
 (define-primitive-procedure 'real?
  (lambda (x) (real? (generic-zero-dereference x))))
 (define-primitive-procedure 'pair?
  (lambda (x) (or (generic-zero? x) (pair? (generic-zero-dereference x)))))
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
 (define-primitive-procedure 'zero (lambda (x) 'generic-zero))
 (define-primitive-procedure 'generic-zero? generic-zero?)
 (define-primitive-procedure 'plus (binary plus "plus"))
 (define-primitive-procedure 'map-closure-forward
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-forward" x))
   (let ((f (car x)) (g (cdr x)))
    (cond
     ((closure? g)
      (make-closure (closure-variables g)
		    (map-vector (lambda (v) (call f v)) (closure-values g))
		    (closure-variable g)
		    (closure-body g)))
     ((recursive-closure? g)
      (make-recursive-closure
       (recursive-closure-variables g)
       (map-vector (lambda (v) (call f v)) (recursive-closure-values g))
       (recursive-closure-used-binding-maps g)
       (recursive-closure-procedure-variables g)
       (recursive-closure-argument-variables g)
       (recursive-closure-bodies g)
       (recursive-closure-index g)))
     (else (run-time-error "Invalid argument to map-closure-forward" x))))))
 (define-primitive-procedure 'map-closure-reverse
  (lambda (x)
   (unless (and (pair? x) (vlad-procedure? (car x)) (vlad-procedure? (cdr x)))
    (run-time-error "Invalid argument to map-closure-reverse" x))
   (let ((f (car x)) (g (cdr x)))
    (cond
     ((closure? g)
      (let* ((bs (map (lambda (v) (make-value-binding (gensym) v))
		      (cons '() (map value-binding-value *value-bindings*))))
	     (e (reverse-transform
		 bs
		 (create-lambda-expression
		  bs
		  (list (closure-variable g))
		  (alpha-rename (closure-body g)))))
	     (xs (free-variables e))
	     (x (lambda-expression-variable e))
	     (e (lambda-expression-body e)))
       (make-closure
	xs
	(list->vector
	 (map (lambda (x)
	       (let ((i (positionq x (closure-variables g))))
		(if i
		    (call f (vector-ref (closure-values g) i))
		    (value-binding-value
		     (find-if (lambda (b) (eq? (value-binding-variable b) x))
			      bs)))))
	      xs))
	x
	(index x xs e))))
     ((recursive-closure? g)
      (let* ((bs (map (lambda (v) (make-value-binding (gensym) v))
		      (cons '() (map value-binding-value *value-bindings*))))
	     (es (reverse-transforms
		  bs
		  (vector->list (recursive-closure-used-binding-maps g))
		  (vector->list (recursive-closure-procedure-variables g))
		  (vector->list
		   (map-vector new-lambda-expression
			       (recursive-closure-argument-variables g)
			       (recursive-closure-bodies g)))))
	     (xs (letrec-free-variables
		  (vector->list (recursive-closure-procedure-variables g))
		  (map lambda-expression-variable es)
		  (map lambda-expression-body es))))
       (make-recursive-closure
	xs
	(list->vector
	 (map (lambda (x)
	       (let ((i (positionq x (recursive-closure-variables g))))
		(if i
		    (call f (vector-ref (recursive-closure-values g) i))
		    (value-binding-value
		     (find-if (lambda (b) (eq? (value-binding-variable b) x))
			      bs)))))
	      xs))
	(recursive-closure-used-binding-maps g)
	(recursive-closure-procedure-variables g)
	(list->vector (map lambda-expression-variable es))
	(list->vector
	 (map
	  (lambda (used-bindings e)
	   (index (lambda-expression-variable e)
		  (append
		   (vector->list
		    (map-vector
		     (lambda (i)
		      (vector-ref (recursive-closure-procedure-variables g) i))
		     used-bindings))
		   xs)
		  (lambda-expression-body e)))
	  (vector->list (recursive-closure-used-binding-maps g))
	  es))
	(recursive-closure-index g))))
     (else (run-time-error "Invalid argument to map-closure-reverse" x))))))
 (define-primitive-procedure 'write
  (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam
