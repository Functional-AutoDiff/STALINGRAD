(MODULE MAP-CLOSURELIB-STUFF)
;;; LaHaShem HaAretz U'Mloah
;;; CVS version control block - do not edit manually
;;;  $RCSfile$
;;;  $Revision$
;;;  $Date$
;;;  $Source$

;;; Map-Closure 0.1
;;; Copyright 2006 Purdue University. All rights reserved.

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
;;;    Lafayette IN 47907-2035 USA
;;;    voice: +1 765 496-3197
;;;    FAX:   +1 765 494-6440
;;;    qobi@purdue.edu
;;;    ftp://ftp.ecn.purdue.edu/qobi
;;;    http://www.ece.purdue.edu/~qobi
;;;             and
;;;    Barak A. Pearlmutter
;;;    Hamilton Institute
;;;    National University of Ireland, Maynooth
;;;    Co. Kildare
;;;    Ireland
;;;    voice: +353 1 7086100
;;;    FAX:   +353 1 7086269
;;;    barak@cs.nuim.ie
;;;    http://www.bcl.hamilton.ie/~barak/

(include "QobiScheme.sch")
(include "map-closurelib-stuff.sch")

;;; Macros

;;; Structures

(define-structure constant-expression value)

(define-structure variable-access-expression variable index)

(define-structure name-expression variable index)

(define-structure lambda-expression
 free-variables
 free-variable-indices			;vector
 variable
 body)

(define-structure application callee argument)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure name procedure meter)

(define-structure closure
 variables
 values					;vector
 variable
 body)

(define-structure name variable)

;;; Variables

(define *gensym* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

;;; Parameters

(define *include-path* '())

(define *metered?* #f)

(define *show-access-indices?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-closures?* #f)

(define *pp?* #f)

(define *cps-converted?* #f)

(define *closure-converted?* #f)

;;; Procedures

;;; VLAD datastructures

(define vlad-true #t)

(define vlad-false #f)

(define (vlad-true? v) (eq? v #t))

(define (vlad-false? v) (eq? v #f))

(define (vlad-boolean? v) (or (vlad-true? v) (vlad-false? v)))

(define (vlad-pair? v) (pair? v))

(define (vlad-car v)
 (unless (vlad-pair? v)
  (run-time-error "Attempt to take vlad-car of a non-pair" v))
 (car v))

(define (vlad-cdr v)
 (unless (vlad-pair? v)
  (run-time-error "Attempt to take vlad-cdr of a non-pair" v))
 (cdr v))

(define (vlad-cons v1 v2) (cons v1 v2))

(define (vlad-procedure? v) (or (primitive-procedure? v) (closure? v)))

(define (vlad-equal? v1 v2)
 (or (eq? v1 v2)
     (and (null? v1) (null? v2))
     (or (and (vlad-true? v1) (vlad-true? v2))
	 (and (vlad-false? v1) (vlad-false? v2)))
     (and (real? v1) (real? v2) (= v1 v2))
     (and (name? v1)
	  (name? v2)
	  (variable=? (name-variable v1) (name-variable v2)))
     (and (vlad-pair? v1)
	  (vlad-pair? v2)
	  (vlad-equal? (vlad-car v1) (vlad-car v2))
	  (vlad-equal? (vlad-cdr v1) (vlad-cdr v2)))
     (and (primitive-procedure? v1)
	  (primitive-procedure? v2)
	  (eq? v1 v2))
     (and (closure? v1)
	  (closure? v2)
	  (= (vector-length (closure-values v1))
	     (vector-length (closure-values v2)))
	  (alpha-equivalent?
	   (closure-body v1)
	   (closure-body v2)
	   (cons (closure-variable v1) (closure-variables v1))
	   (cons (closure-variable v2) (closure-variables v2)))
	  (every-vector vlad-equal? (closure-values v1) (closure-values v2)))))

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (variable? x)
 (or (and (symbol? x)
	  (not (memq x '(quote
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
			 or
			 set!
			 either
			 all-values
			 local-set!
			 ignore
			 consvar
			 alpha))))
     (and (list? x)
	  (= (length x) 1)
	  (eq? (first x) 'ignore))
     (and (list? x)
	  (= (length x) 3)
	  (eq? (first x) 'consvar)
	  (variable? (second x))
	  (variable? (third x)))
     (and (list? x)
	  (= (length x) 3)
	  (eq? (first x) 'alpha)
	  (variable? (second x))
	  (integer? (third x))
	  (exact? (third x))
	  (not (negative? (third x))))))

(define (variable=? x1 x2) (equal? x1 x2))

(define (variable-base x)
 (if (and (list? x) (eq? (first x) 'alpha)) (variable-base (second x)) x))

(define (variable-alpha x)
 (if (and (list? x) (eq? (first x) 'alpha))
     (cons (third x) (variable-alpha (second x)))
     '()))

(define (base-variable<? x1 x2)
 (if (symbol? x1)
     (if (symbol? x2)
	 (string<? (symbol->string x1) (symbol->string x2))
	 #t)
     (if (symbol? x2)
	 #f
	 (if (eq? (first x1) (first x2))
	     (case (first x1)
	      ((ignore) #f)
	      ((consvar) (or (variable<? (second x1) (second x2))
			     (and (variable=? (second x1) (second x2))
				  (variable<? (third x1) (third x2)))))
	      (else (fuck-up)))
	     (not (not (memq (first x2)
			     (memq (first x1) '(ignore consvar)))))))))

(define (variable<? x1 x2)
 (or (base-variable<? (variable-base x1) (variable-base x2))
     (and (variable=? (variable-base x1) (variable-base x2))
	  ((lexicographically<? < =)
	   (reverse (variable-alpha x1)) (reverse (variable-alpha x2))))))

(define (parameter->consvar p)
 (cond ((variable? p) p)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3) (fuck-up))
	  `(consvar ,(parameter->consvar (second p))
		    ,(parameter->consvar (third p))))
	 ((cons*)
	  (case (length (rest p))
	   ((0) '(ignore))
	   ((1) (parameter->consvar (second p)))
	   (else `(consvar ,(parameter->consvar (second p))
			   ,(parameter->consvar `(cons* ,@(rest (rest p))))))))
	 ((list)
	  (if (null? (rest p))
	      '(ignore)
	      `(consvar ,(parameter->consvar (second p))
			,(parameter->consvar `(list ,@(rest (rest p)))))))
	 (else (fuck-up))))
       (else (fuck-up))))

(define (duplicates? xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (member (first xs) (rest xs)) (duplicates? (rest xs)))))

(define (sort-variables xs) (sort xs variable<? identity))

;;; Expression constructors

(define (new-variable-access-expression x)
 (make-variable-access-expression x #f))

(define (new-name-expression x) (make-name-expression x #f))

(define (new-lambda-expression x e)
 (make-lambda-expression (removep variable=? x (free-variables e)) #f x e))

(define (new-application e1 e2) (make-application e1 e2))

(define (new-let* xs es e)
 (if (null? xs)
     e
     (new-application
      (if #f
	  (make-lambda-expression #f
				  #f
				  (first xs)
				  (new-let* (rest xs) (rest es) e))
	  (new-lambda-expression (first xs) (new-let* (rest xs) (rest es) e)))
      (first es))))

(define (union-variables xs1 xs2) (unionp variable=? xs1 xs2))

;;; LET*

(define (let*? e)
 (and (application? e) (lambda-expression? (application-callee e))))

(define (let*-variables e)
 (if (let*? e)
     (cons (lambda-expression-variable (application-callee e))
	   (let*-variables (lambda-expression-body (application-callee e))))
     '()))

(define (let*-expressions e)
 (if (let*? e)
     (cons (application-argument e)
	   (let*-expressions (lambda-expression-body (application-callee e))))
     '()))

(define (let*-body e)
 (if (let*? e) (let*-body (lambda-expression-body (application-callee e))) e))

;;; Search path

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
 (let ((pathname (default-extension pathname "vlad")))
  (unless (can-open-file-for-input? pathname)
   (panic (format #f "Cannot find: ~a" pathname)))
  (call-with-input-file pathname
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
       (else (loop (cons e es))))))))))

;;; Standard prelude

(define (standard-prelude e)
 `(let* ((ys (let* ((y (lambda (f)
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
		   ((map (lambda (f) (lambda (x) ((f (ys fs)) x))))
		    fs)))))))
   ,e))

;;; Definitions

(define (definens? e)
 (or (variable? e) (and (list? e) (not (null? e)) (definens? (first e)))))

(define (definition? d)
 (and
  (list? d) (= (length d) 3) (eq? (first d) 'define) (definens? (second d))))

(define (definens-name e) (if (variable? e) e (definens-name (first e))))

(define (definens-expression e1 e2)
 (if (variable? e1)
     e2
     (definens-expression (first e1) `(lambda ,(rest e1) ,e2))))

(define (expand-definitions ds e)
 (for-each (lambda (d)
	    (unless (definition? d)
	     (panic (format #f "Invalid definition: ~s" d))))
	   ds)
 (standard-prelude
  `(letrec ,(map (lambda (d)
		  `(,(definens-name (second d))
		    ,(definens-expression (second d) (third d))))
		 ds)
    ,e)))

;;; Alpha conversion

(define (alphaify x xs)
 (if (memp variable=? x xs)
     `(alpha ,x
	     ,(+ (reduce max
			 (map (lambda (x1)
			       (if (and (list? x1)
					(eq? (first x1) 'alpha)
					(variable=? (second x1) x))
				   (third x1)
				   0))
			      xs)
			 0)
		 1))
     x))

(define (alpha-convert e xs)
 (second
  (let outer ((e e) (xs xs) (bs (map make-alpha-binding xs xs)))
   (cond
    ((constant-expression? e) e)
    ((variable-access-expression? e)
     (list xs
	   (new-variable-access-expression
	    (alpha-binding-variable2
	     (find-if (lambda (b)
		       (variable=? (alpha-binding-variable1 b)
				   (variable-access-expression-variable e)))
		      bs)))))
    ((name-expression? e)
     (list xs
	   (new-name-expression
	    (alpha-binding-variable2
	     (find-if (lambda (b)
		       (variable=? (alpha-binding-variable1 b)
				   (name-expression-variable e)))
		      bs)))))
    ((lambda-expression? e)
     (let* ((x (alphaify (lambda-expression-variable e) xs))
	    (result (outer (lambda-expression-body e)
			   (cons x xs)
			   (cons (make-alpha-binding
				  (lambda-expression-variable e) x)
				 bs))))
      (list (first result) (new-lambda-expression x (second result)))))
    ((application? e)
     (let* ((result1 (outer (application-callee e) xs bs))
	    (result2 (outer (application-argument e) (first result1) bs)))
      (list (first result2)
	    (new-application (second result1) (second result2)))))
    (else (fuck-up))))))

(define (alpha-equivalent? e1 e2 xs1 xs2)
 (or
  (and (variable-access-expression? e1)
       (variable-access-expression? e2)
       (= (positionp variable=? (variable-access-expression-variable e1) xs1)
	  (positionp variable=? (variable-access-expression-variable e2) xs2)))
  (and (name-expression? e1)
       (name-expression? e2)
       (= (positionp variable=? (name-expression-variable e1) xs1)
	  (positionp variable=? (name-expression-variable e2) xs2)))
  (and (lambda-expression? e1)
       (lambda-expression? e2)
       (alpha-equivalent? (lambda-expression-body e1)
			  (lambda-expression-body e2)
			  (cons (lambda-expression-variable e1) xs1)
			  (cons (lambda-expression-variable e2) xs2)))
  (and (application? e1)
       (application? e2)
       (alpha-equivalent?
	(application-callee e1) (application-callee e2) xs1 xs2)
       (alpha-equivalent?
	(application-argument e1) (application-argument e2) xs1 xs2))))

;;; Conversion

(define (new-let xs es e) (new-let* xs es e))

;;; CPS Conversion

(define (cps-car e)
 (new-application (new-variable-access-expression 'cps-car) e))

(define (cps-cdr e)
 (new-application (new-variable-access-expression 'cps-cdr) e))

(define (cps-cons e1 e2)
 (new-application
  (new-application (new-variable-access-expression 'cps-cons-procedure) e1)
  e2))

(define (cps-cons* es)
 (cond ((null? es) (make-constant-expression '()))
       ((null? (rest es)) (first es))
       (else (cps-cons (first es) (cps-cons* (rest es))))))

(define (cps-application e . es) (new-application e (cps-cons* es)))

(define (cps-convert e)
 (new-let
  '(cps-car cps-cdr cps-cons-procedure)
  (list (new-variable-access-expression 'car)
	(new-variable-access-expression 'cdr)
	(new-variable-access-expression 'cons-procedure))
  (new-let
   (free-variables e)
   (map (lambda (x)
	 ;; This assumes that all free variables in e are bound to
	 ;; primitive procedures.
	 (cond ((variable=? x 'call-with-current-continuation)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-cdr x)
		    ((cps-cons-procedure (cps-car x))
		     (lambda (y) ((cps-car x) (cps-cdr y))))))))
	       ((variable=? x 'cons-procedure)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-car x)
		    (lambda (y)
		     ((cps-car y)
		      ((cps-cons-procedure (cps-cdr x)) (cps-cdr y))))))))
	       ((variable=? x 'map-closure)
		(concrete->abstract-expression
		 '(lambda (x)
		   ((cps-car x)
		    (map-closure
		     ((cps-cons-procedure
		       (lambda (y)
			((cps-car (cps-cdr x))
			 ((cps-cons-procedure (lambda (x) x)) y))))
		      (cps-cdr (cps-cdr x))))))))
	       (else (let ((x1 (gensym)))
		      (new-lambda-expression
		       x1
		       (new-application
			(cps-car (new-variable-access-expression x1))
			(new-application
			 (new-variable-access-expression x)
			 (cps-cdr (new-variable-access-expression x1)))))))))
	(free-variables e))
   (let loop ((e1 (new-lambda-expression
		   'x (new-variable-access-expression 'x)))
	      (e2 e))
    (cond ((constant-expression? e2) (new-application e1 e2))
	  ((variable-access-expression? e2) (new-application e1 e2))
	  ((name-expression? e2) (new-application e1 e2))
	  ((lambda-expression? e2)
	   (let ((x (gensym)))
	    (new-application
	     e1
	     (new-lambda-expression
	      x
	      (new-let* (list (lambda-expression-variable e2))
			(list (cps-cdr (new-variable-access-expression x)))
			(loop (cps-car (new-variable-access-expression x))
			      (lambda-expression-body e2)))))))
	  ((application? e2)
	   (let ((x1 (gensym)) (x2 (gensym)))
	    (loop
	     (new-lambda-expression
	      x1
	      (loop (new-lambda-expression
		     x2
		     (cps-application (new-variable-access-expression x1)
				      e1
				      (new-variable-access-expression x2)))
		    (application-argument e2)))
	     (application-callee e2))))
	  (else (fuck-up)))))))

;;; Closure Conversion

(define (closure-car e)
 (new-application (new-variable-access-expression 'closure-car) e))

(define (closure-cdr e)
 (new-application (new-variable-access-expression 'closure-cdr) e))

(define (closure-cons e1 e2)
 (new-application
  (new-application (new-variable-access-expression 'closure-cons-procedure) e1)
  e2))

(define (closure-cons* es)
 (cond ((null? es) (make-constant-expression '()))
       ((null? (rest es)) (first es))
       (else (closure-cons (first es) (closure-cons* (rest es))))))

(define (closure-list es)
 (if (null? es)
     (make-constant-expression '())
     (closure-cons (first es) (closure-list (rest es)))))

(define (closure-application e . es) (new-application e (closure-cons* es)))

(define (closure-convert e)
 (new-let
  '(closure-car
    closure-cdr
    closure-cons-procedure
    closure-if-procedure
    closure-pair?
    closure-procedure?)
  (list (new-variable-access-expression 'car)
	(new-variable-access-expression 'cdr)
	(new-variable-access-expression 'cons-procedure)
	(new-variable-access-expression 'if-procedure)
	(new-variable-access-expression 'pair?)
	(new-variable-access-expression 'procedure?))
  (let ((x (gensym)))
   (new-let
    (free-variables e)
    (map (lambda (x)
	  ;; This assumes that all free variables in e are bound to
	  ;; primitive procedures.
	  (closure-cons
	   (cond
	    ((variable=? x 'pair?)
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-if-procedure
		  ((closure-cons-procedure (closure-pair? (closure-cdr x)))
		   ((closure-cons-procedure
		     (lambda (y)
		      ((closure-if-procedure
			((closure-cons-procedure
			  (closure-procedure? (closure-car (closure-cdr x))))
			 ((closure-cons-procedure (lambda (y) #f))
			  (lambda (y) #t))))
		       '())))
		    (lambda (y) #f))))
		 '()))))
	    ((variable=? x 'procedure?)
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-if-procedure
		  ((closure-cons-procedure (closure-pair? (closure-cdr x)))
		   ((closure-cons-procedure
		     (lambda (y)
		      (closure-procedure? (closure-car (closure-cdr x)))))
		    (lambda (y) #f))))
		 '()))))
	    ((variable=? x 'map-closure)
	     (concrete->abstract-expression
	      '(let* ((y (lambda (f)
			  ((lambda (g) (lambda (x) ((f (g g)) x)))
			   (lambda (g) (lambda (x) ((f (g g)) x))))))
		      (map
		       (lambda (f)
			(y (lambda (map)
			    (lambda (l)
			     ((closure-if-procedure
			       ((closure-cons-procedure (null? l))
				((closure-cons-procedure (lambda (x) l))
				 (lambda (x)
				  ((closure-cons-procedure (f (closure-car l)))
				   (map (closure-cdr l)))))))
			      '())))))))
		(lambda (x)
		 ((closure-cons-procedure
		   (closure-car (closure-cdr (closure-cdr x))))
		  ((map (lambda (y)
			 ((closure-cons-procedure (closure-car y))
			  ((closure-car (closure-car (closure-cdr x)))
			   ((closure-cons-procedure
			     (closure-cdr (closure-car (closure-cdr x))))
			    y)))))
		   (closure-cdr (closure-cdr (closure-cdr x)))))))))
	    ((variable=? x 'cons-procedure)
	     (concrete->abstract-expression
	      '(lambda (x)
		((closure-cons-procedure
		  (lambda (y)
		   ((closure-cons-procedure (closure-cdr x)) (closure-cdr y))))
		 '()))))
	    (else (let ((x1 (gensym)))
		   (new-lambda-expression
		    x1
		    (new-application
		     (new-variable-access-expression x)
		     (closure-cdr (new-variable-access-expression x1)))))))
	   (make-constant-expression '())))
	 (free-variables e))
    (new-let
     (list x)
     (list (closure-list
	    (map (lambda (x)
		  (closure-cons (new-name-expression x)
				(new-variable-access-expression x)))
		 (free-variables e))))
     (let loop ((x1 x) (e e))
      (cond
       ((constant-expression? e) e)
       ((variable-access-expression? e)
	(closure-application
	 (new-variable-access-expression 'lookup)
	 (new-name-expression (variable-access-expression-variable e))
	 (new-variable-access-expression x1)))
       ((name-expression? e) e)
       ((lambda-expression? e)
	(let ((x2 (gensym)) (x3 (gensym)) (x4 (gensym)))
	 (closure-cons
	  (new-lambda-expression
	   x2
	   (new-let*
	    (list x3 (lambda-expression-variable e) x4)
	    (list
	     (closure-car (new-variable-access-expression x2))
	     (closure-cdr (new-variable-access-expression x2))
	     (closure-cons
	      (closure-cons
	       (new-name-expression (lambda-expression-variable e))
	       (new-variable-access-expression (lambda-expression-variable e)))
	      (new-variable-access-expression x3)))
	    (loop x4 (lambda-expression-body e))))
	  (closure-list
	   (map (lambda (x)
		 (closure-cons (new-name-expression x)
			       (loop x1 (new-variable-access-expression x))))
		(free-variables e))))))
       ((application? e)
	(let ((x2 (gensym)))
	 (new-let (list x2)
		  (list (loop x1 (application-callee e)))
		  (closure-application
		   (closure-car (new-variable-access-expression x2))
		   (closure-cdr (new-variable-access-expression x2))
		   (loop x1 (application-argument e))))))
       (else (fuck-up)))))))))

;;; Constant Conversion

(define (constants-in e)
 (cond ((constant-expression? e) (list (constant-expression-value e)))
       ((variable-access-expression? e) '())
       ((name-expression? e) '())
       ((lambda-expression? e) (constants-in (lambda-expression-body e)))
       ((application? e)
	(unionp vlad-equal?
		(constants-in (application-callee e))
		(constants-in (application-argument e))))
       (else (fuck-up))))

(define (constant-convert bs e)
 (cond ((constant-expression? e)
	(new-variable-access-expression
	 (value-binding-variable
	  (find-if (lambda (b)
		    (vlad-equal? (value-binding-value b)
				 (constant-expression-value e)))
		   bs))))
       ((variable-access-expression? e) e)
       ((name-expression? e) e)
       ((lambda-expression? e)
	(new-lambda-expression
	 (lambda-expression-variable e)
	 (constant-convert bs (lambda-expression-body e))))
       ((application? e)
	(new-application (constant-convert bs (application-callee e))
			 (constant-convert bs (application-argument e))))
       (else (fuck-up))))

;;; Free variables

(define (letrec-recursive-closure-variables xs1 xs2 es)
 (sort-variables
  (set-differencep
   variable=?
   (reduce
    union-variables
    (map (lambda (x e) (removep variable=? x (free-variables e))) xs2 es)
    '())
   xs1)))

(define (free-variables e)
 (sort-variables
  (let loop ((e e))
   (cond ((constant-expression? e) '())
	 ((variable-access-expression? e)
	  (list (variable-access-expression-variable e)))
	 ((name-expression? e) (list (name-expression-variable e)))
	 ((lambda-expression? e)
	  ;; This is a vestigial let*-expression.
	  (if (eq? (lambda-expression-free-variables e) #f)
	      (removep variable=?
		       (lambda-expression-variable e)
		       (loop (lambda-expression-body e)))
	      (lambda-expression-free-variables e)))
	 ((application? e)
	  (union-variables (loop (application-callee e))
			   (loop (application-argument e))))
	 (else (fuck-up))))))

(define (vector-append . vss)
 (list->vector (reduce append (map vector->list vss) '())))

(define (index x xs e)
 (define (lookup x-prime)
  (unless (or (variable=? x-prime x) (memp variable=? x-prime xs)) (fuck-up))
  ;; The reverse is necessary because let*-expression doesn't prune unaccessed
  ;; variables.
  (if (memp variable=? x-prime xs)
      ;; This is a vestigial let*-expression.
      (- (length xs) (positionp variable=? x-prime (reverse xs)) 1)
      -1))
 (cond ((variable-access-expression? e)
	(make-variable-access-expression
	 (variable-access-expression-variable e)
	 (lookup (variable-access-expression-variable e))))
       ((name-expression? e)
	(make-name-expression
	 (name-expression-variable e) (lookup (name-expression-variable e))))
       ((lambda-expression? e)
	(make-lambda-expression
	 (lambda-expression-free-variables e)
	 ;; This is a vestigial let*-expression.
	 (if (eq? (lambda-expression-free-variables e) #f)
	     #f
	     (list->vector (map lookup (free-variables e))))
	 (lambda-expression-variable e)
	 (index (lambda-expression-variable e)
		(free-variables e)
		(lambda-expression-body e))))
       ((application? e)
	(make-application (index x xs (application-callee e))
			  (index x xs (application-argument e))))
       (else (fuck-up))))

;;; Concrete->Abstract

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (internalize v)
 (cond ((null? v) v)
       ((boolean? v) (if v vlad-true vlad-false))
       ((real? v) v)
       ((pair? v) (vlad-cons (internalize (car v)) (internalize (cdr v))))
       (else (fuck-up))))

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
       ((variable? p) e)
       ((and (list? p) (not (null? p)))
	(case (first p)
	 ((cons)
	  (unless (= (length p) 3)
	   (panic (format #f "Invalid parameter: ~s" p)))
	  (let ((x (parameter->consvar p)))
	   `(lambda (,x)
	     (let* ((,(second p) (car ,x)) (,(third p) (cdr ,x)))
	      ,(third e)))))
	 ((cons*)
	  (case (length (rest p))
	   ((0) `(lambda ((ignore)) ,(third e)))
	   ((1) `(lambda (,(second p)) ,(third e)))
	   (else `(lambda ((cons ,(second p) (cons* ,@(rest (rest p)))))
		   ,(third e)))))
	 ((list)
	  (if (null? (rest p))
	      `(lambda ((ignore)) ,(third e))
	      `(lambda ((cons ,(second p) (list ,@(rest (rest p)))))
		,(third e))))
	 (else (panic (format #f "Invalid parameter: ~s" p)))))
       (else (panic (format #f "Invalid parameter: ~s" p))))))
    (else `(lambda ((cons* ,@(second e))) ,(third e)))))
  ((letrec)
   (unless (and (= (length e) 3)
		(list? (second e))
		(every (lambda (b)
			(and (list? b) (= (length b) 2) (variable? (first b))))
		       (second e)))
    (panic (format #f "Invalid expression: ~s" e)))
   (if (null? (second e))
       ;; This allows removing the standard prelude for debugging purposes.
       (third e)
       `(let (((list ,@(map first (second e)))
	       (ys (list ,@(map (lambda (b)
				 `(lambda ((list ,@(map first (second e))))
				   ,(second b)))
				(second e))))))
	 ,(third e))))
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
  ((if)
   (unless (= (length e) 4) (panic (format #f "Invalid expression: ~s" e)))
   `((if-procedure
      ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e)))))
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
  ((set!)
   (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
   `(set (name ,(second e)) ,(third e)))
  ((either)
   (if (null? (rest e))
       '(fail)
       `(if (a-boolean) ,(second e) (either ,@(rest (rest e))))))
  ((all-values)
   (unless (= (length e) 2) (panic (format #f "Invalid expression: ~s" e)))
   `(all-values-thunk (lambda () ,(second e))))
  ((local-set!)
   (unless (= (length e) 3) (panic (format #f "Invalid expression: ~s" e)))
   `(local-set (name ,(second e)) ,(third e)))
  (else (case (length (rest e))
	 ((0) `(,(first e) (cons* ,@(rest e))))
	 ((1) e)
	 (else `(,(first e) (cons* ,@(rest e))))))))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs (map value-binding-variable *value-bindings*)))
  (cond
   ((null? e) (panic (format #f "Invalid expression: ~s" e)))
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((variable? e)
    (unless (memp variable=? e xs)
     (panic (format #f "Unbound variable: ~s" e)))
    #f)
   ((list? e)
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (panic (format #f "Invalid expression: ~s" e)))
	      #f)
     ((name) (unless (and (= (length e) 2) (variable? (second e)))
	      (panic (format #f "Invalid expression: ~s" e)))
	     (unless (memp variable=? (second e) xs)
	      (panic (format #f "Unbound variable: ~s" e)))
	     #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (panic (format #f "Invalid expression: ~s" e)))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (if (variable? (first (second e)))
		;; We no longer check for duplicate variables.
		(loop (third e) (cons (first (second e)) xs))
		(loop (macro-expand e) xs)))
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
     ((set!) (loop (macro-expand e) xs))
     ((either) (loop (macro-expand e) xs))
     ((all-values) (loop (macro-expand e) xs))
     ((local-set!) (loop (macro-expand e) xs))
     (else (case (length (rest e))
	    ((0) (loop (macro-expand e) xs))
	    ((1) (loop (first e) xs)
		 (loop (second e) xs))
	    (else (loop (macro-expand e) xs))))))
   (else (panic (format #f "Invalid expression: ~s" e))))))

(define (concrete->abstract-expression e)
 (cond
  ((boolean? e) (concrete->abstract-expression `',e))
  ((real? e) (concrete->abstract-expression `',e))
  ((variable? e) (new-variable-access-expression e))
  ((list? e)
   (case (first e)
    ((quote) (make-constant-expression (internalize (second e))))
    ((name) (new-name-expression (second e)))
    ((lambda)
     (case (length (second e))
      ((0) (concrete->abstract-expression (macro-expand e)))
      ((1) (if (variable? (first (second e)))
	       (new-lambda-expression
		(first (second e)) (concrete->abstract-expression (third e)))
	       (concrete->abstract-expression (macro-expand e))))
      (else (concrete->abstract-expression (macro-expand e)))))
    ((letrec) (concrete->abstract-expression (macro-expand e)))
    ((let) (concrete->abstract-expression (macro-expand e)))
    ((let*) (concrete->abstract-expression (macro-expand e)))
    ((if) (concrete->abstract-expression (macro-expand e)))
    ((cons) (concrete->abstract-expression (macro-expand e)))
    ((cons*) (concrete->abstract-expression (macro-expand e)))
    ((list) (concrete->abstract-expression (macro-expand e)))
    ((cond) (concrete->abstract-expression (macro-expand e)))
    ((and) (concrete->abstract-expression (macro-expand e)))
    ((or) (concrete->abstract-expression (macro-expand e)))
    ((set!) (concrete->abstract-expression (macro-expand e)))
    ((either) (concrete->abstract-expression (macro-expand e)))
    ((all-values) (concrete->abstract-expression (macro-expand e)))
    ((local-set!) (concrete->abstract-expression (macro-expand e)))
    (else (case (length (rest e))
	   ((0) (concrete->abstract-expression (macro-expand e)))
	   ((1) (new-application (concrete->abstract-expression (first e))
				 (concrete->abstract-expression (second e))))
	   (else (concrete->abstract-expression (macro-expand e)))))))
  (else (fuck-up))))

(define (parse e)
 ;; needs work: we no-longer alpha convert
 (let* ((e (concrete->abstract-expression e))
	(e (if *cps-converted?* (cps-convert e) e))
	(e (if *closure-converted?* (closure-convert e) e))
	(bs (map (lambda (v) (make-value-binding (gensym) v))
		 (constants-in e)))
	(e (constant-convert bs e))
	(xs (free-variables e))
	(bs (append bs *value-bindings*)))
  (list
   (index #f xs e)
   (map (lambda (x)
	 (value-binding-value
	  (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs)))
	xs))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (abstract->concrete e)
 (cond
  ((let*? e)
   (let loop ((xs (let*-variables e)) (es (let*-expressions e)) (bs '()))
    (if (null? xs)
	(case (length bs)
	 ((0) (fuck-up))
	 ((1) `(let ,bs ,(abstract->concrete (let*-body e))))
	 (else `(let* ,(reverse bs) ,(abstract->concrete (let*-body e)))))
	(loop (rest xs)
	      (rest es)
	      (cons `(,(first xs) ,(abstract->concrete (first es))) bs)))))
  ((constant-expression? e)
   `',(externalize (constant-expression-value e)))
  ((variable-access-expression? e)
   (let* ((x (variable-access-expression-variable e))
	  (x (if (primitive-procedure? x)
		 (primitive-procedure-name x)
		 x)))
    (if *show-access-indices?*
	`(access ,x ,(variable-access-expression-index e))
	x)))
  ((name-expression? e)
   (if *show-access-indices?*
       `(name ,(name-expression-variable e)
	      ,(name-expression-index e))
       `(name ,(name-expression-variable e))))
  ((lambda-expression? e)
   `(lambda (,(lambda-expression-variable e))
     ,(abstract->concrete (lambda-expression-body e))))
  ((application? e)
   `(,(abstract->concrete (application-callee e))
     ,(abstract->concrete (application-argument e))))
  (else (fuck-up))))

(define (quotable? v)
 (cond ((null? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((real? v) #t)
       ((name? v) #t)
       ((vlad-pair? v) (and (quotable? (vlad-car v)) (quotable? (vlad-cdr v))))
       ((primitive-procedure? v) #f)
       ((closure? v) #f)
       (else (fuck-up))))

(define (externalize v)
 (let ((v
	(let loop ((v v) (quote? #f))
	 (cond
	  ((null? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((vlad-true? v) #t)
	  ((vlad-false? v) #f)
	  ((real? v) v)
	  ((name? v) `(name ,(name-variable v)))
	  ((vlad-pair? v)
	   (if (and *unabbreviate-executably?* (not quote?))
	       (if (quotable? v)
		   `',(cons (loop (vlad-car v) #t) (loop (vlad-cdr v) #t))
		   `(cons ,(loop (vlad-car v) #f) ,(loop (vlad-cdr v) #f)))
	       (cons (loop (vlad-car v) quote?) (loop (vlad-cdr v) quote?))))
	  ((primitive-procedure? v)
	   (cond (*unabbreviate-executably?*
		  (when quote? (fuck-up))
		  (string->symbol
		   (string-append (symbol->string (primitive-procedure-name v))
				  (symbol->string '-primitive))))
		 (else (primitive-procedure-name v))))
	  ((closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (when quote? (fuck-up))
	     (case (length (closure-variables v))
	      ((0)
	       `(lambda (,(closure-variable v))
		 ,(abstract->concrete (closure-body v))))
	      ((1)
	       `(let ,(map-indexed
		       (lambda (x i)
			`(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		       (closure-variables v))
		 (lambda (,(closure-variable v))
		  ,(abstract->concrete (closure-body v)))))
	      (else
	       ;; This really should be a let but since the free variables
	       ;; might include car, cdr, and cons-procedure, shadowing them
	       ;; might break multiple-binding let which structures and
	       ;; destructures with car, cdr, and cons-procedure. Thus we use
	       ;; let* which does no such structuring and destructuring.
	       `(let* ,(map-indexed
			(lambda (x i)
			 `(,x
			   ,(loop (vector-ref (closure-values v) i) quote?)))
			(closure-variables v))
		 (lambda (,(closure-variable v))
		  ,(abstract->concrete (closure-body v)))))))
	    (*unabbreviate-closures?*
	     `(closure
	       ,(map-indexed
		 (lambda (x i)
		  `(,x ,(loop (vector-ref (closure-values v) i) quote?)))
		 (closure-variables v))
	       (lambda (,(closure-variable v))
		,(abstract->concrete (closure-body v)))))
	    (else `(lambda (,(closure-variable v))
		    ,(abstract->concrete (closure-body v))))))
	  (else (fuck-up))))))
  (if *unabbreviate-executably?*
      `(let* ,(map (lambda (b)
		    (let ((x (value-binding-variable b)))
		     `(,(string->symbol
			 (string-append (symbol->string x)
					(symbol->string '-primitive)))
		       ,x)))
		   *value-bindings*)
	,v)
      v)))

;;; Evaluator

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

(define (run-time-error message . vs)
 (format #t "Stack trace~%")
 (for-each (lambda (record)
	    (display "Procedure: ")
	    ((if *pp?* pp write) (externalize (first record)))
	    (newline)
	    (display "Argument: ")
	    ((if *pp?* pp write) (externalize (second record)))
	    (newline)
	    (newline))
	   *stack*)
 (newline)
 (for-each (lambda (v) ((if *pp?* pp write) (externalize v)) (newline)) vs)
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
	      (externalize callee)
	      (externalize argument))
      (format #t "~aentering ~s~%"
	      (make-string *trace-level* #\space)
	      (externalize callee)))
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
	 (else (fuck-up)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? callee) *trace-primitive-procedures?*)
	      ((closure? callee) *trace-closures?*)
	      (else (fuck-up)))
   (set! *trace-level* (- *trace-level* 1))
   (if *trace-argument/result?*
       (format #t "~aexiting ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize callee)
	       (externalize result))
       (format #t "~aexiting ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize callee))))
  result))

(define (evaluate e v vs)
 (define (lookup i) (if (= i -1) v (vector-ref vs i)))
 (cond ((variable-access-expression? e)
	(lookup (variable-access-expression-index e)))
       ((name-expression? e) (make-name (name-expression-variable e)))
       ((lambda-expression? e)
	(make-closure
	 (free-variables e)
	 (map-vector lookup (lambda-expression-free-variable-indices e))
	 (lambda-expression-variable e)
	 (lambda-expression-body e)))
       ((application? e)
	;; This LET* is to specify the evaluation order.
	(let* ((callee (evaluate (application-callee e) v vs))
	       (argument (evaluate (application-argument e) v vs)))
	 (call callee argument)))
       (else (fuck-up))))

;;; Primitives

(define (divide x1 x2)
 ;; An approximation of IEEE since Scheme->C hides it. Doesn't handle positive
 ;; vs. negative zero x2.
 (if (zero? x2)
     (cond ((positive? x1) infinity)
	   ((negative? x1) minus-infinity)
	   ;; Both zeros and nan.
	   (else nan))
     (/ x1 x2)))

(define (unary f s) f)

(define (unary-predicate f s) (lambda (x) (if (f x) vlad-true vlad-false)))

(define (unary-real f s)
 (lambda (x)
  (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f x)))

(define (unary-real-predicate f s)
 (lambda (x)
  (unless (real? x) (run-time-error (format #f "Invalid argument to ~a" s) x))
  (if (f x) vlad-true vlad-false)))

(define (binary f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (f (vlad-car x) (vlad-cdr x))))

(define (binary-real f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 x2))))

(define (binary-real-predicate f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x2 (vlad-cdr x)))
   (unless (and (real? x1) (real? x2))
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (if (f x1 x2) vlad-true vlad-false))))

(define (ternary f s)
 (lambda (x)
  (unless (vlad-pair? x)
   (run-time-error (format #f "Invalid argument to ~a" s) x))
  (let ((x1 (vlad-car x)) (x23 (vlad-cdr x)))
   (unless (vlad-pair? x23)
    (run-time-error (format #f "Invalid argument to ~a" s) x))
   (f x1 (vlad-car x23) (vlad-cdr x23)))))

(define (define-primitive-procedure x procedure)
 (set! *value-bindings*
       (cons (make-value-binding x (make-primitive-procedure x procedure 0))
	     *value-bindings*)))

(define (initialize-basis!)
 (define-primitive-procedure '+ (binary-real + "+"))
 (define-primitive-procedure '- (binary-real - "-"))
 (define-primitive-procedure '* (binary-real * "*"))
 (define-primitive-procedure '/ (binary-real divide "/"))
 (define-primitive-procedure 'sqrt (unary-real sqrt "sqrt"))
 (define-primitive-procedure 'exp (unary-real exp "exp"))
 (define-primitive-procedure 'log (unary-real log "log"))
 (define-primitive-procedure 'sin (unary-real sin "sin"))
 (define-primitive-procedure 'cos (unary-real cos "cos"))
 (define-primitive-procedure 'atan (binary-real atan "atan"))
 (define-primitive-procedure '= (binary-real-predicate = "="))
 (define-primitive-procedure '< (binary-real-predicate < "<"))
 (define-primitive-procedure '> (binary-real-predicate > ">"))
 (define-primitive-procedure '<= (binary-real-predicate <= "<="))
 (define-primitive-procedure '>= (binary-real-predicate >= ">="))
 (define-primitive-procedure 'zero? (unary-real-predicate zero? "zero?"))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?"))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?"))
 (define-primitive-procedure 'null? (unary-predicate null? "null?"))
 (define-primitive-procedure 'boolean?
  (unary-predicate vlad-boolean? "boolean?"))
 (define-primitive-procedure 'real? (unary-predicate real? "real?"))
 (define-primitive-procedure 'pair? (unary-predicate vlad-pair? "pair?"))
 (define-primitive-procedure 'procedure?
  (unary-predicate vlad-procedure? "procedure?"))
 (define-primitive-procedure 'equal?
  (binary (lambda (x1 x2) (if (equal? x1 x2) vlad-true vlad-false)) "equal?"))
 (define-primitive-procedure 'write
  (unary (lambda (x) ((if *pp?* pp write) (externalize x)) (newline) x)
	 "write"))
 ;; These might be Church encoded.
 (define-primitive-procedure 'car (binary (lambda (x1 x2) x1) "car"))
 (define-primitive-procedure 'cdr (binary (lambda (x1 x2) x2) "cdr"))
 (define-primitive-procedure 'cons-procedure
  (unary (lambda (x1)
	  (make-primitive-procedure
	   "cons-procedure" (lambda (x2) (vlad-cons x1 x2)) 0))
	 "cons-procedure"))
 (define-primitive-procedure 'if-procedure
  (ternary (lambda (x1 x2 x3) (if x1 x2 x3)) "if-procedure"))
 ;; These are specific to Map-Closure.
 (define-primitive-procedure 'name? (unary-predicate name? "name?"))
 (define-primitive-procedure 'name=?
  (binary (lambda (x1 x2)
	   (unless (and (name? x1) (name? x2))
	    (run-time-error "Invalid argument to name?" (vlad-cons x1 x2)))
	   (if (variable=? (name-variable x1) (name-variable x2))
	       vlad-true
	       vlad-false))
	  "name=?"))
 (define-primitive-procedure 'call-with-current-continuation
  (unary (lambda (x)
	  (run-time-error "Cannot call call-with-current-continuation unless CPS conversion is enabled" x))
	 "call-with-current-continuation"))
 (define-primitive-procedure 'map-closure
  (unary (lambda (x)
	  (run-time-error "Cannot call map-closure unless closure conversion is enabled" x))
	 "map-closure"))
 ;; debugging
 (define-primitive-procedure 'lookup
  (binary (lambda (x1 x2)
	   (unless (name? x1)
	    (run-time-error "Invalid argument to lookup" (vlad-cons x1 x2)))
	   (let loop ((x x2))
	    (when (null? x) (fuck-up))
	    (unless (and (vlad-pair? x)
			 (vlad-pair? (vlad-car x))
			 (name? (vlad-car (vlad-car x))))
	     (run-time-error "Invalid argument to lookup" (vlad-cons x1 x2)))
	    (if (variable=? (name-variable (vlad-car (vlad-car x)))
			    (name-variable x1))
		(vlad-cdr (vlad-car x))
		(loop (vlad-cdr x)))))
	  "lookup")))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
