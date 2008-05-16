(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah
;;; $Id$

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004, 2005, 2006, 2007, and 2008 Purdue University. All rights
;;; reserved.

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
;;;    National University of Ireland Maynooth
;;;    Co. Kildare
;;;    Ireland
;;;    voice: +353 1 7086100
;;;    FAX:   +353 1 7086269
;;;    barak@cs.nuim.ie
;;;    http://www.bcl.hamilton.ie/~barak/

(include "QobiScheme.sch")
(include "c-externals.sc")
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. zero, perturb, unperturb, primal, tangent, bundle, sensitize,
;;;     unsensitize, plus, *j, and *j-inverse should be lazy.
;;;  2. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  3. unary -
;;;  4. begin, case, delay, do, named let, quasiquote, unquote,
;;;     unquote-splicing, internal defines
;;;  5. chars, ports, eof object, symbols, continuations, strings, vectors

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete or abstract variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: concrete or abstract value
;;;  d: definition
;;;  record, geysym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

(define-macro assert
 (lambda (form expander)
  (unless (= (length form) 2)
   (error 'assert "Wrong number of arguments: ~s" form))
  (expander `(assert-internal (lambda () ,(second form))) expander)))

(define-macro time-it
 ;; belongs in QobiScheme
 (lambda (form expander)
  (let* ((string (format #f "~a" (second form)))
	 (string (if (<= (string-length string) 60)
		     string
		     (substring string 0 60))))
   (expander
    (if #f				;debugging
	`(time ,(format #f "~~a ~a~~%" string) (lambda () ,(second form)))
	(second form))
    expander))))

(define-macro time-it-bucket
 ;; belongs in QobiScheme
 (lambda (form expander)
  (expander
   (if #t				;debugging
       `(time-bucket ,(second form) (lambda () ,(third form)))
       (third form))
   expander)))

;;; Structures

(define-structure variable
 name
 index
 perturbationify
 forwardify
 sensitivityify
 reverseify
 unperturbationify
 unforwardify
 unsensitivityify
 unreverseify)

(define-structure constant-expression
 parents
 environment-bindings
 value)

(define-structure variable-access-expression
 parents
 environment-bindings
 variable)

(define-structure lambda-expression
 alpha-conversion-inverse
 perturbation-transform
 perturbation-transform-inverse
 forward-transform
 forward-transform-inverse
 sensitivity-transform
 sensitivity-transform-inverse
 reverse-transform
 reverse-transform-inverse
 nonrecursive-closures
 recursive-closures
 parents
 environment-bindings
 free-variables
 parameter
 body)

(define-structure application
 parents
 environment-bindings
 enqueue?
 free-variables
 callee
 argument)

(define-structure letrec-expression
 parents
 environment-bindings
 enqueue?
 free-variables
 procedure-variables
 lambda-expressions
 body)

(define-structure cons-expression
 parents
 environment-bindings
 enqueue?
 free-variables
 tags
 car
 cdr)

(define-structure variable-binding variable expression)

(define-structure parameter-binding parameter expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 name procedure generator forward reverse meter)

(define-structure nonrecursive-closure
 values
 lambda-expression
 canonical?
 interned?
 widen
 c:index
 boxed?
 void?)

(define-structure recursive-closure
 values
 procedure-variables			;vector
 lambda-expressions			;vector
 index
 canonical?
 interned?
 widen
 c:index
 boxed?
 void?)

(define-structure perturbation-tagged-value
 primal canonical? interned? widen c:index boxed? void?)

(define-structure bundle
 primal tangent canonical? interned? widen c:index boxed? void?)

(define-structure sensitivity-tagged-value
 primal canonical? interned? widen c:index boxed? void?)

(define-structure reverse-tagged-value
 primal canonical? interned? widen c:index boxed? void?)

(define-structure tagged-pair
 tags car cdr canonical? interned? widen c:index boxed? void?)

(define-structure union values canonical? interned? widen c:index boxed? void?)

(define-structure environment-binding values value)

(define-structure if-instance v)

(define-structure function-instance v1 v2)

(define-structure widener-instance v1 v2)

;;; Variables

(define *time-buckets* #f)		; belongs in QobiScheme

(define *gensym* 0)

(define *alpha* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *error* #f)

(define *error?* #f)

(define *abstract?* #f)

(define *variables* '())

(define *backpropagator-variables* (vector #f))

(define *anf-variables* (vector #f))

(define *expressions* '())

(define *queue* '())

;;; Can better index the following six.

(define *perturbation-tagged-values* '())

(define *bundles* '())

(define *sensitivity-tagged-values* '())

(define *reverse-tagged-values* '())

(define *tagged-pairs* '())

(define *unions* '())

(define *empty-abstract-value* #f)

(define *abstract-boolean* #f)

;;; Can better index the following.

(define *c:indices* '())

;;; Parameters

(define *include-path* '())

(define *assert?* #f)

(define *wizard?* #f)

(define *flow-analysis?* #f)

(define *compile?* #f)

(define *metered?* #f)

(define *trace-primitive-procedures?* #f)

(define *trace-nonrecursive-closures?* #f)

(define *trace-recursive-closures?* #f)

(define *trace-argument/result?* #f)

(define *unabbreviate-executably?* #f)

(define *unabbreviate-transformed?* #f)

(define *unabbreviate-nonrecursive-closures?* #f)

(define *unabbreviate-recursive-closures?* #f)

(define *pp?* #f)

(define *verbose* #f)

(define *imprecise-inexacts?* #f)

(define *warnings?* #f)

(define *real-width-limit* #f)

(define *closure-width-limit* #f)

(define *perturbation-tagged-value-width-limit* #f)

(define *bundle-width-limit* #f)

(define *sensitivity-tagged-value-width-limit* #f)

(define *reverse-tagged-value-width-limit* #f)

(define *tagged-pair-width-limit* #f)

(define *closure-depth-limit* #f)

(define *backpropagator-depth-limit* #f)

(define *perturbation-tagged-value-depth-limit* #f)

(define *bundle-depth-limit* #f)

(define *sensitivity-tagged-value-depth-limit* #f)

(define *reverse-tagged-value-depth-limit* #f)

(define *tagged-pair-depth-limit* #f)

(define *memoized?* #f)

(define *expensive-checks?* #f)

(define *union* "struct")

;;; Procedures

;;; General

(define (initialize-time-buckets n)
 ;; belongs in QobiScheme
 (set! *time-buckets* (make-vector n 0)))

(define (time-bucket i thunk)
 ;; belongs in QobiScheme
 (let* ((start (clock-sample))
	(result (thunk))
	(end (clock-sample)))
  (vector-set!
   *time-buckets* i (+ (vector-ref *time-buckets* i) (- end start)))
  result))

(define (print-time-buckets)
 ;; belongs in QobiScheme
 (for-each-n (lambda (i)
	      (format #t "~a ~a~%"
		      (number->string-of-length i 4)
		      (number->string-of-length-and-precision
		       (vector-ref *time-buckets* i) 8 2)))
	     (vector-length *time-buckets*)))

(define (duplicatesp? p xs)
 ;; belongs in QobiScheme
 (and (not (null? xs))
      (or (memp p (first xs) (rest xs)) (duplicatesp? p (rest xs)))))

(define (positionp-vector p x v)
 ;; belongs in QobiScheme
 (let loop ((i 0))
  (cond ((>= i (vector-length v)) #f)
	((p x (vector-ref v i)) i)
	(else (loop (+ i 1))))))

(define (map-reduce g i f l . ls)
 ;; belongs in QobiScheme
 (let loop ((l (reverse l)) (ls (map reverse ls)) (c i))
  (if (null? l)
      c
      (loop (rest l) (map rest ls) (g (apply f (first l) (map first ls)) c)))))

(define (rest* l k) (if (zero? k) l (rest* (rest l) (- k 1))))

(define (maximal-elements <=? s)
 ;; belongs in QobiScheme
 (remove-if
  (lambda (e)
   (some (lambda (e-prime) (and (not (eq? e-prime e)) (<=? e e-prime))) s))
  s))

(define (cross-product f l1 l2)
 (map-reduce append '() (lambda (x1) (map (lambda (x2) (f x1 x2)) l2)) l1))

(define (without-abstract thunk)
 ;; needs work: To disable errors.
 (let ((abstract? *abstract?*))
  (set! *abstract?* #f)
  (let ((result (thunk)))
   (set! *abstract?* abstract?)
   result)))

(define (some-cps p l cs k)
 (if (null? l)
     (k #f cs)
     (p (first l)
	cs
	(lambda (r? cs) (if r? (k #t cs) (some-cps p (rest l) cs k))))))

(define (every-cps p l cs k)
 (if (null? l)
     (k #t cs)
     (p (first l)
	cs
	(lambda (r? cs) (if r? (every-cps p (rest l) cs k) (k #f cs))))))

(define (every2-cps p l1 l2 cs k)
 (if (null? l1)
     (k #t cs)
     (p (first l1)
	(first l2)
	cs
	(lambda (r? cs)
	 (if r? (every2-cps p (rest l1) (rest l2) cs k) (k #f cs))))))

(define (map-cps p l cs k)
 (let loop ((l l) (cs cs) (n '()))
  (if (null? l)
      (k (reverse n) cs)
      (p (first l) cs (lambda (r cs) (loop (rest l) cs (cons r n)))))))

(define (map2-cps p l1 l2 cs k)
 (let loop ((l1 l1) (l2 l2) (cs cs) (n '()))
  (if (null? l1)
      (k (reverse n) cs)
      (p (first l1)
	 (first l2)
	 cs
	 (lambda (r cs) (loop (rest l1) (rest l2) cs (cons r n)))))))

;;; Error Handing

(define (internal-error . arguments)
 (if (null? arguments)
     (panic "Internal error")
     (apply panic
	    (format #f "Internal error: ~a" (first arguments))
	    (rest arguments))))

(define (assert-internal thunk)
 (when *assert?* (unless (thunk) (internal-error))))

(define (unimplemented . arguments)
 (if (null? arguments)
     (panic "Not (yet) implemented")
     (apply panic
	    (format #f "Not (yet) implemented: ~a" (first arguments))
	    (rest arguments))))

(define (compile-time-error message . arguments)
 (apply format stderr-port message arguments)
 (newline stderr-port)
 (exit -1))

(define (compile-time-warning message . vs)
 (assert *abstract?*)
 (when *warnings?*
  (for-each (lambda (v)
	     ((if *pp?* pp write) (externalize v) stderr-port)
	     (newline stderr-port))
	    vs)
  (display "Warning: " stderr-port)
  (display message stderr-port)
  (newline stderr-port))
 (empty-abstract-value))

(define (run-time-error message . vs)
 (assert (not *abstract?*))
 (when *error?*
  (display "Nested error: " stderr-port)
  (display message stderr-port)
  (newline stderr-port)
  (display "Error: " stderr-port)
  (display *error* stderr-port)
  (newline stderr-port)
  (exit -1))
 (set! *error* message)
 (set! *error?* #t)
 (unless *abstract?*
  (format stderr-port "Stack trace~%")
  (for-each (lambda (record)
	     (display "Procedure: " stderr-port)
	     ((if *pp?* pp write) (externalize (first record)) stderr-port)
	     (newline stderr-port)
	     (display "Argument: " stderr-port)
	     ((if *pp?* pp write) (externalize (second record)) stderr-port)
	     (newline stderr-port)
	     (newline stderr-port))
	    *stack*)
  (newline stderr-port))
 (for-each (lambda (v)
	    ((if *pp?* pp write) (externalize v) stderr-port)
	    (newline stderr-port))
	   vs)
 (display "Error: " stderr-port)
 (display message stderr-port)
 (newline stderr-port)
 (exit -1))

(define (ad-error message . vs)
 (if *abstract?*
     (apply compile-time-warning (format #f message "might not be") vs)
     (apply run-time-error (format #f message "is not") vs)))

;;; Tags

(define (empty-tags) '())

(define (empty-tags? tags) (null? tags))

(define (add-tag tag tags) (cons tag tags))

(define (tagged? tag tags) (and (not (null? tags)) (eq? (first tags) tag)))

(define (remove-tag tag tags)
 (assert (tagged? tag tags))
 (rest tags))

(define (prefix-tags? tags1 tags2)
 (or (null? tags1)
     (and (not (null? tags2))
	  (eq? (first tags1) (first tags2))
	  (prefix-tags? (rest tags1) (rest tags2)))))

(define (equal-tags? tags1 tags2) (equal? tags1 tags2))

;;; Variables

(define (gensym)
 (let ((gensym *gensym*))
  (set! *gensym* (+ *gensym* 1))
  (string->uninterned-symbol
   (format #f "G~a" (number->padded-string-of-length gensym 9)))))

(define (concrete-user-variable? x)
 (and (symbol? x)
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
		     alpha
		     anf
		     backpropagator
		     perturbation
		     forward
		     sensitivity
		     reverse)))))

(define (concrete-variable? x)
 (or (concrete-user-variable? x)
     (and (list? x)
	  (= (length x) 3)
	  (eq? (first x) 'alpha)
	  (concrete-variable? (second x))
	  (integer? (third x))
	  (exact? (third x))
	  (not (negative? (third x))))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'anf)
	  (integer? (second x))
	  (exact? (second x))
	  (not (negative? (second x))))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'backpropagator)
	  (integer? (second x))
	  (exact? (second x))
	  (not (negative? (second x))))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'perturbation)
	  (concrete-variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'forward)
	  (concrete-variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'sensitivity)
	  (concrete-variable? (second x)))
     (and (list? x)
	  (= (length x) 2)
	  (eq? (first x) 'reverse)
	  (concrete-variable? (second x)))))

(define (variable-anf-max x)
 (let loop ((x (variable-name x)))
  (cond ((symbol? x) 0)
	((list? x)
	 (case (first x)
	  ((alpha) (loop (second x)))
	  ((anf) (second x))
	  ((backpropagator) 0)
	  ((perturbation forward sensitivity reverse) (loop (second x)))
	  (else (internal-error))))
	(else (internal-error)))))

(define (concrete-variable=? x1 x2)
 (assert (and (concrete-variable? x1) (concrete-variable? x2)))
 (equal? x1 x2))

(define (variable=? x1 x2)
 (assert (and (variable? x1) (variable? x2)))
 (eq? x1 x2))

(define (concrete-variable-base x)
 (if (and (list? x) (eq? (first x) 'alpha))
     (concrete-variable-base (second x))
     x))

(define (concrete-variable-alpha x)
 (if (and (list? x) (eq? (first x) 'alpha))
     (cons (third x) (concrete-variable-alpha (second x)))
     '()))

(define (base-concrete-variable<? x1 x2)
 (if (symbol? x1)
     (if (symbol? x2)
	 (string<? (symbol->string x1) (symbol->string x2))
	 #t)
     (if (symbol? x2)
	 #f
	 (if (eq? (first x1) (first x2))
	     (case (first x1)
	      ((anf backpropagator) (< (second x1) (second x2)))
	      ((perturbation forward sensitivity reverse)
	       (concrete-variable<? (second x1) (second x2)))
	      (else (internal-error)))
	     (not (not (memq (first x2)
			     (memq (first x1)
				   '(anf
				     backpropagator
				     perturbation
				     forward
				     sensitivity
				     reverse)))))))))

(define (concrete-variable<? x1 x2)
 (or (base-concrete-variable<? (concrete-variable-base x1)
			       (concrete-variable-base x2))
     (and (concrete-variable=? (concrete-variable-base x1)
			       (concrete-variable-base x2))
	  ((lexicographically<? < =)
	   (reverse (concrete-variable-alpha x1))
	   (reverse (concrete-variable-alpha x2))))))

(define (variable<? x1 x2)
 (concrete-variable<? (variable-name x1) (variable-name x2)))

(define (sort-variables xs) (sort xs variable<? identity))

(define (new-variable x)
 (assert (concrete-variable? x))
 (or (find-if (lambda (x0) (concrete-variable=? (variable-name x0) x))
	      *variables*)
     (let ((x0 (make-variable x #f #f #f #f #f #f #f #f #f)))
      (set! *variables* (cons x0 *variables*))
      x0)))

(define (anfify i)
 (if (< i (vector-length *anf-variables*))
     (or (vector-ref *anf-variables* i)
	 (let ((x (new-variable `(anf ,i))))
	  (vector-set! *anf-variables* i x)
	  x))
     (let ((anf-variables
	    (make-vector (* 2 (vector-length *anf-variables*)) #f))
	   (x (new-variable `(anf ,i))))
      (for-each-n
       (lambda (i)
	(vector-set! anf-variables i (vector-ref *anf-variables* i)))
       (vector-length *anf-variables*))
      (set! *anf-variables* anf-variables)
      (vector-set! *anf-variables* i x)
      x)))

(define (backpropagatorify i)
 (if (< i (vector-length *backpropagator-variables*))
     (or (vector-ref *backpropagator-variables* i)
	 (let ((x (new-variable `(backpropagator ,i))))
	  (vector-set! *backpropagator-variables* i x)
	  x))
     (let ((backpropagator-variables
	    (make-vector (* 2 (vector-length *backpropagator-variables*)) #f))
	   (x (new-variable `(backpropagator ,i))))
      (for-each-n
       (lambda (i)
	(vector-set!
	 backpropagator-variables i (vector-ref *backpropagator-variables* i)))
       (vector-length *backpropagator-variables*))
      (set! *backpropagator-variables* backpropagator-variables)
      (vector-set! *backpropagator-variables* i x)
      x)))

(define (perturbationify x)
 (or (variable-perturbationify x)
     (let ((x0 (new-variable `(perturbation ,(variable-name x)))))
      (set-variable-perturbationify! x x0)
      (set-variable-unperturbationify! x0 x)
      x0)))

(define (forwardify x)
 (or (variable-forwardify x)
     (let ((x0 (new-variable `(forward ,(variable-name x)))))
      (set-variable-forwardify! x x0)
      (set-variable-unforwardify! x0 x)
      x0)))

(define (sensitivityify x)
 (or (variable-sensitivityify x)
     (let ((x0 (new-variable `(sensitivity ,(variable-name x)))))
      (set-variable-sensitivityify! x x0)
      (set-variable-unsensitivityify! x0 x)
      x0)))

(define (reverseify x)
 (or (variable-reverseify x)
     (let ((x0 (new-variable `(reverse ,(variable-name x)))))
      (set-variable-reverseify! x x0)
      (set-variable-unreverseify! x0 x)
      x0)))

(define (unperturbationify x)
 (assert (variable-unperturbationify x))
 (variable-unperturbationify x))

(define (unforwardify x)
 (assert (variable-unforwardify x))
 (variable-unforwardify x))

(define (unsensitivityify? x)
 (or (variable-unsensitivityify x)
     (let loop ((x (variable-name x)))
      (and (pair? x)
	   (case (first x)
	    ;; This case needs to be this way because of the call to
	    ;; sensitivity-transform in reverse-transform-internal which is
	    ;; subsequently alpha-converted.
	    ((alpha) (loop (second x)))
	    ((anf) #f)
	    ((backpropagator) #f)
	    ((perturbation) #f)
	    ((forward) #f)
	    ((sensitivity) #t)
	    ((reverse) #f)
	    (else #f))))))

(define (unsensitivityify x)
 (or (variable-unsensitivityify x)
     (let ((x0 (new-variable
		(let loop ((x (variable-name x)))
		 (assert (pair? x))
		 (case (first x)
		  ;; This case needs to be this way because of the call to
		  ;; sensitivity-transform in reverse-transform-internal which
		  ;; is subsequently alpha-converted.
		  ((alpha) (loop (second x)))
		  ((anf) (internal-error))
		  ((backpropagator) (internal-error))
		  ((perturbation) (internal-error))
		  ((forward) (internal-error))
		  ((sensitivity) (second x))
		  ((reverse) (internal-error))
		  (else (internal-error)))))))
      (set-variable-unsensitivityify! x x0)
      x0)))

(define (unreverseify x)
 (assert (variable-unreverseify x))
 (variable-unreverseify x))

(define (sensitivity-access x)
 (new-variable-access-expression (sensitivityify x)))

(define (reverse-access x) (new-variable-access-expression (reverseify x)))

(define (perturbationify-access e)
 (new-variable-access-expression
  (perturbationify (variable-access-expression-variable e))))

(define (forwardify-access e)
 (new-variable-access-expression
  (forwardify (variable-access-expression-variable e))))

(define (sensitivityify-access e)
 (new-variable-access-expression
  (sensitivityify (variable-access-expression-variable e))))

(define (reverseify-access e)
 (new-variable-access-expression
  (reverseify (variable-access-expression-variable e))))

(define (variable-tags x)
 (let loop ((x (variable-name x)))
  (if (pair? x)
      (case (first x)
       ((alpha) (loop (second x)))
       ((anf) (empty-tags))
       ((backpropagator) (empty-tags))
       ((perturbation) (add-tag 'perturbation (loop (second x))))
       ((forward) (add-tag 'forward (loop (second x))))
       ((sensitivity) (add-tag 'sensitivity (loop (second x))))
       ((reverse) (add-tag 'reverse (loop (second x))))
       (else (internal-error)))
      (empty-tags))))

;;; Parameters

(define (parameter-tags p)
 (cond
  ;; Calling value-tags is OK because constant expression value should always
  ;; be concrete.
  ((constant-expression? p) (value-tags (constant-expression-value p)))
  ((variable-access-expression? p)
   (variable-tags (variable-access-expression-variable p)))
  ((lambda-expression? p) (lambda-expression-tags p))
  ((letrec-expression? p)
   (assert
    (and (variable-access-expression? (letrec-expression-body p))
	 (memp variable=?
	       (variable-access-expression-variable (letrec-expression-body p))
	       (letrec-expression-procedure-variables p))))
   ;; It is also possible to derive this from the tags of one of the procedure
   ;; variables.
   ;; The procedure-variables and lambda-expressions slots will be nonempty.
   (lambda-expression-tags (first (letrec-expression-lambda-expressions p))))
  ((cons-expression? p) (cons-expression-tags p))
  (else (internal-error))))

(define (lambda-expression-tags e)
 (parameter-tags (lambda-expression-parameter e)))

(define (perturbation-parameter? p) (tagged? 'perturbation (parameter-tags p)))

(define (forward-parameter? p) (tagged? 'forward (parameter-tags p)))

(define (sensitivity-parameter? p) (tagged? 'sensitivity (parameter-tags p)))

(define (reverse-parameter? p) (tagged? 'reverse (parameter-tags p)))

;;; Free variables

(define (union-variables xs1 xs2) (unionp variable=? xs1 xs2))

(define (free-variables e)
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       ((application? e) (application-free-variables e))
       ((letrec-expression? e) (letrec-expression-free-variables e))
       ((cons-expression? e) (cons-expression-free-variables e))
       (else (internal-error))))

(define (recursive-closure-free-variables xs es)
 (sort-variables
  (set-differencep
   variable=? (map-reduce union-variables '() free-variables es) xs)))

(define (letrec-expression-variables e)
 (recursive-closure-free-variables (letrec-expression-procedure-variables e)
				   (letrec-expression-lambda-expressions e)))

(define (parameter-variables p)
 (cond ((constant-expression? p) '())
       ((variable-access-expression? p)
	(list (variable-access-expression-variable p)))
       ((lambda-expression? p) (free-variables p))
       ((letrec-expression? p)
	(assert (and (variable-access-expression? (letrec-expression-body p))
		     (memp variable=?
			   (variable-access-expression-variable
			    (letrec-expression-body p))
			   (letrec-expression-procedure-variables p))))
	(letrec-expression-variables p))
       ((cons-expression? p)
	(append (parameter-variables (cons-expression-car p))
		(parameter-variables (cons-expression-cdr p))))
       (else (internal-error))))

;;; Expression constructors

(define (new-constant-expression value)
 (let ((e0 (make-constant-expression '() '() value)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-variable-access-expression variable)
 (assert (variable? variable))
 (let ((e0 (make-variable-access-expression '() '() variable)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-lambda-expression p e)
 (assert (not (duplicatesp? variable=? (parameter-variables p))))
 (let ((e0 (make-lambda-expression
	    #f
	    #f
	    #f
	    #f
	    #f
	    #f
	    #f
	    #f
	    #f
	    '()
	    '()
	    '()
	    '()
	    (sort-variables
	     (set-differencep
	      variable=? (free-variables e) (parameter-variables p)))
	    p
	    e)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-application e1 e2)
 (let ((e0 (make-application
	    '()
	    '()
	    #f
	    (sort-variables
	     (union-variables (free-variables e1) (free-variables e2)))
	    e1
	    e2)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-letrec-expression xs es e)
 (assert (and (= (length xs) (length es)) (every variable? xs)))
 (if (null? xs)
     e
     (let ((e0 (make-letrec-expression
		'()
		'()
		#f
		(sort-variables
		 (set-differencep
		  variable=?
		  (union-variables
		   (map-reduce union-variables '() free-variables es)
		   (free-variables e))
		  xs))
		xs
		es
		e)))
      (set! *expressions* (cons e0 *expressions*))
      e0)))

(define (new-cons-expression tags e1 e2)
 (let ((e0 (make-cons-expression
	    '()
	    '()
	    #f
	    (sort-variables
	     (union-variables (free-variables e1) (free-variables e2)))
	    tags
	    e1
	    e2)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

;;; Generic expression accessors and mutators

(define (expression-parents e)
 ((cond ((constant-expression? e) constant-expression-parents)
	((variable-access-expression? e) variable-access-expression-parents)
	((lambda-expression? e) lambda-expression-parents)
	((application? e) application-parents)
	((letrec-expression? e) letrec-expression-parents)
	((cons-expression? e) cons-expression-parents)
	(else (internal-error)))
  e))

(define (set-expression-parents! e es)
 ((cond
   ((constant-expression? e) set-constant-expression-parents!)
   ((variable-access-expression? e) set-variable-access-expression-parents!)
   ((lambda-expression? e) set-lambda-expression-parents!)
   ((application? e) set-application-parents!)
   ((letrec-expression? e) set-letrec-expression-parents!)
   ((cons-expression? e) set-cons-expression-parents!)
   (else (internal-error)))
  e
  es))

(define (expression-environment-bindings e)
 ((cond ((constant-expression? e) constant-expression-environment-bindings)
	((variable-access-expression? e)
	 variable-access-expression-environment-bindings)
	((lambda-expression? e) lambda-expression-environment-bindings)
	((application? e) application-environment-bindings)
	((letrec-expression? e) letrec-expression-environment-bindings)
	((cons-expression? e) cons-expression-environment-bindings)
	(else (internal-error)))
  e))

(define (set-expression-environment-bindings! e es)
 ((cond
   ((constant-expression? e) set-constant-expression-environment-bindings!)
   ((variable-access-expression? e)
    set-variable-access-expression-environment-bindings!)
   ((lambda-expression? e) set-lambda-expression-environment-bindings!)
   ((application? e) set-application-environment-bindings!)
   ((letrec-expression? e) set-letrec-expression-environment-bindings!)
   ((cons-expression? e) set-cons-expression-environment-bindings!)
   (else (internal-error)))
  e
  es))

(define (expression-enqueue? e)
 ((cond ((application? e) application-enqueue?)
	((letrec-expression? e) letrec-expression-enqueue?)
	((cons-expression? e) cons-expression-enqueue?)
	(else (internal-error)))
  e))

(define (set-expression-enqueue?! e es)
 ((cond ((application? e) set-application-enqueue?!)
	((letrec-expression? e) set-letrec-expression-enqueue?!)
	((cons-expression? e) set-cons-expression-enqueue?!)
	(else (internal-error)))
  e
  es))

;;; Derived expression constructors

(define (new-let* ps es e)
 (if (null? ps)
     e
     (new-application
      (new-lambda-expression (first ps) (new-let* (rest ps) (rest es) e))
      (first es))))

(define (create-let* bs e)
 (new-let* (map parameter-binding-parameter bs)
	   (map parameter-binding-expression bs)
	   e))

(define (reference-graph xs es e)
 ;; needs work: Should have structure instead of list.
 (list
  (map (lambda (x e) (list x (intersectionp variable=? xs (free-variables e))))
       xs
       es)
  (intersectionp variable=? xs (free-variables e))))

(define (transitive-closure arms)
 ;; needs work: Should have structure instead of list.
 (let loop ((arms arms))
  (let ((new-arms
	 (map (lambda (arm)
	       (list (first arm)
		     (union-variables
		      (second arm)
		      (map-reduce
		       union-variables
		       '()
		       (lambda (target) (second (assp variable=? target arms)))
		       (second arm)))))
	      arms)))
   (if (every (lambda (arm new-arm)
	       (set-equalq? (second arm) (second new-arm)))
	      arms
	      new-arms)
       arms
       (loop new-arms)))))

(define (strongly-connected-components arms transitive-arms)
 ;; needs work: Should have structure instead of list.
 (equivalence-classesp
  (lambda (x1 x2)
   (and (memp variable=? x1 (second (assp variable=? x2 transitive-arms)))
	(memp variable=? x2 (second (assp variable=? x1 transitive-arms)))))
  (map first arms)))

(define (lightweight-letrec-conversion xs es e)
 ;; needs work: Should have structure instead of list.
 (let* ((reference-graph (reference-graph xs es e))
	(arms (first reference-graph))
	(xs1 (second reference-graph))
	(transitive-arms (transitive-closure arms)))
  (map
   (lambda (this)
    (list
     this
     (or (not (null? (rest this)))
	 (not (not (memp variable=?
			 (first this)
			 (second (assp variable=? (first this) arms))))))))
   (topological-sort
    ;; component2 calls component1
    (lambda (component1 component2)
     (some (lambda (x2)
	    (some (lambda (x1)
		   (memp variable=?
			 x1
			 (second (assp variable=? x2 transitive-arms))))
		  component1))
	   component2))
    (remove-if-not
     (lambda (component)
      (some (lambda (x1)
	     (some (lambda (x2)
		    (or (variable=? x2 x1)
			(memp variable=?
			      x2
			      (second (assp variable=? x1 transitive-arms)))))
		   component))
	    xs1))
     (strongly-connected-components arms transitive-arms))))))

(define (create-letrec-expression xs es e)
 (let loop ((clusters (lightweight-letrec-conversion xs es e)))
  (if (null? clusters)
      e
      (let ((cluster (first clusters)))
       (if (second cluster)
	   (new-letrec-expression
	    (first cluster)
	    (map (lambda (x) (list-ref es (positionp variable=? x xs)))
		 (first cluster))
	    (loop (rest clusters)))
	   (let ((x (first (first cluster))))
	    (new-let* (list (new-variable-access-expression x))
		      (list (list-ref es (positionp variable=? x xs)))
		      (loop (rest clusters)))))))))

(define (create-cons-expression e1 e2)
 (new-cons-expression (empty-tags) e1 e2))

;;; LET*

(define (contains-letrec? e)
 (or (letrec-expression? e)
     (and (application? e)
	  (or (contains-letrec? (application-callee e))
	      (contains-letrec? (application-argument e))))
     (and (cons-expression? e)
	  (or (contains-letrec? (cons-expression-car e))
	      (contains-letrec? (cons-expression-cdr e))))))

(define (let*? e)
 ;; This is a stronger check than:
 ;;  2. No letrec nested in a let* expression or body can reference a variable
 ;;     bound by that let*.
 (and
  (application? e)
  (lambda-expression? (application-callee e))
  (and (not (contains-letrec? (lambda-expression-body (application-callee e))))
       (not (contains-letrec? (application-argument e))))))

(define (let*-parameters e)
 (if (let*? e)
     (cons (lambda-expression-parameter (application-callee e))
	   (let*-parameters (lambda-expression-body (application-callee e))))
     '()))

(define (let*-expressions e)
 (if (let*? e)
     (cons (application-argument e)
	   (let*-expressions (lambda-expression-body (application-callee e))))
     '()))

(define (let*-body e)
 (if (let*? e) (let*-body (lambda-expression-body (application-callee e))) e))

;;; Expression Equivalence

(define (expression-eqv? e1 e2)
 ;; needs work: We need to look for all implicit eq? comparisons.
 (eq? e1 e2))

(define (dereferenced-expression-eqv? e1 e2)
 ;; needs work: We need to look for all implicit eq? comparisons.
 (if (and (lambda-expression? e1) (lambda-expression? e2))
     (cond ((lambda-expression-alpha-conversion-inverse e1)
	    (dereferenced-expression-eqv?
	     (lambda-expression-alpha-conversion-inverse e1) e2))
	   ((lambda-expression-alpha-conversion-inverse e2)
	    (dereferenced-expression-eqv?
	     e1 (lambda-expression-alpha-conversion-inverse e2)))
	   ((and (lambda-expression-perturbation-transform-inverse e1)
		 (lambda-expression-perturbation-transform-inverse e2))
	    (dereferenced-expression-eqv?
	     (lambda-expression-perturbation-transform-inverse e1)
	     (lambda-expression-perturbation-transform-inverse e2)))
	   ((and (lambda-expression-forward-transform-inverse e1)
		 (lambda-expression-forward-transform-inverse e2))
	    (dereferenced-expression-eqv?
	     (lambda-expression-forward-transform-inverse e1)
	     (lambda-expression-forward-transform-inverse e2)))
	   ((and (lambda-expression-sensitivity-transform-inverse e1)
		 (lambda-expression-sensitivity-transform-inverse e2))
	    (dereferenced-expression-eqv?
	     (lambda-expression-sensitivity-transform-inverse e1)
	     (lambda-expression-sensitivity-transform-inverse e2)))
	   ((and (lambda-expression-reverse-transform-inverse e1)
		 (lambda-expression-reverse-transform-inverse e2))
	    (dereferenced-expression-eqv?
	     (lambda-expression-reverse-transform-inverse e1)
	     (lambda-expression-reverse-transform-inverse e2)))
	   (else (eq? e1 e2)))
     (eq? e1 e2)))

;;; Values

;;; Empty Lists

(define (vlad-empty-list) '())

(define (vlad-empty-list? u)
 (assert (not (union? u)))
 (null? u))

;;; Booleans

(define (vlad-true) #t)

(define (vlad-false) #f)

(define (vlad-true? u)
 (assert (not (union? u)))
 (eq? u #t))

(define (vlad-false? u)
 (assert (not (union? u)))
 (eq? u #f))

(define (vlad-boolean? u) (or (vlad-true? u) (vlad-false? u)))

;;; Reals

(define (abstract-real) 'real)

(define (abstract-real? u)
 (assert (not (union? u)))
 (eq? u 'real))

(define (vlad-real? u)
 (assert (not (union? u)))
 (or (real? u) (abstract-real? u)))

;;; Closures

(define (create-nonrecursive-closure vs e)
 (assert
  (and (= (length vs) (length (free-variables e)))
       ;; We used to enforce the constraint that the tags of the parameter of e
       ;; (as an indication of the tags of the resulting closure) were a prefix
       ;; of the tags of each v in vs. But this does not hold of the let*
       ;; bindings taken as lambda expressions for results paired with
       ;; backpropagator variables. The backpropagator variables are free in
       ;; the nested let* context context of the forward phase reverse
       ;; transformed procedure but the backpropagators are not reverse values.
       (or *abstract?*
	   (every
	    (lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	    (free-variables e)
	    vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and *abstract?*
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (free-variables e)
	    vs)))
     (empty-abstract-value)
     (make-nonrecursive-closure vs e #t #f #f #f #f 'unfilled)))

(define (new-nonrecursive-closure vs e)
 (assert
  (and (= (length vs) (length (free-variables e)))
       ;; We used to enforce the constraint that the tags of the parameter of e
       ;; (as an indication of the tags of the resulting closure) were a prefix
       ;; of the tags of each v in vs. But this does not hold of the let*
       ;; bindings taken as lambda expressions for results paired with
       ;; backpropagator variables. The backpropagator variables are free in
       ;; the nested let* context context of the forward phase reverse
       ;; transformed procedure but the backpropagators are not reverse values.
       (or *abstract?*
	   (every
	    (lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	    (free-variables e)
	    vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and *abstract?*
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (free-variables e)
	    vs)))
     (empty-abstract-value)
     (if *memoized?*
	 ;; We only index on e. We could build an index tree on the vs. By
	 ;; indexing on e, there is an implicit expession-eqv?.
	 (or (find-if (lambda (v0)
		       ;; We don't need to check the lengths because if the
		       ;; expressions are expression-eqv?, they will have the
		       ;; same free variables.
		       (abstract-environment=?
			vs (get-nonrecursive-closure-values v0)))
		      (lambda-expression-nonrecursive-closures e))
	     (let ((v0
		    (make-nonrecursive-closure vs e #t #t #f #f #f 'unfilled)))
	      (set-lambda-expression-nonrecursive-closures!
	       e (cons v0 (lambda-expression-nonrecursive-closures e)))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-nonrecursive-closure vs e #t #f #f #f #f 'unfilled))))

(define (fill-nonrecursive-closure-values! u vs)
 ;; We can't do the full checks of new-nonrecursive-closure at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert
  (and (= (length vs)
	  (length (free-variables (nonrecursive-closure-lambda-expression u))))
       (eq? (nonrecursive-closure-values u) 'unfilled)))
 (set-nonrecursive-closure-values! u vs))

(define (get-nonrecursive-closure-values v)
 (assert (not (eq? (nonrecursive-closure-values v) 'unfilled)))
 (nonrecursive-closure-values v))

(define (create-recursive-closure vs xs es i)
 (assert
  (and
   (= (length vs)
      (length (recursive-closure-free-variables
	       (vector->list xs) (vector->list es))))
   ;; See the note in new-nonrecursive-closure. While that hasn't happened in
   ;; practise, and I don't know whether it can, I removed it in principle.
   (or *abstract?*
       (every
	(lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	(recursive-closure-free-variables (vector->list xs) (vector->list es))
	vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and *abstract?*
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (recursive-closure-free-variables
	     (vector->list xs) (vector->list es))
	    vs)))
     (empty-abstract-value)
     (make-recursive-closure vs xs es i #t #f #f #f #f 'unfilled)))

(define (new-recursive-closure vs xs es i)
 (assert
  (and
   (= (length vs)
      (length (recursive-closure-free-variables
	       (vector->list xs) (vector->list es))))
   ;; See the note in new-nonrecursive-closure. While that hasn't happened in
   ;; practise, and I don't know whether it can, I removed it in principle.
   (or *abstract?*
       (every
	(lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	(recursive-closure-free-variables (vector->list xs) (vector->list es))
	vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and *abstract?*
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (recursive-closure-free-variables
	     (vector->list xs) (vector->list es))
	    vs)))
     (empty-abstract-value)
     (if *memoized?*
	 ;; We only index on the first e. Since an e uniquely determines the
	 ;; letrec, we don't need to index by or even check the other es or the
	 ;; xs. We could index on i and build an index tree on the vs. By
	 ;; indexing on the first e, there is an implicit expession-eqv?.
	 (or (find-if
	      (lambda (v0)
	       (and
		(= i (recursive-closure-index v0))
		;; We don't need to check the lengths because if the letrec
		;; expressions are expression-eqv?, they will have the same
		;; free variables.
		(abstract-environment=? vs (get-recursive-closure-values v0))))
	      (lambda-expression-recursive-closures (vector-ref es 0)))
	     (let ((v0 (make-recursive-closure
			vs xs es i #t #t #f #f #f 'unfilled)))
	      (set-lambda-expression-recursive-closures!
	       (vector-ref es 0)
	       (cons
		v0 (lambda-expression-recursive-closures (vector-ref es 0))))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-recursive-closure vs xs es i #t #f #f #f #f 'unfilled))))

(define (fill-recursive-closure-values! u vs)
 ;; We can't do the full checks of new-recursive-closure at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert (and (= (length vs) (length (recursive-closure-variables u)))
	      (eq? (recursive-closure-values u) 'unfilled)))
 (set-recursive-closure-values! u vs))

(define (get-recursive-closure-values v)
 (assert (not (eq? (recursive-closure-values v) 'unfilled)))
 (recursive-closure-values v))

(define (nonrecursive-closure-match? u1 u2)
 (assert (and (not (union? u1)) (not (union? u2))))
 ;; The first condition is an optimization.
 (and (= (length (get-nonrecursive-closure-values u1))
	 (length (get-nonrecursive-closure-values u2)))
      (expression-eqv? (nonrecursive-closure-lambda-expression u1)
		       (nonrecursive-closure-lambda-expression u2))))

(define (dereferenced-nonrecursive-closure-match? u1 u2)
 (assert (and (not (union? u1)) (not (union? u2))))
 ;; The first condition is an optimization.
 (and (= (length (get-nonrecursive-closure-values u1))
	 (length (get-nonrecursive-closure-values u2)))
      (dereferenced-expression-eqv?
       (nonrecursive-closure-lambda-expression u1)
       (nonrecursive-closure-lambda-expression u2))))

(define (recursive-closure-match? u1 u2)
 (assert (and (not (union? u1)) (not (union? u2))))
 (and (= (recursive-closure-index u1) (recursive-closure-index u2))
      (= (vector-length (recursive-closure-procedure-variables u1))
	 (vector-length (recursive-closure-procedure-variables u2)))
      (= (vector-length (recursive-closure-lambda-expressions u1))
	 (vector-length (recursive-closure-lambda-expressions u2)))
      ;; This is an optimization.
      (= (length (get-recursive-closure-values u1))
	 (length (get-recursive-closure-values u2)))
      (every-vector expression-eqv?
		    (recursive-closure-lambda-expressions u1)
		    (recursive-closure-lambda-expressions u2))))

(define (dereferenced-recursive-closure-match? u1 u2)
 (assert (and (not (union? u1)) (not (union? u2))))
 (and (= (recursive-closure-index u1) (recursive-closure-index u2))
      (= (vector-length (recursive-closure-procedure-variables u1))
	 (vector-length (recursive-closure-procedure-variables u2)))
      (= (vector-length (recursive-closure-lambda-expressions u1))
	 (vector-length (recursive-closure-lambda-expressions u2)))
      ;; This is an optimization.
      (= (length (get-recursive-closure-values u1))
	 (length (get-recursive-closure-values u2)))
      (every-vector dereferenced-expression-eqv?
		    (recursive-closure-lambda-expressions u1)
		    (recursive-closure-lambda-expressions u2))))

(define (closure? u)
 (assert (not (union? u)))
 (or (nonrecursive-closure? u) (recursive-closure? u)))

(define (closure-match? u1 u2)
 (assert (and (closure? u1) (closure? u2)))
 (or (and (nonrecursive-closure? u1)
	  (nonrecursive-closure? u2)
	  (nonrecursive-closure-match? u1 u2))
     (and (recursive-closure? u1)
	  (recursive-closure? u2)
	  (recursive-closure-match? u1 u2))))

(define (nonrecursive-closure-variables u)
 (assert (not (union? u)))
 (free-variables (nonrecursive-closure-lambda-expression u)))

(define (recursive-closure-variables u)
 (assert (not (union? u)))
 (recursive-closure-free-variables
  (vector->list (recursive-closure-procedure-variables u))
  (vector->list (recursive-closure-lambda-expressions u))))

(define (closure-variables u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-variables u))
       ((recursive-closure? u) (recursive-closure-variables u))
       (else (internal-error))))

(define (nonrecursive-closure-parameter u)
 (assert (not (union? u)))
 (lambda-expression-parameter (nonrecursive-closure-lambda-expression u)))

(define (recursive-closure-parameter u)
 (assert (not (union? u)))
 (lambda-expression-parameter
  (vector-ref (recursive-closure-lambda-expressions u)
	      (recursive-closure-index u))))

(define (closure-parameter u)
 (cond ((nonrecursive-closure? u) (nonrecursive-closure-parameter u))
       ((recursive-closure? u) (recursive-closure-parameter u))
       (else (internal-error))))

(define (nonrecursive-closure-tags u)
 (assert (not (union? u)))
 (parameter-tags (nonrecursive-closure-parameter u)))

(define (recursive-closure-tags u)
 (assert (not (union? u)))
 (parameter-tags (recursive-closure-parameter u)))

(define (closure-body u)
 (lambda-expression-body
  (cond ((nonrecursive-closure? u) (nonrecursive-closure-lambda-expression u))
	((recursive-closure? u)
	 (vector-ref (recursive-closure-lambda-expressions u)
		     (recursive-closure-index u)))
	(else (internal-error)))))

(define (vlad-procedure? u)
 (assert (not (union? u)))
 (or (primitive-procedure? u) (closure? u)))

;;; Perturbation Tagged Values

(define (create-perturbation-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (make-perturbation-tagged-value v #t #f #f #f #f 'unfilled)))

(define (new-perturbation-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *memoized?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-perturbation-tagged-value-primal v0)))
	      *perturbation-tagged-values*)
	     (let ((v0 (make-perturbation-tagged-value
			v #t #t #f #f #f 'unfilled)))
	      (set! *perturbation-tagged-values*
		    (cons v0 *perturbation-tagged-values*))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-perturbation-tagged-value v #t #f #f #f #f 'unfilled))))

(define (fill-perturbation-tagged-value-primal! u v)
 ;; We can't do the full checks of new-perturbation-tagged-value at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert (eq? (perturbation-tagged-value-primal u) 'unfilled))
 (set-perturbation-tagged-value-primal! u v))

(define (get-perturbation-tagged-value-primal v)
 (assert (not (eq? (perturbation-tagged-value-primal v) 'unfilled)))
 (perturbation-tagged-value-primal v))

;;; Bundles

(define (some-bundlable? v v-perturbation)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  0
  (let loop ((v v)
	     (v-perturbation v-perturbation)
	     (cs '())
	     (k (lambda (r? cs) r?)))
   (let ((found?
	  (find-if
	   (lambda (c)
	    (and (eq? (car (car c)) v) (eq? (cdr (car c)) v-perturbation)))
	   cs)))
    (if found?
	(k (cdr found?) cs)
	;; needs work: What is the circular value?
	(let* ((c (cons (cons v v-perturbation) #f))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ((union? v)
	   (some-cps (lambda (u cs k) (loop u v-perturbation cs k))
		     (union-members v)
		     cs
		     k))
	  ((union? v-perturbation)
	   (some-cps (lambda (u-perturbation cs k) (loop v u-perturbation cs k))
		     (union-members v-perturbation)
		     cs
		     k))
	  ((or
	    (and (vlad-empty-list? v)
		 (perturbation-tagged-value? v-perturbation)
		 (some vlad-empty-list?
		       (union-members
			(get-perturbation-tagged-value-primal v-perturbation))))
	    (and (vlad-true? v)
		 (perturbation-tagged-value? v-perturbation)
		 (some vlad-true?
		       (union-members
			(get-perturbation-tagged-value-primal v-perturbation))))
	    (and (vlad-false? v)
		 (perturbation-tagged-value? v-perturbation)
		 (some vlad-false?
		       (union-members
			(get-perturbation-tagged-value-primal v-perturbation))))
	    (and (vlad-real? v)
		 (perturbation-tagged-value? v-perturbation)
		 (some vlad-real?
		       (union-members
			(get-perturbation-tagged-value-primal v-perturbation))))
	    (and
	     (primitive-procedure? v)
	     (perturbation-tagged-value? v-perturbation)
	     (some (lambda (u) (and (primitive-procedure? u) (eq? v u)))
		   (union-members
		    (get-perturbation-tagged-value-primal v-perturbation)))))
	   (k #t cs))
	  ((and (perturbation-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (some-cps (lambda (u cs k)
		      (if (perturbation-tagged-value? u)
			  (loop (get-perturbation-tagged-value-primal v)
				(create-perturbation-tagged-value
				 (get-perturbation-tagged-value-primal u))
				cs
				k)
			  (k #f cs)))
		     (union-members
		      (get-perturbation-tagged-value-primal v-perturbation))
		     cs
		     k))
	  ((and (bundle? v) (perturbation-tagged-value? v-perturbation))
	   (some-cps
	    (lambda (u cs k)
	     (if (bundle? u)
		 (loop (get-bundle-primal v)
		       (create-perturbation-tagged-value (get-bundle-primal u))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (get-bundle-tangent v)
				  (create-perturbation-tagged-value
				   (get-bundle-tangent u))
				  cs
				  k)
			    (k #f cs))))
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (sensitivity-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (some-cps (lambda (u cs k)
		      (if (sensitivity-tagged-value? u)
			  (loop (get-sensitivity-tagged-value-primal v)
				(create-perturbation-tagged-value
				 (get-sensitivity-tagged-value-primal u))
				cs
				k)
			  (k #f cs)))
		     (union-members
		      (get-perturbation-tagged-value-primal v-perturbation))
		     cs
		     k))
	  ((and (reverse-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (some-cps (lambda (u cs k)
		      (if (reverse-tagged-value? u)
			  (loop (get-reverse-tagged-value-primal v)
				(create-perturbation-tagged-value
				 (get-reverse-tagged-value-primal u))
				cs
				k)
			  (k #f cs)))
		     (union-members
		      (get-perturbation-tagged-value-primal v-perturbation))
		     cs
		     k))
	  (else (k #f cs)))))))))

(define (every-bundlable? v v-perturbation)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  1
  (let loop ((v v)
	     (v-perturbation v-perturbation)
	     (cs '())
	     (k (lambda (r? cs) r?)))
   (let ((found?
	  (find-if
	   (lambda (c)
	    (and (eq? (car (car c)) v) (eq? (cdr (car c)) v-perturbation)))
	   cs)))
    (if found?
	(k (cdr found?) cs)
	;; needs work: What is the circular value?
	(let* ((c (cons (cons v v-perturbation) #t))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ((union? v)
	   (every-cps (lambda (u cs k) (loop u v-perturbation cs k))
		      (union-members v)
		      cs
		      k))
	  ((union? v-perturbation)
	   (every-cps
	    (lambda (u-perturbation cs k) (loop v u-perturbation cs k))
	    (union-members v-perturbation)
	    cs
	    k))
	  ((or
	    (and
	     (vlad-empty-list? v)
	     (perturbation-tagged-value? v-perturbation)
	     (every vlad-empty-list?
		    (union-members
		     (get-perturbation-tagged-value-primal v-perturbation))))
	    (and
	     (vlad-true? v)
	     (perturbation-tagged-value? v-perturbation)
	     (every vlad-true?
		    (union-members
		     (get-perturbation-tagged-value-primal v-perturbation))))
	    (and
	     (vlad-false? v)
	     (perturbation-tagged-value? v-perturbation)
	     (every vlad-false?
		    (union-members
		     (get-perturbation-tagged-value-primal v-perturbation))))
	    (and
	     (vlad-real? v)
	     (perturbation-tagged-value? v-perturbation)
	     (every vlad-real?
		    (union-members
		     (get-perturbation-tagged-value-primal v-perturbation))))
	    (and
	     (primitive-procedure? v)
	     (perturbation-tagged-value? v-perturbation)
	     (every (lambda (u) (and (primitive-procedure? u) (eq? v u)))
		    (union-members
		     (get-perturbation-tagged-value-primal v-perturbation)))))
	   (k #t cs))
	  ((and (perturbation-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (every-cps (lambda (u cs k)
		       (if (perturbation-tagged-value? u)
			   (loop (get-perturbation-tagged-value-primal v)
				 (create-perturbation-tagged-value
				  (get-perturbation-tagged-value-primal u))
				 cs
				 k)
			   (k #f cs)))
		      (union-members
		       (get-perturbation-tagged-value-primal v-perturbation))
		      cs
		      k))
	  ((and (bundle? v) (perturbation-tagged-value? v-perturbation))
	   (every-cps
	    (lambda (u cs k)
	     (if (bundle? u)
		 (loop (get-bundle-primal v)
		       (create-perturbation-tagged-value (get-bundle-primal u))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (get-bundle-tangent v)
				  (create-perturbation-tagged-value
				   (get-bundle-tangent u))
				  cs
				  k)
			    (k #f cs))))
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (sensitivity-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (every-cps (lambda (u cs k)
		       (if (sensitivity-tagged-value? u)
			   (loop (get-sensitivity-tagged-value-primal v)
				 (create-perturbation-tagged-value
				  (get-sensitivity-tagged-value-primal u))
				 cs
				 k)
			   (k #f cs)))
		      (union-members
		       (get-perturbation-tagged-value-primal v-perturbation))
		      cs
		      k))
	  ((and (reverse-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (every-cps (lambda (u cs k)
		       (if (reverse-tagged-value? u)
			   (loop (get-reverse-tagged-value-primal v)
				 (create-perturbation-tagged-value
				  (get-reverse-tagged-value-primal u))
				 cs
				 k)
			   (k #f cs)))
		      (union-members
		       (get-perturbation-tagged-value-primal v-perturbation))
		      cs
		      k))
	  (else (k #f cs)))))))))

(define (create-bundle v v-perturbation)
 (assert (or *abstract?* (some-bundlable? v v-perturbation)))
 (if (or (empty-abstract-value? v)
	 (empty-abstract-value? v-perturbation)
	 (and *abstract?* (not (some-bundlable? v v-perturbation))))
     (empty-abstract-value)
     (make-bundle v v-perturbation #t #f #f #f #f 'unfilled)))

(define (new-bundle v v-perturbation)
 (assert (or *abstract?* (some-bundlable? v v-perturbation)))
 (if (or (empty-abstract-value? v)
	 (empty-abstract-value? v-perturbation)
	 (and *abstract?* (not (some-bundlable? v v-perturbation))))
     (empty-abstract-value)
     (if *memoized?*
	 (or (find-if
	      (lambda (v0)
	       (and (abstract-value=? v (get-bundle-primal v0))
		    (abstract-value=? v-perturbation (get-bundle-tangent v0))))
	      *bundles*)
	     (let ((v0
		    (make-bundle v v-perturbation #t #t #f #f #f 'unfilled)))
	      (set! *bundles* (cons v0 *bundles*))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-bundle v v-perturbation #t #f #f #f #f 'unfilled))))

(define (fill-bundle! u v v-perturbation)
 ;; We can't do the full checks of new-bundle at this point because there may
 ;; be residual unfilled slots so the checks are delayed until
 ;; canonize-abstract-value.
 (assert (and (eq? (bundle-primal u) 'unfilled)
	      (eq? (bundle-tangent u) 'unfilled)))
 (set-bundle-primal! u v)
 (set-bundle-tangent! u v-perturbation))

(define (get-bundle-primal v)
 (assert (and (not (eq? (bundle-primal v) 'unfilled))
	      (not (eq? (bundle-tangent v) 'unfilled))))
 (bundle-primal v))

(define (get-bundle-tangent v)
 (assert (and (not (eq? (bundle-primal v) 'unfilled))
	      (not (eq? (bundle-tangent v) 'unfilled))))
 (bundle-tangent v))

;;; Sensitivity Tagged Values

(define (create-sensitivity-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (make-sensitivity-tagged-value v #t #f #f #f #f 'unfilled)))

(define (new-sensitivity-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *memoized?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-sensitivity-tagged-value-primal v0)))
	      *sensitivity-tagged-values*)
	     (let ((v0 (make-sensitivity-tagged-value
			v #t #t #f #f #f 'unfilled)))
	      (set! *sensitivity-tagged-values*
		    (cons v0 *sensitivity-tagged-values*))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-sensitivity-tagged-value v #t #f #f #f #f 'unfilled))))

(define (fill-sensitivity-tagged-value-primal! u v)
 ;; We can't do the full checks of new-sensitivity-tagged-value at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert (eq? (sensitivity-tagged-value-primal u) 'unfilled))
 (set-sensitivity-tagged-value-primal! u v))

(define (get-sensitivity-tagged-value-primal v)
 (assert (not (eq? (sensitivity-tagged-value-primal v) 'unfilled)))
 (sensitivity-tagged-value-primal v))

;;; Reverse Tagged Values

(define (create-reverse-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (make-reverse-tagged-value v #t #f #f #f #f 'unfilled)))

(define (new-reverse-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *memoized?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-reverse-tagged-value-primal v0)))
	      *reverse-tagged-values*)
	     (let ((v0
		    (make-reverse-tagged-value v #t #t #f #f #f 'unfilled)))
	      (set! *reverse-tagged-values* (cons v0 *reverse-tagged-values*))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-reverse-tagged-value v #t #f #f #f #f 'unfilled))))

(define (fill-reverse-tagged-value-primal! u v)
 ;; We can't do the full checks of new-reverse-tagged-value at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert (eq? (reverse-tagged-value-primal u) 'unfilled))
 (set-reverse-tagged-value-primal! u v))

(define (get-reverse-tagged-value-primal v)
 (assert (not (eq? (reverse-tagged-value-primal v) 'unfilled)))
 (reverse-tagged-value-primal v))

;;; Pairs

(define (create-tagged-pair tags v1 v2)
 (assert (or *abstract?*
	     (and (prefix-tags? tags (value-tags v1))
		  (prefix-tags? tags (value-tags v2)))))
 (if (or
      (empty-abstract-value? v1)
      (empty-abstract-value? v2)
      (and
       *abstract?*
       (or (every-value-tags (lambda (tags) (not (prefix-tags? tags tags))) v1)
	   (every-value-tags (lambda (tags) (not (prefix-tags? tags tags)))
			     v2))))
     (empty-abstract-value)
     (make-tagged-pair tags v1 v2 #t #f #f #f #f 'unfilled)))

(define (new-tagged-pair tags v1 v2)
 (assert (or *abstract?*
	     (and (prefix-tags? tags (value-tags v1))
		  (prefix-tags? tags (value-tags v2)))))
 (if (or
      (empty-abstract-value? v1)
      (empty-abstract-value? v2)
      (and
       *abstract?*
       (or (every-value-tags (lambda (tags) (not (prefix-tags? tags tags))) v1)
	   (every-value-tags (lambda (tags) (not (prefix-tags? tags tags)))
			     v2))))
     (empty-abstract-value)
     (if *memoized?*
	 (or (find-if (lambda (v0)
		       (and (abstract-value=? v1 (get-tagged-pair-car v0))
			    (abstract-value=? v2 (get-tagged-pair-cdr v0))
			    (equal-tags? tags (tagged-pair-tags v0))))
		      *tagged-pairs*)
	     (let ((v0 (make-tagged-pair tags v1 v2 #t #t #f #f #f 'unfilled)))
	      (set! *tagged-pairs* (cons v0 *tagged-pairs*))
	      (when *expensive-checks?* (check-abstract-value! v0))
	      v0))
	 (make-tagged-pair tags v1 v2 #t #f #f #f #f 'unfilled))))

(define (fill-tagged-pair! u v1 v2)
 ;; We can't do the full checks of new-tagged-pair at this point because there
 ;; may be residual unfilled slots so the checks are delayed until
 ;; canonize-abstract-value.
 (assert (and (eq? (tagged-pair-car u) 'unfilled)
	      (eq? (tagged-pair-cdr u) 'unfilled)))
 (set-tagged-pair-car! u v1)
 (set-tagged-pair-cdr! u v2))

(define (get-tagged-pair-car v)
 (assert (and (not (eq? (tagged-pair-car v) 'unfilled))
	      (not (eq? (tagged-pair-cdr v) 'unfilled))))
 (tagged-pair-car v))

(define (get-tagged-pair-cdr v)
 (assert (and (not (eq? (tagged-pair-car v) 'unfilled))
	      (not (eq? (tagged-pair-cdr v) 'unfilled))))
 (tagged-pair-cdr v))

(define (vlad-pair? u)
 (assert (not (union? u)))
 (and (tagged-pair? u) (empty-tags? (tagged-pair-tags u))))

(define (vlad-car u)
 (assert (vlad-pair? u))
 (get-tagged-pair-car u))

(define (vlad-cdr u)
 (assert (vlad-pair? u))
 (get-tagged-pair-cdr u))

(define (vlad-cons v1 v2) (new-tagged-pair (empty-tags) v1 v2))

;;; Unions

(define (empty-abstract-value) *empty-abstract-value*)

(define (empty-abstract-value? v) (null? (union-members v)))

(define (abstract-boolean) *abstract-boolean*)

(define (union-members v)
 (if (union? v)
     (map-reduce append '() union-members (get-union-values v))
     (list v)))

(define (create-union vs) (make-union vs #f #f #f #f #f 'unfilled))

(define (new-union vs)
 (if *memoized?*
     (or (find-if
	  (lambda (v0) (set-equalp? abstract-value=? vs (get-union-values v0)))
	  *unions*)
	 (let ((v0 (make-union vs #f #t #f #f #f 'unfilled)))
	  (set! *unions* (cons v0 *unions*))
	  (when *expensive-checks?* (check-abstract-value! v0))
	  v0))
     (make-union vs #f #f #f #f #f 'unfilled)))

(define (fill-union-values! v vs)
 (assert (and (not (memq v vs)) (eq? (union-values v) 'unfilled)))
 (set-union-values! v vs))

(define (get-union-values v)
 (assert (not (eq? (union-values v) 'unfilled)))
 (union-values v))

(define (unionize vs) (reduce abstract-value-union vs (empty-abstract-value)))

(define (map-union f v) (unionize (map f (union-members v))))

(define (cross-union f v1 v2)
 (unionize (cross-product f (union-members v1) (union-members v2))))

;;; Generic

(define (perturbation-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (perturbation-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (perturbation-parameter? (recursive-closure-parameter u)))
     (perturbation-tagged-value? u)
     (and (tagged-pair? u) (tagged? 'perturbation (tagged-pair-tags u)))))

(define (forward-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (forward-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (forward-parameter? (recursive-closure-parameter u)))
     (bundle? u)
     (and (tagged-pair? u) (tagged? 'forward (tagged-pair-tags u)))))

(define (sensitivity-value? u)
 ;; Backpropagators will be considered as sensitivity values. But you can't
 ;; unsensitize them. You need to invoke backpropagators so we can't prohibit
 ;; invocation of sensitivity-tagged procedures. Perhaps we could/should
 ;; prohibit invocation of perturbation-tagged procedures.
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (sensitivity-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (sensitivity-parameter? (recursive-closure-parameter u)))
     (sensitivity-tagged-value? u)
     (and (tagged-pair? u) (tagged? 'sensitivity (tagged-pair-tags u)))))

(define (reverse-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (reverse-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (reverse-parameter? (recursive-closure-parameter u)))
     (reverse-tagged-value? u)
     (and (tagged-pair? u) (tagged? 'reverse (tagged-pair-tags u)))))

(define (scalar-value? u)
 (assert (not (union? u)))
 (or (vlad-boolean? u)
     (vlad-empty-list? u)
     (vlad-real? u)
     (primitive-procedure? u)))

(define (aggregate-value-values u)
 (cond
  ((nonrecursive-closure? u) (get-nonrecursive-closure-values u))
  ((recursive-closure? u) (get-recursive-closure-values u))
  ((perturbation-tagged-value? u)
   (list (get-perturbation-tagged-value-primal u)))
  ((bundle? u) (list (get-bundle-primal u) (get-bundle-tangent u)))
  ((sensitivity-tagged-value? u)
   (list (get-sensitivity-tagged-value-primal u)))
  ((reverse-tagged-value? u) (list (get-reverse-tagged-value-primal u)))
  ((tagged-pair? u) (list (get-tagged-pair-car u) (get-tagged-pair-cdr u)))
  (else (internal-error))))

(define (create-aggregate-value-with-new-values u vs)
 (cond
  ((nonrecursive-closure? u)
   (create-nonrecursive-closure vs (nonrecursive-closure-lambda-expression u)))
  ((recursive-closure? u)
   (create-recursive-closure vs
			     (recursive-closure-procedure-variables u)
			     (recursive-closure-lambda-expressions u)
			     (recursive-closure-index u)))
  ((perturbation-tagged-value? u)
   (assert (= (length vs) 1))
   (create-perturbation-tagged-value (first vs)))
  ((bundle? u)
   (assert (= (length vs) 2))
   (create-bundle (first vs) (second vs)))
  ((sensitivity-tagged-value? u)
   (assert (= (length vs) 1))
   (create-sensitivity-tagged-value (first vs)))
  ((reverse-tagged-value? u)
   (assert (= (length vs) 1))
   (create-reverse-tagged-value (first vs)))
  ((tagged-pair? u)
   (assert (= (length vs) 2))
   (create-tagged-pair (tagged-pair-tags u) (first vs) (second vs)))
  (else (internal-error))))

(define (value-tags u)
 (assert (not (union? u)))
 (cond
  ((scalar-value? u) '())
  ((nonrecursive-closure? u) (nonrecursive-closure-tags u))
  ((recursive-closure? u) (recursive-closure-tags u))
  ((perturbation-tagged-value? u)
   (add-tag 'perturbation
	    (value-tags (get-perturbation-tagged-value-primal u))))
  ((bundle? u) (add-tag 'forward (value-tags (get-bundle-primal u))))
  ((sensitivity-tagged-value? u)
   (add-tag 'sensitivity
	    (value-tags (get-sensitivity-tagged-value-primal u))))
  ((reverse-tagged-value? u)
   (add-tag 'reverse (value-tags (get-reverse-tagged-value-primal u))))
  ((tagged-pair? u) (tagged-pair-tags u))
  (else (internal-error))))

(define (some-value-tags p v)
 (let loop ((tags '()) (v v) (vs '()))
  (cond
   ;; needs work: I'm not sure that this is sound.
   ((memq v vs) #t)
   ((union? v) (some (lambda (u) (loop tags u (cons v vs))) (union-members v)))
   ((scalar-value? v) (p (reverse tags)))
   ((nonrecursive-closure? v)
    (p (append (reverse tags) (nonrecursive-closure-tags v))))
   ((recursive-closure? v)
    (p (append (reverse tags) (recursive-closure-tags v))))
   ((perturbation-tagged-value? v)
    (loop (cons 'perturbation tags)
	  (get-perturbation-tagged-value-primal v) vs))
   ((bundle? v) (loop (cons 'forward tags) (get-bundle-primal v) vs))
   ((sensitivity-tagged-value? v)
    (loop (cons 'sensitivity tags) (get-sensitivity-tagged-value-primal v) vs))
   ((reverse-tagged-value? v)
    (loop (cons 'reverse tags) (get-reverse-tagged-value-primal v) vs))
   ((tagged-pair? v) (p (append (reverse tags) (tagged-pair-tags v))))
   (else (internal-error)))))

(define (every-value-tags p v)
 (let loop ((tags '()) (v v) (vs '()))
  (cond
   ;; needs work: I'm not sure that this is sound.
   ((memq v vs) #f)
   ((union? v)
    (every (lambda (u) (loop tags u (cons v vs))) (union-members v)))
   ((scalar-value? v) (p (reverse tags)))
   ((nonrecursive-closure? v)
    (p (append (reverse tags) (nonrecursive-closure-tags v))))
   ((recursive-closure? v)
    (p (append (reverse tags) (recursive-closure-tags v))))
   ((perturbation-tagged-value? v)
    (loop (cons 'perturbation tags)
	  (get-perturbation-tagged-value-primal v) vs))
   ((bundle? v) (loop (cons 'forward tags) (get-bundle-primal v) vs))
   ((sensitivity-tagged-value? v)
    (loop (cons 'sensitivity tags) (get-sensitivity-tagged-value-primal v) vs))
   ((reverse-tagged-value? v)
    (loop (cons 'reverse tags) (get-reverse-tagged-value-primal v) vs))
   ((tagged-pair? v) (p (append (reverse tags) (tagged-pair-tags v))))
   (else (internal-error)))))

;;; Abstract Value Subset, Equivalence, Nondisjointness, Union, Canonization,
;;; and Internment

(define (abstract-value-subset? v1 v2)
 ;; I used to think that abstract value subset and equality is undecidable (by
 ;; reduction from context-free-grammar equivalence and that it is
 ;; semidecidable since a lone element in the extension of the left argument
 ;; that is not in the extension of the right argument witnesses nonsubset and
 ;; the extension of an abstract value is recursively enumerable.) But now I
 ;; realize that we are asking about the trees generated by a grammar, not the
 ;; strings, i.e. strong equivalence, not weak equivalence. And I don't know
 ;; whether this is decidable. We conservatively approximate these. A #t result
 ;; is precise. The lone cause of imprecision is illustrated by the following
 ;; example. Let v1={box({0,1})} and v2={box({0}),box({1})}. v1 is a subset of
 ;; v2. Yet the procedure checks whether for every u1 in v1 there is some u2 in
 ;; v2 such that u1 is a subset of v2. This does not hold in this example
 ;; because there is no single u2 which box({0,1}) is a subset of. One can get
 ;; more precision by multiplying out v1. In this case, multiplying out v1 to
 ;; {box({0}),box({1})} whould allow every u1 to have a single u2 for which u1
 ;; is a subset of u2. Thus in this case, multiplying out would yield a precise
 ;; result. In principle, one only need multiply out v1. But if v1 has
 ;; recursion, there is no bound on the amount of multiplying out that may be
 ;; needed.
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  2
  (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (r? cs) r?)))
   (let ((found?
	  (find-if
	   (lambda (c) (and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
	   cs)))
    (if found?
	(k (cdr found?) cs)
	;; needs work: What is the circular value?
	(let* ((c (cons (cons v1 v2) #t))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ;; This is an optimization.
	  ((eq? v1 v2) (k #t cs))
	  ((union? v1)
	   (every-cps
	    (lambda (u1 cs k) (loop u1 v2 cs k)) (union-members v1) cs k))
	  ((union? v2)
	   (some-cps
	    (lambda (u2 cs k) (loop v1 u2 cs k)) (union-members v2) cs k))
	  ((or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
	       (and (vlad-true? v1) (vlad-true? v2))
	       (and (vlad-false? v1) (vlad-false? v2))
	       (and (vlad-real? v1)
		    (vlad-real? v2)
		    ;; This was = but then it equates exact values with inexact
		    ;; values and this breaks -imprecise-inexacts.
		    (or (and (real? v1) (real? v2) (equal? v1 v2))
			(and (real? v1) (abstract-real? v2))
			(and (abstract-real? v1) (abstract-real? v2))))
	       (and (primitive-procedure? v1)
		    (primitive-procedure? v2)
		    (eq? v1 v2)))
	   (k #t cs))
	  ((and (nonrecursive-closure? v1)
		(nonrecursive-closure? v2)
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	   (loop (get-perturbation-tagged-value-primal v1)
		 (get-perturbation-tagged-value-primal v2)
		 cs
		 k))
	  ((and (bundle? v1) (bundle? v2))
	   (loop (get-bundle-primal v1)
		 (get-bundle-primal v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-bundle-tangent v1)
			    (get-bundle-tangent v2)
			    cs
			    k)
		      (k #f cs)))))
	  ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	   (loop (get-sensitivity-tagged-value-primal v1)
		 (get-sensitivity-tagged-value-primal v2)
		 cs
		 k))
	  ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	   (loop (get-reverse-tagged-value-primal v1)
		 (get-reverse-tagged-value-primal v2)
		 cs
		 k))
	  ((and (tagged-pair? v1)
		(tagged-pair? v2)
		(equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
	   (loop (get-tagged-pair-car v1)
		 (get-tagged-pair-car v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-tagged-pair-cdr v1)
			    (get-tagged-pair-cdr v2)
			    cs
			    k)
		      (k #f cs)))))
	  (else (k #f cs)))))))))

(define (deep-abstract-value=? v1 v2)
 (and (abstract-value-subset? v1 v2) (abstract-value-subset? v2 v1)))

(define (abstract-value=? v1 v2)
 (if *memoized?*
     ;; This works because vlad-empty-list is (), vlad-true is #t, vlad-false
     ;; is #f, abstract-real is real, and all other non-concrete-real values
     ;; are structures. All of these are comparable with eq?.
     (begin
      (when *expensive-checks?*
       (check-abstract-value! v1)
       (check-abstract-value! v2)
       (assert (eq? (or (eq? v1 v2) (and (real? v1) (real? v2) (equal? v1 v2)))
		    (deep-abstract-value=? v1 v2))))
      (or (eq? v1 v2) (and (real? v1) (real? v2) (equal? v1 v2))))
     (deep-abstract-value=? v1 v2)))

(define (abstract-value-nondisjoint? v1 v2)
 ;; I used to think that determining whether two abstract values are
 ;; nondisjoint is undecidable (by reduction from nonempty interesection of
 ;; two context-free grammars, which is semidecidable since a lone element in
 ;; the extension of both arguments witnesses nondisjointness and the
 ;; extension of an abstract value is enumerable.) But now I realize that we
 ;; are asking about the trees generated by a grammar, not the strings, i.e.
 ;; strong equivalence, not weak equivalence. And I believe that determining
 ;; whether the set of trees generated by two context-free grammars is
 ;; nondisjoint is decidable. And I believe that this algorithm is precise.
 ;; Only used in abstract-destructure and generate-destructure for generating
 ;; error messages.
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  3
  (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (r? cs) r?)))
   (let ((found?
	  (find-if
	   (lambda (c) (and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
	   cs)))
    (if found?
	(k (cdr found?) cs)
	;; needs work: What is the circular value?
	(let* ((c (cons (cons v1 v2) #f))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ;; This is an optimization.
	  ((and (eq? v1 v2) (not (empty-abstract-value? v1))) (k #t cs))
	  ((union? v1)
	   (some-cps
	    (lambda (u1 cs k) (loop u1 v2 cs k)) (union-members v1) cs k))
	  ((union? v2)
	   (let ((c (cons (cons v1 v2) #f)))
	    (some-cps
	     (lambda (u2 cs k) (loop v1 u2 cs k)) (union-members v2) cs k)))
	  ((or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
	       (and (vlad-true? v1) (vlad-true? v2))
	       (and (vlad-false? v1) (vlad-false? v2))
	       (and (vlad-real? v1)
		    (vlad-real? v2)
		    (or (abstract-real? v1)
			(abstract-real? v2)
			;; This was = but then it equates exact values with
			;; inexact values and this breaks -imprecise-inexacts.
			(equal? v1 v2)))
	       (and (primitive-procedure? v1)
		    (primitive-procedure? v2)
		    (eq? v1 v2)))
	   (k #t cs))
	  ((and (nonrecursive-closure? v1)
		(nonrecursive-closure? v2)
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	   (loop (get-perturbation-tagged-value-primal v1)
		 (get-perturbation-tagged-value-primal v2)
		 cs
		 k))
	  ((and (bundle? v1) (bundle? v2))
	   (loop (get-bundle-primal v1)
		 (get-bundle-primal v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-bundle-tangent v1)
			    (get-bundle-tangent v2)
			    cs
			    k)
		      (k #f cs)))))
	  ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	   (loop (get-sensitivity-tagged-value-primal v1)
		 (get-sensitivity-tagged-value-primal v2)
		 cs
		 k))
	  ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	   (loop (get-reverse-tagged-value-primal v1)
		 (get-reverse-tagged-value-primal v2)
		 cs
		 k))
	  ((and (tagged-pair? v1)
		(tagged-pair? v2)
		(equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
	   (loop (get-tagged-pair-car v1)
		 (get-tagged-pair-car v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-tagged-pair-cdr v1)
			    (get-tagged-pair-cdr v2)
			    cs
			    k)
		      (k #f cs)))))
	  (else (k #f cs)))))))))

(define (abstract-value-unionable? v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  4
  (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (r? cs) r?)))
   (let ((found?
	  (find-if
	   (lambda (c) (and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
	   cs)))
    (if found?
	(k (cdr found?) cs)
	;; needs work: What is the circular value?
	(let* ((c (cons (cons v1 v2) #t))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ;; This is an optimization.
	  ((eq? v1 v2) (k #t cs))
	  ((union? v1)
	   (every-cps
	    (lambda (u1 cs k) (loop u1 v2 cs k)) (union-members v1) cs k))
	  ((union? v2)
	   (every-cps
	    (lambda (u2 cs k) (loop v1 u2 cs k)) (union-members v2) cs k))
	  ((or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
	       (and (vlad-boolean? v1) (vlad-boolean? v2))
	       (and (vlad-real? v1) (vlad-real? v2))
	       (and (primitive-procedure? v1)
		    (primitive-procedure? v2)
		    (eq? v1 v2))
	       (and (backpropagator? v1) (backpropagator? v2)))
	   (k #t cs))
	  ((and (nonrecursive-closure? v1)
		(nonrecursive-closure? v2)
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	   (loop (get-perturbation-tagged-value-primal v1)
		 (get-perturbation-tagged-value-primal v2)
		 cs
		 k))
	  ((and (bundle? v1) (bundle? v2))
	   (loop (get-bundle-primal v1)
		 (get-bundle-primal v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-bundle-tangent v1)
			    (get-bundle-tangent v2)
			    cs
			    k)
		      (k #f cs)))))
	  ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	   (loop (get-sensitivity-tagged-value-primal v1)
		 (get-sensitivity-tagged-value-primal v2)
		 cs
		 k))
	  ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	   (loop (get-reverse-tagged-value-primal v1)
		 (get-reverse-tagged-value-primal v2)
		 cs
		 k))
	  ((and (tagged-pair? v1)
		(tagged-pair? v2)
		(equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
	   (loop (get-tagged-pair-car v1)
		 (get-tagged-pair-car v2)
		 cs
		 (lambda (r? cs)
		  (if r?
		      (loop (get-tagged-pair-cdr v1)
			    (get-tagged-pair-cdr v2)
			    cs
			    k)
		      (k #f cs)))))
	  (else (k #f cs)))))))))

(define (abstract-value-union-internal v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 ;; The output can be wider than the strict union since unions of transformed
 ;; booleans are transformed into transformed unions of booleans, widening in
 ;; the process (for bundles).
 (time-it-bucket
  5
  (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (v cs) v)))
   (let ((found? (find-if (lambda (c)
			   (and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
			  cs)))
    (cond
     (found? (k (cdr found?) cs))
     ((union? v1)
      (unless (abstract-value-unionable? v1 v2)
       (compile-time-error "Program is not almost union free: ~s ~s"
			   (externalize v1)
			   (externalize v2)))
      (let* ((us (maximal-elements
		  abstract-value-subset?
		  (remove-duplicatesp
		   deep-abstract-value=?
		   (append (union-members v1) (union-members v2)))))
	     (u (if (and (not (null? us)) (null? (rest us)))
		    (first us)
		    (create-union us))))
       (k u (cons (cons (cons v1 v2) u) cs))))
     ((union? v2)
      (unless (abstract-value-unionable? v1 v2)
       (compile-time-error "Program is not almost union free: ~s ~s"
			   (externalize v1)
			   (externalize v2)))
      (let* ((us (maximal-elements
		  abstract-value-subset?
		  (remove-duplicatesp
		   deep-abstract-value=? (cons v1 (union-members v2)))))
	     (u (if (and (not (null? us)) (null? (rest us)))
		    (first us)
		    (create-union us))))
       (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (vlad-empty-list? v1) (vlad-empty-list? v2))
      (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (vlad-true? v1) (vlad-true? v2))
      (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (vlad-false? v1) (vlad-false? v2))
      (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (vlad-boolean? v1) (vlad-boolean? v2))
      (let ((u (abstract-boolean))) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (real? v1) (real? v2) (equal? v1 v2))
      (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (vlad-real? v1) (vlad-real? v2))
      (let ((u (abstract-real))) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
      (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (nonrecursive-closure? v1)
	   (nonrecursive-closure? v2)
	   (nonrecursive-closure-match? v1 v2)
	   (every abstract-value-unionable?
		  (get-nonrecursive-closure-values v1)
		  (get-nonrecursive-closure-values v2)))
      ;; See the note in abstract-environment=?.
      (let ((u (make-nonrecursive-closure
		'unfilled
		(nonrecursive-closure-lambda-expression v1)
		#f
		#f
		#f
		#f
		#f
		'unfilled)))
       (map2-cps loop
		 (get-nonrecursive-closure-values v1)
		 (get-nonrecursive-closure-values v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (vs cs)
		  (fill-nonrecursive-closure-values! u vs)
		  (k u cs)))))
     ((and (backpropagator? v1) (backpropagator? v2))
      (let ((u (if (deep-abstract-value=? v1 v2)
		   v1
		   (create-union (list v1 v2)))))
       (k u (cons (cons (cons v1 v2) u) cs))))
     ((and (recursive-closure? v1)
	   (recursive-closure? v2)
	   (recursive-closure-match? v1 v2))
      ;; See the note in abstract-environment=?.
      (let ((u (make-recursive-closure
		'unfilled
		(recursive-closure-procedure-variables v1)
		(recursive-closure-lambda-expressions v1)
		(recursive-closure-index v1)
		#f
		#f
		#f
		#f
		#f
		'unfilled)))
       (map2-cps loop
		 (get-recursive-closure-values v1)
		 (get-recursive-closure-values v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (vs cs)
		  (fill-recursive-closure-values! u vs)
		  (k u cs)))))
     ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
      (let ((u (make-perturbation-tagged-value
		'unfilled #f #f #f #f #f 'unfilled)))
       (loop (get-perturbation-tagged-value-primal v1)
	     (get-perturbation-tagged-value-primal v2)
	     (cons (cons (cons v1 v2) u) cs)
	     (lambda (v cs)
	      (fill-perturbation-tagged-value-primal! u v)
	      (k u cs)))))
     ((and (bundle? v1) (bundle? v2))
      (let ((u (make-bundle 'unfilled 'unfilled #f #f #f #f #f 'unfilled)))
       (loop (get-bundle-primal v1)
	     (get-bundle-primal v2)
	     (cons (cons (cons v1 v2) u) cs)
	     (lambda (v-primal cs)
	      (loop (get-bundle-tangent v1)
		    (get-bundle-tangent v2)
		    cs
		    (lambda (v-tangent cs)
		     (fill-bundle! u v-primal v-tangent)
		     (k u cs)))))))
     ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
      (let ((u (make-sensitivity-tagged-value
		'unfilled #f #f #f #f #f 'unfilled)))
       (loop (get-sensitivity-tagged-value-primal v1)
	     (get-sensitivity-tagged-value-primal v2)
	     (cons (cons (cons v1 v2) u) cs)
	     (lambda (v cs)
	      (fill-sensitivity-tagged-value-primal! u v)
	      (k u cs)))))
     ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
      (let ((u (make-reverse-tagged-value 'unfilled #f #f #f #f #f 'unfilled)))
       (loop (get-reverse-tagged-value-primal v1)
	     (get-reverse-tagged-value-primal v2)
	     (cons (cons (cons v1 v2) u) cs)
	     (lambda (v cs)
	      (fill-reverse-tagged-value-primal! u v)
	      (k u cs)))))
     ((and (tagged-pair? v1)
	   (tagged-pair? v2)
	   (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
      (let ((u (make-tagged-pair (tagged-pair-tags v1)
				 'unfilled
				 'unfilled
				 #f
				 #f
				 #f
				 #f
				 #f
				 'unfilled)))
       (loop (get-tagged-pair-car v1)
	     (get-tagged-pair-car v2)
	     (cons (cons (cons v1 v2) u) cs)
	     (lambda (v-car cs)
	      (loop (get-tagged-pair-cdr v1)
		    (get-tagged-pair-cdr v2)
		    cs
		    (lambda (v-cdr cs)
		     (fill-tagged-pair! u v-car v-cdr)
		     (k u cs)))))))
     (else (compile-time-error "Program is not almost union free: ~s ~s"
			       (externalize v1)
			       (externalize v2))))))))

(define (abstract-value-union v1 v2)
 (canonize-and-maybe-intern-abstract-value
  (abstract-value-union-internal v1 v2)))

(define (canonize-abstract-value v)
 ;; This is written in CPS so as not to break structure sharing.
 ;; The whole purpose of this procedure is to:
 ;; - propagate empty abstract values (empty unions) upward so that there are
 ;;   never any nested empty abstract values,
 ;; - to merge unions of unions so that there are never any unions immediately
 ;;   nested in another union,
 ;; - to remove singleton unions, and
 ;; - to propagate unions of transformed booleans into transformed unions of
 ;;   booleans. For bundles, this widens in the process.
 ;; If assq is replaced with assp deep-abstract-value=? then this also:
 ;; - discovers structure to share.
 ;; It is necessary to use assp deep-abstract-value=? or else an error occurs
 ;; during nr-sqrt-RR where equivalent but non-eq recursive abstract values are
 ;; nested and then path-of-greatest-depth finds a path with equivalent but
 ;; non-eq values which when merged yield a value that agai has that path
 ;; causing an infinite loop.
 (time-it-bucket
  6
  (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
   (if (or (and (nonrecursive-closure? v)
		(nonrecursive-closure-canonical? v))
	   (and (recursive-closure? v)
		(recursive-closure-canonical? v))
	   (and (perturbation-tagged-value? v)
		(perturbation-tagged-value-canonical? v))
	   (and (bundle? v) (bundle-canonical? v))
	   (and (sensitivity-tagged-value? v)
		(sensitivity-tagged-value-canonical? v))
	   (and (reverse-tagged-value? v)
		(reverse-tagged-value-canonical? v))
	   (and (tagged-pair? v) (tagged-pair-canonical? v))
	   (and (union? v) (union-canonical? v)))
       (k v cs)
       (let ((found? (assp deep-abstract-value=? v cs)))
	(cond
	 (found? (k (cdr found?) cs))
	 ((deep-empty-abstract-value? v)
	  (let ((u-prime (empty-abstract-value)))
	   (k u-prime (cons (cons v u-prime) cs))))
	 ((union? v)
	  ;; This is the whole reason we require that abstract values be copied.
	  ;; This performs the optimization that unionize performs but
	  ;; fill-union-values! is unable to because of unfilled slots.
	  (let ((us (remove-if
		     deep-empty-abstract-value?
		     ;; This is what propagates unions of transformed
		     ;; booleans into transformed unions of booleans and
		     ;; widens in the process (for bundles).
		     (union-members (reduce abstract-value-union-internal
					    (union-members v)
					    (empty-abstract-value))))))
	   ;; This is just to trigger errors on aggregate abstract values that
	   ;; have empty slots. We could do this everywhere which would trigger
	   ;; the error earlier, at the time of creation, but this just triggers
	   ;; the same error later, since we require that every abstract value
	   ;; be copied.
	   (cond ((null? us) (k (empty-abstract-value) cs))
		 ((null? (rest us))
		  (loop (first us) (cons (cons v (first us)) cs) k))
		 (else (let ((v-prime
			      (make-union 'unfilled #t #f #f #f #f 'unfilled)))
			(map-cps loop
				 us
				 (cons (cons v v-prime) cs)
				 (lambda (us-prime cs)
				  (assert (and (not (null? us-prime))
					       (not (null? (rest us-prime)))))
				  (fill-union-values! v-prime us-prime)
				  (k v-prime cs))))))))
	 ((vlad-empty-list? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-true? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-false? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-real? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((primitive-procedure? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((nonrecursive-closure? v)
	  ;; See the note in abstract-environment=?.
	  (let ((u-prime (make-nonrecursive-closure
			  'unfilled
			  (nonrecursive-closure-lambda-expression v)
			  #t
			  #f
			  #f
			  #f
			  #f
			  'unfilled)))
	   (assert
	    (and (= (length (get-nonrecursive-closure-values v))
		    (length (free-variables
			     (nonrecursive-closure-lambda-expression u-prime))))
		 ;; See the note in new-nonrecursive-closure.
		 (or *abstract?*
		     (every (lambda (x v)
			     (prefix-tags? (variable-tags x) (value-tags v)))
			    (free-variables
			     (nonrecursive-closure-lambda-expression u-prime))
			    (get-nonrecursive-closure-values v)))
		 (not (some empty-abstract-value?
			    (get-nonrecursive-closure-values v)))
		 (or (not *abstract?*)
		     (every (lambda (x v)
			     (some-value-tags
			      (lambda (tags)
			       (prefix-tags? (variable-tags x) tags)) v))
			    (free-variables
			     (nonrecursive-closure-lambda-expression u-prime))
			    (get-nonrecursive-closure-values v)))))
	   (map-cps loop
		    (get-nonrecursive-closure-values v)
		    (cons (cons v u-prime) cs)
		    (lambda (vs-prime cs)
		     (fill-nonrecursive-closure-values! u-prime vs-prime)
		     (k u-prime cs)))))
	 ((recursive-closure? v)
	  ;; See the note in abstract-environment=?.
	  (let ((u-prime (make-recursive-closure
			  'unfilled
			  (recursive-closure-procedure-variables v)
			  (recursive-closure-lambda-expressions v)
			  (recursive-closure-index v)
			  #t
			  #f
			  #f
			  #f
			  #f
			  'unfilled)))
	   (assert
	    (and (= (length (get-recursive-closure-values v))
		    (length (recursive-closure-variables u-prime)))
		 ;; See the note in new-nonrecursive-closure.
		 (or *abstract?*
		     (every (lambda (x v)
			     (prefix-tags? (variable-tags x) (value-tags v)))
			    (recursive-closure-variables u-prime)
			    (get-recursive-closure-values v)))
		 (not (some empty-abstract-value?
			    (get-recursive-closure-values v)))
		 (or (not *abstract?*)
		     (every (lambda (x v)
			     (some-value-tags
			      (lambda (tags)
			       (prefix-tags? (variable-tags x) tags)) v))
			    (recursive-closure-variables u-prime)
			    (get-recursive-closure-values v)))))
	   (map-cps loop
		    (get-recursive-closure-values v)
		    (cons (cons v u-prime) cs)
		    (lambda (vs-prime cs)
		     (fill-recursive-closure-values! u-prime vs-prime)
		     (k u-prime cs)))))
	 ((perturbation-tagged-value? v)
	  (let ((u-prime (make-perturbation-tagged-value
			  'unfilled #t #f #f #f #f 'unfilled)))
	   (assert (not (empty-abstract-value?
			 (get-perturbation-tagged-value-primal v))))
	   (loop (get-perturbation-tagged-value-primal v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-prime cs)
		  (fill-perturbation-tagged-value-primal! u-prime v-prime)
		  (k u-prime cs)))))
	 ((bundle? v)
	  (let ((u-prime (make-bundle
			  'unfilled 'unfilled #t #f #f #f #f 'unfilled)))
	   (assert
	    (and (some-bundlable? (get-bundle-primal v) (get-bundle-tangent v))
		 (not (empty-abstract-value? (get-bundle-primal v)))
		 (not (empty-abstract-value? (get-bundle-tangent v)))))
	   (loop (get-bundle-primal v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-primal-prime cs)
		  (loop (get-bundle-tangent v)
			cs
			(lambda (v-tangent-prime cs)
			 (fill-bundle! u-prime v-primal-prime v-tangent-prime)
			 (k u-prime cs)))))))
	 ((sensitivity-tagged-value? v)
	  (let ((u-prime (make-sensitivity-tagged-value
			  'unfilled #t #f #f #f #f 'unfilled)))
	   (assert (not (empty-abstract-value?
			 (get-sensitivity-tagged-value-primal v))))
	   (loop (get-sensitivity-tagged-value-primal v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-prime cs)
		  (fill-sensitivity-tagged-value-primal! u-prime v-prime)
		  (k u-prime cs)))))
	 ((reverse-tagged-value? v)
	  (let ((u-prime (make-reverse-tagged-value
			  'unfilled #t #f #f #f #f 'unfilled)))
	   (assert
	    (not (empty-abstract-value? (get-reverse-tagged-value-primal v))))
	   (loop (get-reverse-tagged-value-primal v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-prime cs)
		  (fill-reverse-tagged-value-primal! u-prime v-prime)
		  (k u-prime cs)))))
	 ((tagged-pair? v)
	  (let ((u-prime (make-tagged-pair (tagged-pair-tags v)
					   'unfilled
					   'unfilled
					   #t
					   #f
					   #f
					   #f
					   #f
					   'unfilled)))
	   (assert
	    (and
	     (or *abstract?*
		 (and (prefix-tags? (tagged-pair-tags u-prime)
				    (value-tags (get-tagged-pair-car v)))
		      (prefix-tags? (tagged-pair-tags u-prime)
				    (value-tags (get-tagged-pair-cdr v)))))
	     (not (empty-abstract-value? (get-tagged-pair-car v)))
	     (not (empty-abstract-value? (get-tagged-pair-cdr v)))
	     (or
	      (not *abstract?*)
	      (and
	       (some-value-tags
		(lambda (tags) (prefix-tags? (tagged-pair-tags u-prime) tags))
		(get-tagged-pair-car v))
	       (some-value-tags
		(lambda (tags) (prefix-tags? (tagged-pair-tags u-prime) tags))
		(get-tagged-pair-cdr v))))))
	   (loop (get-tagged-pair-car v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-car-prime cs)
		  (loop (get-tagged-pair-cdr v)
			cs
			(lambda (v-cdr-prime cs)
			 (fill-tagged-pair! u-prime v-car-prime v-cdr-prime)
			 (k u-prime cs)))))))
	 (else (internal-error))))))))

(define (intern-abstract-value v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  7
  (let loop ((v v) (cs '()) (k (lambda (v-prime cs)
				(when *expensive-checks?*
				 (check-abstract-value! v-prime))
				v-prime)))
   (if (or (and (nonrecursive-closure? v)
		(nonrecursive-closure-interned? v))
	   (and (recursive-closure? v)
		(recursive-closure-interned? v))
	   (and (perturbation-tagged-value? v)
		(perturbation-tagged-value-interned? v))
	   (and (bundle? v) (bundle-interned? v))
	   (and (sensitivity-tagged-value? v)
		(sensitivity-tagged-value-interned? v))
	   (and (reverse-tagged-value? v)
		(reverse-tagged-value-interned? v))
	   (and (tagged-pair? v) (tagged-pair-interned? v))
	   (and (union? v) (union-interned? v)))
       (k v cs)
       (let ((found? (assq v cs)))
	(cond
	 (found? (k (cdr found?) cs))
	 ((union? v)
	  (let ((v-prime
		 ;; here I am: v-prime might be unfilled. Ditto all cases below.
		 (find-if (lambda (v-prime) (deep-abstract-value=? v-prime v))
			  *unions*)))
	   (if v-prime
	       (k v-prime (cons (cons v v-prime) cs))
	       (let ((v-prime (make-union 'unfilled #t #f #f #f #f 'unfilled)))
		(map-cps
		 loop
		 (get-union-values v)
		 (cons (cons v v-prime) cs)
		 (lambda (us-prime cs)
		  (assert
		   (and (not (null? us-prime)) (not (null? (rest us-prime)))))
		  (fill-union-values! v-prime us-prime)
		  ;; here I am: v-prime might be unfilled. Ditto all cases
		  ;;            below.
		  (when *expensive-checks?*
		   (assert (not (memp deep-abstract-value=? v-prime *unions*))))
		  (set! *unions* (cons v-prime *unions*))
		  (set-union-interned?! v-prime #t)
		  (k v-prime cs)))))))
	 ((vlad-empty-list? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-true? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-false? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((vlad-real? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((primitive-procedure? v)
	  (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
	 ((nonrecursive-closure? v)
	  ;; See the notes in new-nonrecursive-closure.
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  (lambda-expression-nonrecursive-closures
			   (nonrecursive-closure-lambda-expression v)))))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       ;; See the note in abstract-environment=?.
	       (let ((u-prime (make-nonrecursive-closure
			       'unfilled
			       (nonrecursive-closure-lambda-expression v)
			       #t
			       #f
			       #f
			       #f
			       #f
			       'unfilled)))
		(assert
		 (and
		  (= (length (get-nonrecursive-closure-values v))
		     (length
		      (free-variables
		       (nonrecursive-closure-lambda-expression u-prime))))
		  ;; See the note in new-nonrecursive-closure.
		  (or *abstract?*
		      (every (lambda (x v)
			      (prefix-tags? (variable-tags x) (value-tags v)))
			     (free-variables
			      (nonrecursive-closure-lambda-expression u-prime))
			     (get-nonrecursive-closure-values v)))
		  (not (some empty-abstract-value?
			     (get-nonrecursive-closure-values v)))
		  (or (not *abstract?*)
		      (every (lambda (x v)
			      (some-value-tags
			       (lambda (tags)
				(prefix-tags? (variable-tags x) tags)) v))
			     (free-variables
			      (nonrecursive-closure-lambda-expression u-prime))
			     (get-nonrecursive-closure-values v)))))
		(map-cps
		 loop
		 (get-nonrecursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-nonrecursive-closure-values! u-prime vs-prime)
		  (when *expensive-checks?*
		   (assert
		    (not (memp deep-abstract-value=?
			       u-prime
			       (lambda-expression-nonrecursive-closures
				(nonrecursive-closure-lambda-expression v))))))
		  (set-lambda-expression-nonrecursive-closures!
		   (nonrecursive-closure-lambda-expression u-prime)
		   (cons u-prime
			 (lambda-expression-nonrecursive-closures
			  (nonrecursive-closure-lambda-expression v))))
		  (set-nonrecursive-closure-interned?! u-prime #t)
		  (k u-prime cs)))))))
	 ((recursive-closure? v)
	  ;; See the notes in new-recursive-closure.
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  (lambda-expression-recursive-closures
			   (vector-ref
			    (recursive-closure-lambda-expressions v) 0)))))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       ;; See the note in abstract-environment=?.
	       (let ((u-prime (make-recursive-closure
			       'unfilled
			       (recursive-closure-procedure-variables v)
			       (recursive-closure-lambda-expressions v)
			       (recursive-closure-index v)
			       #t
			       #f
			       #f
			       #f
			       #f
			       'unfilled)))
		(assert
		 (and
		  (= (length (get-recursive-closure-values v))
		     (length (recursive-closure-variables u-prime)))
		  ;; See the note in new-nonrecursive-closure.
		  (or *abstract?*
		      (every (lambda (x v)
			      (prefix-tags? (variable-tags x) (value-tags v)))
			     (recursive-closure-variables u-prime)
			     (get-recursive-closure-values v)))
		  (not (some empty-abstract-value?
			     (get-recursive-closure-values v)))
		  (or (not *abstract?*)
		      (every (lambda (x v)
			      (some-value-tags
			       (lambda (tags)
				(prefix-tags? (variable-tags x) tags)) v))
			     (recursive-closure-variables u-prime)
			     (get-recursive-closure-values v)))))
		(map-cps
		 loop
		 (get-recursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-recursive-closure-values! u-prime vs-prime)
		  (when *expensive-checks?*
		   (assert
		    (not
		     (memp deep-abstract-value=?
			   u-prime
			   (lambda-expression-recursive-closures
			    (vector-ref
			     (recursive-closure-lambda-expressions v) 0))))))
		  (set-lambda-expression-recursive-closures!
		   (vector-ref
		    (recursive-closure-lambda-expressions u-prime) 0)
		   (cons u-prime
			 (lambda-expression-recursive-closures
			  (vector-ref
			   (recursive-closure-lambda-expressions v) 0))))
		  (set-recursive-closure-interned?! u-prime #t)
		  (k u-prime cs)))))))
	 ((perturbation-tagged-value? v)
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  *perturbation-tagged-values*)))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       (let ((u-prime (make-perturbation-tagged-value
			       'unfilled #t #f #f #f #f 'unfilled)))
		(assert (not (empty-abstract-value?
			      (get-perturbation-tagged-value-primal v))))
		(loop (get-perturbation-tagged-value-primal v)
		      (cons (cons v u-prime) cs)
		      (lambda (v-prime cs)
		       (fill-perturbation-tagged-value-primal! u-prime v-prime)
		       (when *expensive-checks?*
			(assert (not (memp deep-abstract-value=?
					   u-prime
					   *perturbation-tagged-values*))))
		       (set! *perturbation-tagged-values*
			     (cons u-prime *perturbation-tagged-values*))
		       (set-perturbation-tagged-value-interned?! u-prime #t)
		       (k u-prime cs)))))))
	 ((bundle? v)
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  *bundles*)))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       (let ((u-prime (make-bundle
			       'unfilled 'unfilled #t #f #f #f #f 'unfilled)))
		(assert
		 (and
		  (some-bundlable? (get-bundle-primal v) (get-bundle-tangent v))
		  (not (empty-abstract-value? (get-bundle-primal v)))
		  (not (empty-abstract-value? (get-bundle-tangent v)))))
		(loop
		 (get-bundle-primal v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-primal-prime cs)
		  (loop (get-bundle-tangent v)
			cs
			(lambda (v-tangent-prime cs)
			 (fill-bundle! u-prime v-primal-prime v-tangent-prime)
			 (when *expensive-checks?*
			  (assert (not (memp deep-abstract-value=?
					     u-prime
					     *bundles*))))
			 (set! *bundles* (cons u-prime *bundles*))
			 (set-bundle-interned?! u-prime #t)
			 (k u-prime cs)))))))))
	 ((sensitivity-tagged-value? v)
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  *sensitivity-tagged-values*)))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       (let ((u-prime (make-sensitivity-tagged-value
			       'unfilled #t #f #f #f #f 'unfilled)))
		(assert (not (empty-abstract-value?
			      (get-sensitivity-tagged-value-primal v))))
		(loop (get-sensitivity-tagged-value-primal v)
		      (cons (cons v u-prime) cs)
		      (lambda (v-prime cs)
		       (fill-sensitivity-tagged-value-primal! u-prime v-prime)
		       (when *expensive-checks?*
			(assert (not (memp deep-abstract-value=?
					   u-prime
					   *sensitivity-tagged-values*))))
		       (set! *sensitivity-tagged-values*
			     (cons u-prime *sensitivity-tagged-values*))
		       (set-sensitivity-tagged-value-interned?! u-prime #t)
		       (k u-prime cs)))))))
	 ((reverse-tagged-value? v)
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  *reverse-tagged-values*)))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       (let ((u-prime (make-reverse-tagged-value
			       'unfilled #t #f #f #f #f 'unfilled)))
		(assert
		 (not
		  (empty-abstract-value? (get-reverse-tagged-value-primal v))))
		(loop (get-reverse-tagged-value-primal v)
		      (cons (cons v u-prime) cs)
		      (lambda (v-prime cs)
		       (fill-reverse-tagged-value-primal! u-prime v-prime)
		       (when *expensive-checks?*
			(assert (not (memp deep-abstract-value=?
					   u-prime
					   *reverse-tagged-values*))))
		       (set! *reverse-tagged-values*
			     (cons u-prime *reverse-tagged-values*))
		       (set-reverse-tagged-value-interned?! u-prime #t)
		       (k u-prime cs)))))))
	 ((tagged-pair? v)
	  (let ((u-prime
		 (find-if (lambda (u-prime) (deep-abstract-value=? u-prime v))
			  *tagged-pairs*)))
	   (if u-prime
	       (k u-prime (cons (cons v u-prime) cs))
	       (let ((u-prime (make-tagged-pair (tagged-pair-tags v)
						'unfilled
						'unfilled
						#t
						#f
						#f
						#f
						#f
						'unfilled)))
		(assert
		 (and
		  (or *abstract?*
		      (and (prefix-tags? (tagged-pair-tags u-prime)
					 (value-tags (get-tagged-pair-car v)))
			   (prefix-tags? (tagged-pair-tags u-prime)
					 (value-tags (get-tagged-pair-cdr v)))))
		  (not (empty-abstract-value? (get-tagged-pair-car v)))
		  (not (empty-abstract-value? (get-tagged-pair-cdr v)))
		  (or
		   (not *abstract?*)
		   (and
		    (some-value-tags
		     (lambda (tags)
		      (prefix-tags? (tagged-pair-tags u-prime) tags))
		     (get-tagged-pair-car v))
		    (some-value-tags
		     (lambda (tags)
		      (prefix-tags? (tagged-pair-tags u-prime) tags))
		     (get-tagged-pair-cdr v))))))
		(loop
		 (get-tagged-pair-car v)
		 (cons (cons v u-prime) cs)
		 (lambda (v-car-prime cs)
		  (loop (get-tagged-pair-cdr v)
			cs
			(lambda (v-cdr-prime cs)
			 (fill-tagged-pair! u-prime v-car-prime v-cdr-prime)
			 (when *expensive-checks?*
			  (assert (not (memp deep-abstract-value=?
					     u-prime
					     *tagged-pairs*))))
			 (set! *tagged-pairs* (cons u-prime *tagged-pairs*))
			 (set-tagged-pair-interned?! u-prime #t)
			 (k u-prime cs)))))))))
	 (else (internal-error))))))))

(define (canonize-and-maybe-intern-abstract-value v)
 (let ((v (canonize-abstract-value v)))
  (if *memoized?* (intern-abstract-value v) v)))

;;; Abstract Environment Equivalence

(define (deep-abstract-environment=? vs1 vs2)
 ;; This assumes that the free variables in two alpha-equivalent expressions
 ;; are in the same order. Note that this is a weak notion of equivalence. A
 ;; stronger notion would attempt to find a correspondence between the free
 ;; variables that would allow them to be contextually alpha equivalent.
 (every deep-abstract-value=? vs1 vs2))

(define (abstract-environment=? vs1 vs2)
 ;; This assumes that the free variables in two alpha-equivalent expressions
 ;; are in the same order. Note that this is a weak notion of equivalence. A
 ;; stronger notion would attempt to find a correspondence between the free
 ;; variables that would allow them to be contextually alpha equivalent.
 (every abstract-value=? vs1 vs2))

;;; Search path

(define (search-include-path-without-extension pathname)
 (cond ((can-open-file-for-input? pathname) pathname)
       ((and (>= (string-length pathname) 1)
	     (char=? (string-ref pathname 0) #\/))
	(compile-time-error "Cannot find: ~a" pathname))
       (else (let loop ((include-path *include-path*))
	      (cond ((null? include-path)
		     (compile-time-error "Cannot find: ~a" pathname))
		    ((can-open-file-for-input?
		      (string-append (first include-path) "/" pathname))
		     (string-append (first include-path) "/" pathname))
		    (else (loop (rest include-path))))))))

(define (search-include-path pathname)
 (search-include-path-without-extension (default-extension pathname "vlad")))

(define (read-source pathname)
 (let ((pathname (default-extension pathname "vlad")))
  (unless (can-open-file-for-input? pathname)
   (compile-time-error "Cannot find: ~a" pathname))
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

;;; Definitions

(define (definens? e)
 (or (concrete-variable? e)
     (and (list? e) (not (null? e)) (definens? (first e)))))

(define (definition? d)
 (and
  (list? d) (= (length d) 3) (eq? (first d) 'define) (definens? (second d))))

(define (definens-name e)
 (if (concrete-variable? e) e (definens-name (first e))))

(define (definens-expression e1 e2)
 (if (concrete-variable? e1)
     e2
     (definens-expression (first e1) `(lambda ,(rest e1) ,e2))))

(define (expand-definitions ds e)
 (for-each
  (lambda (d)
   (unless (definition? d) (compile-time-error "Invalid definition: ~s" d)))
  ds)
 `(letrec ,(map (lambda (d)
		 `(,(definens-name (second d))
		   ,(definens-expression (second d) (third d))))
		ds)
   ,e))

;;; Alpha conversion

(define (alphaify x)
 (set! *alpha* (+ *alpha* 1))
 (new-variable `(alpha ,(variable-name x) ,*alpha*)))

(define (alpha-convert-parameter p)
 ;; needs work: Should have structure instead of list.
 ;; The output is (p bs) where p is the alpha converted parameter and bs is the
 ;; renamings.
 (cond
  ((constant-expression? p) (list p '()))
  ((variable-access-expression? p)
   (let ((x (alphaify (variable-access-expression-variable p))))
    (list
     (new-variable-access-expression x)
     (list (make-alpha-binding (variable-access-expression-variable p) x)))))
  ((lambda-expression? p)
   (let loop ((bs '()) (xs (parameter-variables p)))
    (if (null? xs)
	(list (alpha-convert-expression p bs) bs)
	(let ((x (alphaify (first xs))))
	 (loop (cons (make-alpha-binding (first xs) x) bs) (rest xs))))))
  ((letrec-expression? p)
   (let loop ((bs '()) (xs (parameter-variables p)))
    (if (null? xs)
	(list (alpha-convert-expression p bs) bs)
	(let ((x (alphaify (first xs))))
	 (loop (cons (make-alpha-binding (first xs) x) bs) (rest xs))))))
  ((cons-expression? p)
   (let* ((result1 (alpha-convert-parameter (cons-expression-car p)))
	  (result2 (alpha-convert-parameter (cons-expression-cdr p))))
    (list (new-cons-expression
	   (cons-expression-tags p) (first result1) (first result2))
	  (append (second result1) (second result2)))))
  (else (internal-error))))

(define (link-inverses e1 e)
 (assert
  (and
   (or (and (not (lambda-expression-alpha-conversion-inverse e))
	    (not (lambda-expression-alpha-conversion-inverse e1)))
       (and (lambda-expression-alpha-conversion-inverse e)
	    (or (not (lambda-expression-alpha-conversion-inverse e1))
		(expression-eqv?
		 (lambda-expression-alpha-conversion-inverse e)
		 (lambda-expression-alpha-conversion-inverse e1)))))
   (or (and (not (lambda-expression-perturbation-transform-inverse e))
	    (not (lambda-expression-perturbation-transform-inverse e1)))
       (and (lambda-expression-perturbation-transform-inverse e)
	    (or (not (lambda-expression-perturbation-transform-inverse e1))
		(expression-eqv?
		 (lambda-expression-perturbation-transform-inverse e)
		 (lambda-expression-perturbation-transform-inverse e1)))))
   (or (and (not (lambda-expression-forward-transform-inverse e))
	    (not (lambda-expression-forward-transform-inverse e1)))
       (and (lambda-expression-forward-transform-inverse e)
	    (or (not (lambda-expression-forward-transform-inverse e1))
		(expression-eqv?
		 (lambda-expression-forward-transform-inverse e)
		 (lambda-expression-forward-transform-inverse e1)))))
   (or (and (not (lambda-expression-sensitivity-transform-inverse e))
	    (not (lambda-expression-sensitivity-transform-inverse e1)))
       (and (lambda-expression-sensitivity-transform-inverse e)
	    (or (not (lambda-expression-sensitivity-transform-inverse e1))
		(expression-eqv?
		 (lambda-expression-sensitivity-transform-inverse e)
		 (lambda-expression-sensitivity-transform-inverse e1)))))
   (or (and (not (lambda-expression-reverse-transform-inverse e))
	    (not (lambda-expression-reverse-transform-inverse e1)))
       (and (lambda-expression-reverse-transform-inverse e)
	    (or (not (lambda-expression-reverse-transform-inverse e1))
		(expression-eqv?
		 (lambda-expression-reverse-transform-inverse e)
		 (lambda-expression-reverse-transform-inverse e1)))))))
 (when (and (lambda-expression-alpha-conversion-inverse e)
	    (not (lambda-expression-alpha-conversion-inverse e1)))
  (set-lambda-expression-alpha-conversion-inverse!
   e1 (lambda-expression-alpha-conversion-inverse e)))
 (when (and (lambda-expression-perturbation-transform-inverse e)
	    (not (lambda-expression-perturbation-transform-inverse e1)))
  (set-lambda-expression-perturbation-transform-inverse!
   e1 (lambda-expression-perturbation-transform-inverse e)))
 (when (and (lambda-expression-forward-transform-inverse e)
	    (not (lambda-expression-forward-transform-inverse e1)))
  (set-lambda-expression-forward-transform-inverse!
   e1 (lambda-expression-forward-transform-inverse e)))
 (when (and (lambda-expression-sensitivity-transform-inverse e)
	    (not (lambda-expression-sensitivity-transform-inverse e1)))
  (set-lambda-expression-sensitivity-transform-inverse!
   e1 (lambda-expression-sensitivity-transform-inverse e)))
 (when (and (lambda-expression-reverse-transform-inverse e)
	    (not (lambda-expression-reverse-transform-inverse e1)))
  (set-lambda-expression-reverse-transform-inverse!
   e1 (lambda-expression-reverse-transform-inverse e)))
 e1)

(define (alpha-convert-expression e bs)
 ;; bs is the renamings currently in scope
 ;; The output is e.
 (cond
  ((constant-expression? e) e)
  ((variable-access-expression? e)
   (new-variable-access-expression
    (alpha-binding-variable2
     (find-if (lambda (b)
	       (variable=? (alpha-binding-variable1 b)
			   (variable-access-expression-variable e)))
	      bs))))
  ((lambda-expression? e)
   (let* ((result (alpha-convert-parameter (lambda-expression-parameter e)))
	  (e1 (link-inverses
	       (new-lambda-expression
		(first result)
		(alpha-convert-expression (lambda-expression-body e)
					  (append (second result) bs)))
	       e)))
    (assert (not (lambda-expression-alpha-conversion-inverse e1)))
    (set-lambda-expression-alpha-conversion-inverse! e1 e)
    e1))
  ((application? e)
   (new-application (alpha-convert-expression (application-callee e) bs)
		    (alpha-convert-expression (application-argument e) bs)))
  ((letrec-expression? e)
   (let outer ((xs1 (letrec-expression-procedure-variables e)) (xs2 '()))
    (if (null? xs1)
	(let ((bs (append (map make-alpha-binding
			       (letrec-expression-procedure-variables e)
			       (reverse xs2))
			  bs)))
	 (let inner ((es (letrec-expression-lambda-expressions e)) (es1 '()))
	  (if (null? es)
	      (new-letrec-expression
	       (reverse xs2)
	       (reverse es1)
	       (alpha-convert-expression (letrec-expression-body e) bs))
	      (inner (rest es)
		     (cons (alpha-convert-expression (first es) bs) es1)))))
	(outer (rest xs1) (cons (alphaify (first xs1)) xs2)))))
  ((cons-expression? e)
   (new-cons-expression (cons-expression-tags e)
			(alpha-convert-expression (cons-expression-car e) bs)
			(alpha-convert-expression (cons-expression-cdr e) bs)))
  (else (internal-error))))

(define (alpha-convert e)
 (alpha-convert-expression
  e (map make-alpha-binding (free-variables e) (free-variables e))))

;;; ANF conversion

;;; The soundness of our method for ANF conversion relies on two things:
;;;  1. E must be alpha converted.
;;;     This allows letrecs to be merged.
;;;     It also allows let*s in expressions of let*s to be merged.
;;;  2. No letrec nested in a let* expression or body can reference a variable
;;;     bound by that let*.

(define (anf-result result)
 ;; needs work: Should have structure instead of list.
 (assert (or (null? (fourth result))
	     ;; needs work: To abstract this.
	     (null?
	      (rest
	       (remove-duplicates
		(map (lambda (b)
		      (lambda-expression-tags (variable-binding-expression b)))
		     (fourth result)))))))
 (new-letrec-expression
  (map variable-binding-variable (reverse (fourth result)))
  (map variable-binding-expression (reverse (fourth result)))
  (new-let* (map parameter-binding-parameter (reverse (third result)))
	    (map parameter-binding-expression (reverse (third result)))
	    (second result))))

(define (anf-max e)
 (cond
  ((constant-expression? e) 0)
  ((variable-access-expression? e)
   (variable-anf-max (variable-access-expression-variable e)))
  ((lambda-expression? e)
   (max (anf-max (lambda-expression-parameter e))
	(anf-max (lambda-expression-body e))))
  ((application? e)
   (max (anf-max (application-callee e)) (anf-max (application-argument e))))
  ((letrec-expression? e)
   (max (map-reduce
	 max 0 variable-anf-max (letrec-expression-procedure-variables e))
	(map-reduce max 0 anf-max (letrec-expression-lambda-expressions e))
	(anf-max (letrec-expression-body e))))
  ((cons-expression? e)
   (max (anf-max (cons-expression-car e)) (anf-max (cons-expression-cdr e))))
  (else (internal-error))))

(define (anf-convert-parameter i p p?)
 ;; needs work: Should have structure instead of list.
 (cond
  ;; result
  ((constant-expression? p) (list i p))
  ;; result
  ((variable-access-expression? p) (list i p))
  ((lambda-expression? p)
   (let* ((result1
	   (anf-convert-parameter i (lambda-expression-parameter p) p?))
	  (result2
	   (anf-convert-expression
	    (first result1) (lambda-expression-body p) '() '() p? #f)))
    ;; result
    (list (first result2)
	  (link-inverses
	   (new-lambda-expression (second result1) (anf-result result2)) p))))
  ((letrec-expression? p)
   (assert (and (variable-access-expression? (letrec-expression-body p))
		(memp variable=?
		      (variable-access-expression-variable
		       (letrec-expression-body p))
		      (letrec-expression-procedure-variables p))))
   (let loop ((i i) (es (letrec-expression-lambda-expressions p)) (es1 '()))
    (if (null? es)
	;; result
	(list i
	      (new-letrec-expression
	       (letrec-expression-procedure-variables p)
	       (reverse es1)
	       (letrec-expression-body p)))
	(let* ((result1 (anf-convert-parameter
			 i (lambda-expression-parameter (first es)) p?))
	       (result2 (anf-convert-expression
			 (first result1)
			 (lambda-expression-body (first es))
			 '()
			 '()
			 p?
			 #f)))
	 (loop
	  (first result2)
	  (rest es)
	  (cons (link-inverses
		 (new-lambda-expression (second result1) (anf-result result2))
		 (first es))
		es1))))))
  ((cons-expression? p)
   (let* ((result1 (anf-convert-parameter i (cons-expression-car p) p?))
	  (result2 (anf-convert-parameter
		    (first result1) (cons-expression-cdr p) p?)))
    ;; result
    (list (first result2)
	  (new-cons-expression
	   (cons-expression-tags p) (second result1) (second result2)))))
  (else (internal-error))))

(define (anf-convert-expression i e bs1 bs2 p? p1?)
 ;; needs work: Should have structure instead of list.
 (cond
  ((constant-expression? e)
   (let* ((i (+ i 1)) (p (new-variable-access-expression (anfify i))))
    ;; result
    (list i p (cons (make-parameter-binding p e) bs1) bs2)))
  ((variable-access-expression? e)
   (if p?
       ;; This is used during reverse-transform because it
       ;; guarantees that there is a one-to-one correspondence
       ;; between primal and forward phase bindings so that the
       ;; reverse transform is invertible.
       ;; result
       (list i e bs1 bs2)
       ;; This is used during parsing to guarantee that there is
       ;;                                            ___    _
       ;;                                            \      \
       ;; no binding like x = y,y which would become y,y += x
       ;; during reverse phase which incorrecty accumulates.
       (let* ((i (+ i 1)) (p (new-variable-access-expression (anfify i))))
	;; result
	(list i p (cons (make-parameter-binding p e) bs1) bs2))))
  ((lambda-expression? e)
   (if p1?
       (let* ((i (+ i 1)) (p (new-variable-access-expression (anfify i))))
	;; result
	(list i p (cons (make-parameter-binding p e) bs1) bs2))
       (let* ((result1
	       (anf-convert-parameter i (lambda-expression-parameter e) p?))
	      (result2 (anf-convert-expression (first result1)
					       (lambda-expression-body e)
					       '()
					       '()
					       p?
					       p1?))
	      (i (+ (first result2) 1))
	      (p (new-variable-access-expression (anfify i))))
	;; result
	(list
	 i
	 p
	 (cons (make-parameter-binding
		p
		(link-inverses
		 (new-lambda-expression (second result1) (anf-result result2))
		 e))
	       bs1)
	 bs2))))
  ((let*? e)
   (let* ((result1 (anf-convert-parameter
		    i (lambda-expression-parameter (application-callee e)) p?))
	  (result2 (anf-convert-reuse (second result1)
				      (first result1)
				      (application-argument e)
				      bs1
				      bs2
				      p?
				      p1?)))
    (anf-convert-expression (first result2)
			    (lambda-expression-body (application-callee e))
			    (third result2)
			    (fourth result2)
			    p?
			    p1?)))
  ((application? e)
   (let* ((result1
	   (anf-convert-expression i (application-callee e) bs1 bs2 p? p1?))
	  (result2 (anf-convert-expression (first result1)
					   (application-argument e)
					   (third result1)
					   (fourth result1)
					   p?
					   p1?))
	  (i (+ (first result2) 1))
	  (p (new-variable-access-expression (anfify i))))
    ;; result
    (list
     i
     p
     (cons (make-parameter-binding
	    p (new-application (second result1) (second result2)))
	   (third result2))
     (fourth result2))))
  ((letrec-expression? e)
   (if p1?
       (anf-convert-expression
	i
	(letrec-expression-body e)
	bs1
	(append (reverse (map make-variable-binding
			      (letrec-expression-procedure-variables e)
			      (letrec-expression-lambda-expressions e)))
		bs2)
	p?
	p1?)
       (let loop ((i i)
		  (xs (letrec-expression-procedure-variables e))
		  (es (letrec-expression-lambda-expressions e))
		  (bs2 bs2))
	(if (null? xs)
	    (anf-convert-expression
	     i (letrec-expression-body e) bs1 bs2 p? p1?)
	    (let* ((result1 (anf-convert-parameter
			     i (lambda-expression-parameter (first es)) p?))
		   (result2
		    (anf-convert-expression (first result1)
					    (lambda-expression-body (first es))
					    '()
					    '()
					    p?
					    p1?)))
	     (loop
	      (first result2)
	      (rest xs)
	      (rest es)
	      (cons
	       (make-variable-binding
		(first xs)
		(link-inverses
		 (new-lambda-expression (second result1) (anf-result result2))
		 (first es)))
	       bs2)))))))
  ((cons-expression? e)
   (let* ((result1
	   (anf-convert-expression i (cons-expression-car e) bs1 bs2 p? p1?))
	  (result2 (anf-convert-expression (first result1)
					   (cons-expression-cdr e)
					   (third result1)
					   (fourth result1)
					   p?
					   p1?))
	  (i (+ (first result2) 1))
	  (p (new-variable-access-expression (anfify i))))
    ;; result
    (list i
	  p
	  (cons (make-parameter-binding
		 p
		 (new-cons-expression
		  (cons-expression-tags e) (second result1) (second result2)))
		(third result2))
	  (fourth result2))))
  (else (internal-error))))

(define (anf-convert-reuse p i e bs1 bs2 p? p1?)
 ;; needs work: Should have structure instead of list.
 (cond
  ((constant-expression? e)
   ;; result
   (list i p (cons (make-parameter-binding p e) bs1) bs2))
  ((variable-access-expression? e)
   ;; There is copying here, since both names might be used.
   ;; result
   (list i p (cons (make-parameter-binding p e) bs1) bs2))
  ((lambda-expression? e)
   (if p1?
       ;; There is copying here, since both names might be used.
       ;; result
       (list i p (cons (make-parameter-binding p e) bs1) bs2)
       (let* ((result1
	       (anf-convert-parameter i (lambda-expression-parameter e) p?))
	      (result2 (anf-convert-expression (first result1)
					       (lambda-expression-body e)
					       '()
					       '()
					       p?
					       p1?)))
	;; result
	(list
	 (first result2)
	 p
	 (cons (make-parameter-binding
		p
		(link-inverses
		 (new-lambda-expression (second result1) (anf-result result2))
		 e))
	       bs1)
	 bs2))))
  ((let*? e)
   (let* ((result1 (anf-convert-parameter
		    i (lambda-expression-parameter (application-callee e)) p?))
	  (result2 (anf-convert-reuse (second result1)
				      (first result1)
				      (application-argument e)
				      bs1
				      bs2
				      p?
				      p1?)))
    (anf-convert-expression
     (first result2)
     (lambda-expression-body (application-callee e))
     ;; There is copying here, since both names might be used.
     (cons (make-parameter-binding p (second result1))
	   (cons (make-parameter-binding (second result1) (second result2))
		 (third result2)))
     (fourth result2)
     p?
     p1?)))
  ((application? e)
   (let* ((result1
	   (anf-convert-expression i (application-callee e) bs1 bs2 p? p1?))
	  (result2 (anf-convert-expression (first result1)
					   (application-argument e)
					   (third result1)
					   (fourth result1)
					   p?
					   p1?)))
    ;; result
    (list
     (first result2)
     p
     (cons (make-parameter-binding
	    p (new-application (second result1) (second result2)))
	   (third result2))
     (fourth result2))))
  ((letrec-expression? e)
   (if p1?
       (anf-convert-expression
	i
	(letrec-expression-body e)
	bs1
	(append (reverse (map make-variable-binding
			      (letrec-expression-procedure-variables e)
			      (letrec-expression-lambda-expressions e)))
		bs2)
	p?
	p1?)
       (let loop ((i i)
		  (xs (letrec-expression-procedure-variables e))
		  (es (letrec-expression-lambda-expressions e))
		  (bs2 bs2))
	(if (null? xs)
	    (anf-convert-expression
	     i (letrec-expression-body e) bs1 bs2 p? p1?)
	    (let* ((result1 (anf-convert-parameter
			     i (lambda-expression-parameter (first es)) p?))
		   (result2
		    (anf-convert-expression (first result1)
					    (lambda-expression-body (first es))
					    '()
					    '()
					    p?
					    p1?)))
	     (loop
	      (first result2)
	      (rest xs)
	      (rest es)
	      (cons
	       (make-variable-binding
		(first xs)
		(link-inverses
		 (new-lambda-expression (second result1) (anf-result result2))
		 (first es)))
	       bs2)))))))
  ((cons-expression? e)
   (let* ((result1
	   (anf-convert-expression i (cons-expression-car e) bs1 bs2 p? p1?))
	  (result2 (anf-convert-expression (first result1)
					   (cons-expression-cdr e)
					   (third result1)
					   (fourth result1)
					   p?
					   p1?)))
    ;; result
    (list (first result2)
	  p
	  (cons (make-parameter-binding
		 p
		 (new-cons-expression
		  (cons-expression-tags e) (second result1) (second result2)))
		(third result2))
	  (fourth result2))))
  (else (internal-error))))

(define (anf-convert e)
 (anf-result (anf-convert-expression (anf-max e) e '() '() #f #f)))

(define (anf-convert-lambda-expression e)
 (let* ((result1 (anf-convert-parameter
		  (anf-max e) (lambda-expression-parameter e) #f))
	(result2 (anf-convert-expression
		  (first result1) (lambda-expression-body e) '() '() #f #f)))
  (link-inverses
   (new-lambda-expression (second result1) (anf-result result2)) e)))

(define (anf-convert-lambda-expression-shallow e)
 (link-inverses
  (new-lambda-expression
   (lambda-expression-parameter e)
   (anf-result (anf-convert-expression
		(anf-max e) (lambda-expression-body e) '() '() #t #t)))
  e))

(define (anf-convert-lambda-expression-for-reverse e)
 (link-inverses
  (new-lambda-expression
   (lambda-expression-parameter e)
   (anf-result (anf-convert-expression
		(anf-max e) (lambda-expression-body e) '() '() #t #f)))
  e))

(define (anf-let*-parameters e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-parameters (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-parameters e) '())))

(define (anf-let*-expressions e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-expressions (letrec-expression-body e))
	 '())
     (if (let*? e) (let*-expressions e) '())))

(define (anf-parameter e)
 (if (letrec-expression? e)
     (if (let*? (letrec-expression-body e))
	 (let*-body (letrec-expression-body e))
	 (letrec-expression-body e))
     (if (let*? e) (let*-body e) e)))

;;; Concrete->Abstract

(define (value? v)
 (or (null? v)
     (boolean? v)
     (real? v)
     (and *wizard?*
	  (perturbation-tagged-value? v)
	  (value? (get-perturbation-tagged-value-primal v)))
     (and *wizard?*
	  (bundle? v)
	  (value? (get-bundle-primal v))
	  (value? (get-bundle-tangent v)))
     (and *wizard?*
	  (sensitivity-tagged-value? v)
	  (value? (get-sensitivity-tagged-value-primal v)))
     (and *wizard?*
	  (reverse-tagged-value? v)
	  (value? (get-reverse-tagged-value-primal v)))
     (and (pair? v) (value? (car v)) (value? (cdr v)))))

(define (internalize v)
 (cond
  ((null? v) (vlad-empty-list))
  ((boolean? v) (if v (vlad-true) (vlad-false)))
  ((real? v) v)
  ((perturbation-tagged-value? v)
   (new-perturbation-tagged-value
    (internalize (get-perturbation-tagged-value-primal v))))
  ((bundle? v)
   (new-bundle
    (internalize (get-bundle-primal v)) (internalize (get-bundle-tangent v))))
  ((sensitivity-tagged-value? v)
   (new-sensitivity-tagged-value
    (internalize (get-sensitivity-tagged-value-primal v))))
  ((reverse-tagged-value? v)
   (new-reverse-tagged-value
    (internalize (get-reverse-tagged-value-primal v))))
  ((pair? v) (vlad-cons (internalize (car v)) (internalize (cdr v))))
  (else (internal-error))))

;;; needs work: To add perturb, bundle, sensitize, and *j parameters.

(define (syntax-check-parameter! p)
 (cond
  ((boolean? p) (syntax-check-parameter! `',p))
  ((real? p) (syntax-check-parameter! `',p))
  ((concrete-variable? p)
   (unless (or (concrete-user-variable? p) *wizard?*)
    (compile-time-error "Invalid parameter: ~s" p))
   #f)
  ((and (list? p) (not (null? p)))
   (case (first p)
    ((quote) (unless (and (= (length p) 2) (value? (second p)))
	      (compile-time-error "Invalid parameter: ~s" p))
	     #f)
    ((cons)
     (unless (= (length p) 3) (compile-time-error "Invalid parameter: ~s" p))
     (syntax-check-parameter! (second p))
     (syntax-check-parameter! (third p)))
    ((cons*) (syntax-check-parameter! (macro-expand p)))
    ((list) (syntax-check-parameter! (macro-expand p)))
    (else (compile-time-error "Invalid parameter: ~s" p))))
  (else (compile-time-error "Invalid parameter: ~s" p))))

(define (macro-expand e)
 (if (and (list? e) (not (null? e)))
     (case (first e)
      ((lambda) (unless (and (= (length e) 3) (list? (second e)))
		 (compile-time-error "Invalid expression: ~s" e))
		(case (length (second e))
		 ((0) `(lambda ((cons* ,@(second e))) ,(third e)))
		 ((1) e)
		 (else `(lambda ((cons* ,@(second e))) ,(third e)))))
      ((let) (unless (and (= (length e) 3)
			  (list? (second e))
			  (every (lambda (b) (and (list? b) (= (length b) 2)))
				 (second e)))
	      (compile-time-error "Invalid expression: ~s" e))
	     `((lambda ,(map first (second e)) ,(third e))
	       ,@(map second (second e))))
      ((let*)
       (unless (and (= (length e) 3)
		    (list? (second e))
		    (every (lambda (b) (and (list? b) (= (length b) 2)))
			   (second e)))
	(compile-time-error "Invalid expression: ~s" e))
       (case (length (second e))
	((0) (third e))
	((1) `(let ,(second e) ,(third e)))
	(else
	 `(let (,(first (second e))) (let* ,(rest (second e)) ,(third e))))))
      ((if)
       (unless (= (length e) 4)
	(compile-time-error "Invalid expression: ~s" e))
       ;; needs work: To ensure that you don't shadow if-procedure.
       `(if-procedure
	 ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))
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
	       (compile-time-error "Invalid expression: ~s" e))
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
	     (else
	      (let ((x (gensym)))
	       `(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e)))))))))
      (else (case (length (rest e))
	     ((0) `(,(first e) (cons* ,@(rest e))))
	     ((1) e)
	     (else `(,(first e) (cons* ,@(rest e)))))))
     e))

(define (syntax-check-expression! e)
 (let loop ((e e) (xs (map value-binding-variable *value-bindings*)))
  (cond
   ((boolean? e) (loop `',e xs))
   ((real? e) (loop `',e xs))
   ((concrete-variable? e)
    (unless (memp variable=? (new-variable e) xs)
     (compile-time-error "Unbound variable: ~s" e))
    #f)
   ((and (list? e) (not (null? e)))
    (case (first e)
     ((quote) (unless (and (= (length e) 2) (value? (second e)))
	       (compile-time-error "Invalid expression: ~s" e))
	      #f)
     ((lambda)
      (unless (and (= (length e) 3) (list? (second e)))
       (compile-time-error "Invalid expression: ~s" e))
      (case (length (second e))
       ((0) (loop (macro-expand e) xs))
       ((1) (syntax-check-parameter! (first (second e)))
	    (let ((xs0 (parameter-variables
			(internalize-expression (first (second e))))))
	     (when (duplicatesp? variable=? xs0)
	      (compile-time-error "Duplicate variables: ~s" e))
	     (loop (third e) (append xs0 xs))))
       (else (loop (macro-expand e) xs))))
     ((letrec)
      (unless (and (= (length e) 3)
		   (list? (second e))
		   (every
		    (lambda (b)
		     (and (list? b)
			  (= (length b) 2) (concrete-variable? (first b))))
		    (second e)))
       (compile-time-error "Invalid expression: ~s" e))
      (let ((xs0 (map (lambda (b) (new-variable (first b))) (second e))))
       (when (duplicatesp? variable=? xs0)
	(compile-time-error "Duplicate variables: ~s" e))
       (for-each
	(lambda (b)
	 (let ((e1 (macro-expand (second b))))
	  (unless (and (list? e1) (= (length e1) 3) (eq? (first e1) 'lambda))
	   (compile-time-error "Invalid expression: ~s" e))
	  (loop e1 (append xs0 xs))))
	(second e))
       (loop (third e) (append xs0 xs))))
     ((let) (loop (macro-expand e) xs))
     ((let*) (loop (macro-expand e) xs))
     ((if) (loop (macro-expand e) xs))
     ((cons)
      (unless (= (length e) 3) (compile-time-error "Invalid expression: ~s" e))
      (loop (second e) xs)
      (loop (third e) xs))
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
   (else (compile-time-error "Invalid expression: ~s" e)))))

(define (internalize-expression e)
 (cond
  ((boolean? e) (internalize-expression `',e))
  ((real? e) (internalize-expression `',e))
  ((concrete-variable? e) (new-variable-access-expression (new-variable e)))
  ((and (list? e) (not (null? e)))
   (case (first e)
    ((quote) (new-constant-expression (internalize (second e))))
    ((lambda)
     (case (length (second e))
      ((0) (internalize-expression (macro-expand e)))
      ((1) (new-lambda-expression (internalize-expression (first (second e)))
				  (internalize-expression (third e))))
      (else (internalize-expression (macro-expand e)))))
    ((letrec)
     (create-letrec-expression
      (map (lambda (b) (new-variable (first b))) (second e))
      (map (lambda (b) (internalize-expression (macro-expand (second b))))
	   (second e))
      (internalize-expression (third e))))
    ((let) (internalize-expression (macro-expand e)))
    ((let*) (internalize-expression (macro-expand e)))
    ((if) (internalize-expression (macro-expand e)))
    ((cons) (create-cons-expression (internalize-expression (second e))
				    (internalize-expression (third e))))
    ((cons*) (internalize-expression (macro-expand e)))
    ((list) (internalize-expression (macro-expand e)))
    ((cond) (internalize-expression (macro-expand e)))
    ((and) (internalize-expression (macro-expand e)))
    ((or) (internalize-expression (macro-expand e)))
    (else (case (length (rest e))
	   ((0) (internalize-expression (macro-expand e)))
	   ((1) (new-application (internalize-expression (first e))
				 (internalize-expression (second e))))
	   (else (internalize-expression (macro-expand e)))))))
  (else (internal-error))))

(define (parse e)
 (let ((e (anf-convert (alpha-convert (internalize-expression e)))))
  (list e
	(map (lambda (x)
	      (find-if (lambda (b) (variable=? x (value-binding-variable b)))
		       *value-bindings*))
	     (free-variables e)))))

;;; AD

(define (zero v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  8
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v0 cs) v0)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v0 (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v)
		 (cons (cons v v0) cs)
		 (lambda (us0 cs)
		  (fill-union-values! v0 us0)
		  (k v0 cs)))))
      ((vlad-empty-list? v) (k v cs))
      ((vlad-true? v) (k v cs))
      ((vlad-false? v) (k v cs))
      ((vlad-real? v) (k 0 cs))
      ((primitive-procedure? v) (k v cs))
      ((nonrecursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u0 (make-nonrecursive-closure
		  'unfilled
		  (nonrecursive-closure-lambda-expression v)
		  #f
		  #f
		  #f
		  #f
		  #f
		  'unfilled)))
	(map-cps loop
		 (get-nonrecursive-closure-values v)
		 (cons (cons v u0) cs)
		 (lambda (vs0 cs)
		  (fill-nonrecursive-closure-values! u0 vs0)
		  (k u0 cs)))))
      ((recursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u0 (make-recursive-closure
		  'unfilled
		  (recursive-closure-procedure-variables v)
		  (recursive-closure-lambda-expressions v)
		  (recursive-closure-index v)
		  #f
		  #f
		  #f
		  #f
		  #f
		  'unfilled)))
	(map-cps loop
		 (get-recursive-closure-values v)
		 (cons (cons v u0) cs)
		 (lambda (vs0 cs)
		  (fill-recursive-closure-values! u0 vs0)
		  (k u0 cs)))))
      ((perturbation-tagged-value? v)
       (let ((u0 (make-perturbation-tagged-value
		  'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-perturbation-tagged-value-primal v)
	      (cons (cons v u0) cs)
	      (lambda (v0 cs)
	       (fill-perturbation-tagged-value-primal! u0 v0)
	       (k u0 cs)))))
      ((bundle? v)
       (let ((u0 (make-bundle 'unfilled 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-bundle-primal v)
	      (cons (cons v u0) cs)
	      (lambda (v0-primal cs)
	       (loop (get-bundle-tangent v)
		     cs
		     (lambda (v0-tangent cs)
		      (fill-bundle! u0 v0-primal v0-tangent)
		      (k u0 cs)))))))
      ((sensitivity-tagged-value? v)
       (let ((u0 (make-sensitivity-tagged-value
		  'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-sensitivity-tagged-value-primal v)
	      (cons (cons v u0) cs)
	      (lambda (v0 cs)
	       (fill-sensitivity-tagged-value-primal! u0 v0)
	       (k u0 cs)))))
      ((reverse-tagged-value? v)
       (let ((u0
	      (make-reverse-tagged-value 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-reverse-tagged-value-primal v)
	      (cons (cons v u0) cs)
	      (lambda (v0 cs)
	       (fill-reverse-tagged-value-primal! u0 v0)
	       (k u0 cs)))))
      ((tagged-pair? v)
       (let ((u0 (make-tagged-pair (tagged-pair-tags v)
				   'unfilled
				   'unfilled
				   #f
				   #f
				   #f
				   #f
				   #f
				   'unfilled)))
	(loop (get-tagged-pair-car v)
	      (cons (cons v u0) cs)
	      (lambda (v0-car cs)
	       (loop (get-tagged-pair-cdr v)
		     cs
		     (lambda (v0-cdr cs)
		      (fill-tagged-pair! u0 v0-car v0-cdr)
		      (k u0 cs)))))))
      (else (internal-error))))))))

;;; Forward Mode

(define (perturbation-transform e)
 (define (loop e)
  (cond ((constant-expression? e)
	 (without-abstract
	  (lambda ()
	   (new-constant-expression (perturb (constant-expression-value e))))))
	((variable-access-expression? e) (perturbationify-access e))
	((lambda-expression? e) (perturbation-transform e))
	((application? e)
	 (new-application (loop (application-callee e))
			  (loop (application-argument e))))
	((letrec-expression? e)
	 (new-letrec-expression
	  (map perturbationify (letrec-expression-procedure-variables e))
	  (map loop (letrec-expression-lambda-expressions e))
	  (loop (letrec-expression-body e))))
	((cons-expression? e)
	 (new-cons-expression (add-tag 'perturbation (cons-expression-tags e))
			      (loop (cons-expression-car e))
			      (loop (cons-expression-cdr e))))
	(else (internal-error))))
 (assert (lambda-expression? e))
 (if (lambda-expression-perturbation-transform e)
     (lambda-expression-perturbation-transform e)
     (let ((e1 (new-lambda-expression (loop (lambda-expression-parameter e))
				      (loop (lambda-expression-body e)))))
      (assert
       (and (not (lambda-expression-perturbation-transform e))
	    (not (lambda-expression-perturbation-transform-inverse e1))))
      (set-lambda-expression-perturbation-transform! e e1)
      (set-lambda-expression-perturbation-transform-inverse! e1 e)
      e1)))

(define (perturbation-transform-inverse e)
 (assert (and (lambda-expression? e)
	      (lambda-expression-perturbation-transform-inverse e)))
 (lambda-expression-perturbation-transform-inverse e))

(define (forward-transform e)
 (define (loop e)
  (cond
   ((constant-expression? e)
    (without-abstract
     (lambda () (new-constant-expression (j* (constant-expression-value e))))))
   ((variable-access-expression? e) (forwardify-access e))
   ((lambda-expression? e) (forward-transform e))
   ((application? e)
    (new-application (loop (application-callee e))
		     (loop (application-argument e))))
   ((letrec-expression? e)
    (new-letrec-expression
     (map forwardify (letrec-expression-procedure-variables e))
     (map loop (letrec-expression-lambda-expressions e))
     (loop (letrec-expression-body e))))
   ((cons-expression? e)
    (new-cons-expression (add-tag 'forward (cons-expression-tags e))
			 (loop (cons-expression-car e))
			 (loop (cons-expression-cdr e))))
   (else (internal-error))))
 (assert (lambda-expression? e))
 (if (lambda-expression-forward-transform e)
     (lambda-expression-forward-transform e)
     (let ((e1 (new-lambda-expression (loop (lambda-expression-parameter e))
				      (loop (lambda-expression-body e)))))
      (assert (and (not (lambda-expression-forward-transform e))
		   (not (lambda-expression-forward-transform-inverse e1))))
      (set-lambda-expression-forward-transform! e e1)
      (set-lambda-expression-forward-transform-inverse! e1 e)
      e1)))

(define (forward-transform-inverse e)
 (assert (and (lambda-expression? e)
	      (lambda-expression-forward-transform-inverse e)))
 (lambda-expression-forward-transform-inverse e))

(define (perturb v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  9
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v-perturbation cs) v-perturbation)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v-perturbation (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v)
		 (cons (cons v v-perturbation) cs)
		 (lambda (us-perturbation cs)
		  (fill-union-values! v-perturbation us-perturbation)
		  (k v-perturbation cs)))))
      ((vlad-empty-list? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((vlad-true? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((vlad-false? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((vlad-real? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((primitive-procedure? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((nonrecursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-perturbation (make-nonrecursive-closure
			      'unfilled
			      (perturbation-transform
			       (nonrecursive-closure-lambda-expression v))
			      #f
			      #f
			      #f
			      #f
			      #f
			      'unfilled)))
	(map-cps
	 loop
	 (get-nonrecursive-closure-values v)
	 (cons (cons v u-perturbation) cs)
	 (lambda (vs-perturbation cs)
	  (fill-nonrecursive-closure-values! u-perturbation vs-perturbation)
	  (k u-perturbation cs)))))
      ((recursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-perturbation
	      (make-recursive-closure
	       'unfilled
	       (map-vector perturbationify
			   (recursive-closure-procedure-variables v))
	       (map-vector perturbation-transform
			   (recursive-closure-lambda-expressions v))
	       (recursive-closure-index v)
	       #f
	       #f
	       #f
	       #f
	       #f
	       'unfilled)))
	(map-cps
	 loop
	 (get-recursive-closure-values v)
	 (cons (cons v u-perturbation) cs)
	 (lambda (vs-perturbation cs)
	  (fill-recursive-closure-values! u-perturbation vs-perturbation)
	  (k u-perturbation cs)))))
      ((perturbation-tagged-value? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((bundle? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((sensitivity-tagged-value? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((reverse-tagged-value? v)
       (let ((u-perturbation (create-perturbation-tagged-value v)))
	(k u-perturbation (cons (cons v u-perturbation) cs))))
      ((tagged-pair? v)
       (let ((u-perturbation
	      (make-tagged-pair (add-tag 'perturbation (tagged-pair-tags v))
				'unfilled
				'unfilled
				#f
				#f
				#f
				#f
				#f
				'unfilled)))
	(loop (get-tagged-pair-car v)
	      (cons (cons v u-perturbation) cs)
	      (lambda (v-car-perturbation cs)
	       (loop (get-tagged-pair-cdr v)
		     cs
		     (lambda (v-cdr-perturbation cs)
		      (fill-tagged-pair!
		       u-perturbation v-car-perturbation v-cdr-perturbation)
		      (k u-perturbation cs)))))))
      (else (internal-error))))))))

(define (unperturb v-perturbation)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  10
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v-perturbation v-perturbation) (cs '()) (k (lambda (v cs) v)))
    (let ((found? (assq v-perturbation cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v-perturbation)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v-perturbation)
		 (cons (cons v-perturbation v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      ((vlad-empty-list? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((vlad-true? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((vlad-false? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((vlad-real? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((primitive-procedure? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((nonrecursive-closure? v-perturbation)
       (if (tagged? 'perturbation (nonrecursive-closure-tags v-perturbation))
	   ;; See the note in abstract-environment=?.
	   (let ((u (make-nonrecursive-closure
		     'unfilled
		     (perturbation-transform-inverse
		      (nonrecursive-closure-lambda-expression
		       v-perturbation))
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (map-cps loop
		     (get-nonrecursive-closure-values v-perturbation)
		     (cons (cons v-perturbation u) cs)
		     (lambda (vs cs)
		      (fill-nonrecursive-closure-values! u vs)
		      (k u cs))))
	   (let ((u (ad-error
		     "Argument to unperturb ~a a non-perturbation value"
		     v-perturbation)))
	    (k u (cons (cons v-perturbation u) cs)))))
      ((recursive-closure? v-perturbation)
       (if (tagged? 'perturbation (recursive-closure-tags v-perturbation))
	   ;; See the note in abstract-environment=?.
	   (let ((u (make-recursive-closure
		     'unfilled
		     (map-vector
		      unperturbationify
		      (recursive-closure-procedure-variables v-perturbation))
		     (map-vector
		      perturbation-transform-inverse
		      (recursive-closure-lambda-expressions v-perturbation))
		     (recursive-closure-index v-perturbation)
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (map-cps loop
		     (get-recursive-closure-values v-perturbation)
		     (cons (cons v-perturbation u) cs)
		     (lambda (vs cs)
		      (fill-recursive-closure-values! u vs)
		      (k u cs))))
	   (let ((u (ad-error
		     "Argument to unperturb ~a a non-perturbation value"
		     v-perturbation)))
	    (k u (cons (cons v-perturbation u) cs)))))
      ((perturbation-tagged-value? v-perturbation)
       (let ((u (get-perturbation-tagged-value-primal v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((bundle? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((sensitivity-tagged-value? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((reverse-tagged-value? v-perturbation)
       (let ((u (ad-error "Argument to unperturb ~a a non-perturbation value"
			  v-perturbation)))
	(k u (cons (cons v-perturbation u) cs))))
      ((tagged-pair? v-perturbation)
       (if (tagged? 'perturbation (tagged-pair-tags v-perturbation))
	   (let ((u (make-tagged-pair
		     (remove-tag 'perturbation
				 (tagged-pair-tags v-perturbation))
		     'unfilled
		     'unfilled
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (loop (get-tagged-pair-car v-perturbation)
		  (cons (cons v-perturbation u) cs)
		  (lambda (v-car cs)
		   (loop (get-tagged-pair-cdr v-perturbation)
			 cs
			 (lambda (v-cdr cs)
			  (fill-tagged-pair! u v-car v-cdr)
			  (k u cs))))))
	   (let ((u (ad-error
		     "Argument to unperturb ~a a non-perturbation value"
		     v-perturbation)))
	    (k u (cons (cons v-perturbation u) cs)))))
      (else (internal-error))))))))

(define (primal v-forward)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  11
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v-forward v-forward) (cs '()) (k (lambda (v cs) v)))
    (let ((found? (assq v-forward cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v-forward)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v-forward)
		 (cons (cons v-forward v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      (else
       (let ((b (find-if
		 (lambda (b)
		  ;; This is safe because the arguments will never have
		  ;; unfilled values.
		  (deep-abstract-value=?
		   v-forward
		   (primitive-procedure-forward (value-binding-value b))))
		 *value-bindings*)))
	(if b
	    (let ((u (value-binding-value b)))
	     (k u (cons (cons v-forward u) cs)))
	    (cond
	     ((vlad-empty-list? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((vlad-true? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((vlad-false? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((vlad-real? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((primitive-procedure? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((nonrecursive-closure? v-forward)
	      (if (tagged? 'forward (nonrecursive-closure-tags v-forward))
		  ;; See the note in abstract-environment=?.
		  (let ((u (make-nonrecursive-closure
			    'unfilled
			    (forward-transform-inverse
			     (nonrecursive-closure-lambda-expression
			      v-forward))
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled)))
		   (map-cps loop
			    (get-nonrecursive-closure-values v-forward)
			    (cons (cons v-forward u) cs)
			    (lambda (vs cs)
			     (fill-nonrecursive-closure-values! u vs)
			     (k u cs))))
		  (let ((u (ad-error "Argument to primal ~a a non-forward value"
				     v-forward)))
		   (k u (cons (cons v-forward u) cs)))))
	     ((recursive-closure? v-forward)
	      (if (tagged? 'forward (recursive-closure-tags v-forward))
		  ;; See the note in abstract-environment=?.
		  (let ((u (make-recursive-closure
			    'unfilled
			    (map-vector
			     unforwardify
			     (recursive-closure-procedure-variables v-forward))
			    (map-vector
			     forward-transform-inverse
			     (recursive-closure-lambda-expressions v-forward))
			    (recursive-closure-index v-forward)
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled)))
		   (map-cps loop
			    (get-recursive-closure-values v-forward)
			    (cons (cons v-forward u) cs)
			    (lambda (vs cs)
			     (fill-recursive-closure-values! u vs)
			     (k u cs))))
		  (let ((u (ad-error "Argument to primal ~a a non-forward value"
				     v-forward)))
		   (k u (cons (cons v-forward u) cs)))))
	     ((perturbation-tagged-value? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((bundle? v-forward)
	      (let ((u (get-bundle-primal v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((sensitivity-tagged-value? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((reverse-tagged-value? v-forward)
	      (let ((u (ad-error "Argument to primal ~a a non-forward value"
				 v-forward)))
	       (k u (cons (cons v-forward u) cs))))
	     ((tagged-pair? v-forward)
	      (if (tagged? 'forward (tagged-pair-tags v-forward))
		  (let ((u (make-tagged-pair
			    (remove-tag 'forward (tagged-pair-tags v-forward))
			    'unfilled
			    'unfilled
			    #f
			    #f
			    #f
			    #f
			    #f 'unfilled)))
		   (loop (get-tagged-pair-car v-forward)
			 (cons (cons v-forward u) cs)
			 (lambda (v-car cs)
			  (loop (get-tagged-pair-cdr v-forward)
				cs
				(lambda (v-cdr cs)
				 (fill-tagged-pair! u v-car v-cdr)
				 (k u cs))))))
		  (let ((u (ad-error "Argument to primal ~a a non-forward value"
				     v-forward)))
		   (k u (cons (cons v-forward u) cs)))))
	     (else (internal-error))))))))))))

(define (tangent v-forward)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  12
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v-forward v-forward)
	      (cs '())
	      (k (lambda (v-perturbation cs) v-perturbation)))
    (let ((found? (assq v-forward cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v-forward)
       (let ((v-perturbation (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v-forward)
		 (cons (cons v-forward v-perturbation) cs)
		 (lambda (us-perturbation cs)
		  (fill-union-values! v-perturbation us-perturbation)
		  (k v-perturbation cs)))))
      (else
       (let ((b (find-if
		 (lambda (b)
		  ;; This is safe because the arguments will never have
		  ;; unfilled values.
		  (deep-abstract-value=?
		   v-forward
		   (primitive-procedure-forward (value-binding-value b))))
		 *value-bindings*)))
	(if b
	    (let ((u-perturbation (perturb (value-binding-value b))))
	     (k u-perturbation (cons (cons v-forward u-perturbation) cs)))
	    (cond
	     ((vlad-empty-list? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((vlad-true? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((vlad-false? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((vlad-real? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((primitive-procedure? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((nonrecursive-closure? v-forward)
	      (if (tagged? 'forward (nonrecursive-closure-tags v-forward))
		  ;; See the note in abstract-environment=?.
		  (let ((u-perturbation
			 (make-nonrecursive-closure
			  'unfilled
			  (perturbation-transform
			   (forward-transform-inverse
			    (nonrecursive-closure-lambda-expression
			     v-forward)))
			  #f
			  #f
			  #f
			  #f
			  #f
			  'unfilled)))
		   (map-cps loop
			    (get-nonrecursive-closure-values v-forward)
			    (cons (cons v-forward u-perturbation) cs)
			    (lambda (vs-perturbation cs)
			     (fill-nonrecursive-closure-values!
			      u-perturbation vs-perturbation)
			     (k u-perturbation cs))))
		  (let ((u-perturbation
			 (ad-error "Argument to tangent ~a a non-forward value"
				   v-forward)))
		   (k u-perturbation
		      (cons (cons v-forward u-perturbation) cs)))))
	     ((recursive-closure? v-forward)
	      (if (tagged? 'forward (recursive-closure-tags v-forward))
		  ;; See the note in abstract-environment=?.
		  (let ((u-perturbation
			 (make-recursive-closure
			  'unfilled
			  (map-vector
			   (lambda (x) (perturbationify (unforwardify x)))
			   (recursive-closure-procedure-variables v-forward))
			  (map-vector
			   (lambda (e)
			    (perturbation-transform
			     (forward-transform-inverse e)))
			   (recursive-closure-lambda-expressions v-forward))
			  (recursive-closure-index v-forward)
			  #f
			  #f
			  #f
			  #f
			  #f
			  'unfilled)))
		   (map-cps loop
			    (get-recursive-closure-values v-forward)
			    (cons (cons v-forward u-perturbation) cs)
			    (lambda (vs-perturbation cs)
			     (fill-recursive-closure-values!
			      u-perturbation vs-perturbation)
			     (k u-perturbation cs))))
		  (let ((u-perturbation
			 (ad-error "Argument to tangent ~a a non-forward value"
				   v-forward)))
		   (k u-perturbation
		      (cons (cons v-forward u-perturbation) cs)))))
	     ((perturbation-tagged-value? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((bundle? v-forward)
	      (let ((u-perturbation (get-bundle-tangent v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((sensitivity-tagged-value? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((reverse-tagged-value? v-forward)
	      (let ((u-perturbation
		     (ad-error "Argument to tangent ~a a non-forward value"
			       v-forward)))
	       (k u-perturbation (cons (cons v-forward u-perturbation) cs))))
	     ((tagged-pair? v-forward)
	      (if (tagged? 'forward (tagged-pair-tags v-forward))
		  (let ((u-perturbation
			 (make-tagged-pair
			  (add-tag
			   'perturbation
			   (remove-tag 'forward (tagged-pair-tags v-forward)))
			  'unfilled
			  'unfilled
			  #f
			  #f
			  #f
			  #f
			  #f
			  'unfilled)))
		   (loop (get-tagged-pair-car v-forward)
			 (cons (cons v-forward u-perturbation) cs)
			 (lambda (v-car-perturbation cs)
			  (loop (get-tagged-pair-cdr v-forward)
				cs
				(lambda (v-cdr-perturbation cs)
				 (fill-tagged-pair! u-perturbation
						    v-car-perturbation
						    v-cdr-perturbation)
				 (k u-perturbation cs))))))
		  (let ((u-perturbation
			 (ad-error "Argument to tangent ~a a non-forward value"
				   v-forward)))
		   (k u-perturbation
		      (cons (cons v-forward u-perturbation) cs)))))
	     (else (internal-error))))))))))))

(define (bundle v v-perturbation)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  13
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v)
	      (v-perturbation v-perturbation)
	      (cs '())
	      (k (lambda (v-forward cs) v-forward)))
    (let ((found? (find-if (lambda (c)
			    (and (eq? (car (car c)) v)
				 (eq? (cdr (car c)) v-perturbation)))
			   cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v-forward (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps (lambda (u cs k) (loop u v-perturbation cs k))
		 (union-members v)
		 (cons (cons (cons v v-perturbation) v-forward) cs)
		 (lambda (us-forward cs)
		  (fill-union-values! v-forward us-forward)
		  (k v-forward cs)))))
      ((union? v-perturbation)
       (let ((v-forward (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps (lambda (u-perturbation cs k) (loop v u-perturbation cs k))
		 (union-members v-perturbation)
		 (cons (cons (cons v v-perturbation) v-forward) cs)
		 (lambda (us-forward cs)
		  (fill-union-values! v-forward us-forward)
		  (k v-forward cs)))))
      (else
       (let ((b (find-if
		 ;; This is safe because the arguments will never have
		 ;; unfilled values.
		 (lambda (b) (deep-abstract-value=? v (value-binding-value b)))
		 *value-bindings*)))
	(if b
	    (cond
	     ((some-bundlable? v v-perturbation)
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward
		     (primitive-procedure-forward (value-binding-value b))))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     (else
	      (if *abstract?*
		  (let ((u-forward (compile-time-warning
				    "Arguments to bundle might not conform"
				    v
				    v-perturbation)))
		   (k u-forward
		      (cons (cons (cons v v-perturbation) u-forward) cs)))
		  (run-time-error "Arguments to bundle do not conform"
				  v
				  v-perturbation))))
	    (cond
	     ((and (vlad-empty-list? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (vlad-true? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (vlad-false? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (vlad-real? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((primitive-procedure? v) (internal-error))
	     ((and (nonrecursive-closure? v)
		   (nonrecursive-closure? v-perturbation)
		   (perturbation-parameter?
		    (nonrecursive-closure-parameter v-perturbation))
		   (dereferenced-nonrecursive-closure-match?
		    v (unperturb v-perturbation)))
	      ;; See the note in abstract-environment=?.
	      (let ((u-forward (make-nonrecursive-closure
				'unfilled
				(forward-transform
				 (nonrecursive-closure-lambda-expression v))
				#f
				#f
				#f
				#f
				#f
				'unfilled)))
	       (map2-cps
		loop
		(get-nonrecursive-closure-values v)
		(get-nonrecursive-closure-values v-perturbation)
		(cons (cons (cons v v-perturbation) u-forward) cs)
		(lambda (vs-forward cs)
		 (fill-nonrecursive-closure-values! u-forward vs-forward)
		 (k u-forward cs)))))
	     ((and (recursive-closure? v)
		   (recursive-closure? v-perturbation)
		   (perturbation-parameter?
		    (recursive-closure-parameter v-perturbation))
		   (dereferenced-recursive-closure-match?
		    v (unperturb v-perturbation)))
	      ;; See the note in abstract-environment=?.
	      (let ((u-forward
		     (make-recursive-closure
		      'unfilled
		      (map-vector forwardify
				  (recursive-closure-procedure-variables v))
		      (map-vector forward-transform
				  (recursive-closure-lambda-expressions v))
		      (recursive-closure-index v)
		      #f
		      #f
		      #f
		      #f
		      #f
		      'unfilled)))
	       (map2-cps loop
			 (get-recursive-closure-values v)
			 (get-recursive-closure-values v-perturbation)
			 (cons (cons (cons v v-perturbation) u-forward) cs)
			 (lambda (vs-forward cs)
			  (fill-recursive-closure-values! u-forward vs-forward)
			  (k u-forward cs)))))
	     ((and (perturbation-tagged-value? v)
		   (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (bundle? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (sensitivity-tagged-value? v)
		   (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (reverse-tagged-value? v) (some-bundlable? v v-perturbation))
	      (unless (every-bundlable? v v-perturbation)
	       (compile-time-warning
		"Arguments to bundle might not conform" v v-perturbation))
	      (let ((u-forward (create-bundle v v-perturbation)))
	       (k u-forward
		  (cons (cons (cons v v-perturbation) u-forward) cs))))
	     ((and (tagged-pair? v)
		   (tagged-pair? v-perturbation)
		   (tagged? 'perturbation (tagged-pair-tags v-perturbation))
		   (equal-tags?
		    (tagged-pair-tags v)
		    (remove-tag
		     'perturbation (tagged-pair-tags v-perturbation))))
	      (let ((u-forward (make-tagged-pair
				(add-tag 'forward (tagged-pair-tags v))
				'unfilled
				'unfilled
				#f
				#f
				#f
				#f
				#f
				'unfilled)))
	       (loop (get-tagged-pair-car v)
		     (get-tagged-pair-car v-perturbation)
		     (cons (cons (cons v v-perturbation) u-forward) cs)
		     (lambda (v-car-forward cs)
		      (loop (get-tagged-pair-cdr v)
			    (get-tagged-pair-cdr v-perturbation)
			    cs
			    (lambda (v-cdr-forward cs)
			     (fill-tagged-pair!
			      u-forward v-car-forward v-cdr-forward)
			     (k u-forward cs)))))))
	     (else (if *abstract?*
		       (let ((u-forward (compile-time-warning
					 "Arguments to bundle might not conform"
					 v
					 v-perturbation)))
			(k u-forward
			   (cons (cons (cons v v-perturbation) u-forward) cs)))
		       (run-time-error "Arguments to bundle do not conform"
				       v
				       v-perturbation)))))))))))))

(define (j* v) (bundle v (perturb (zero v))))

;;; Reverse Mode

(define (added-variable x)
 (new-constant-expression
  (value-binding-value
   (find-if
    (lambda (b)
     (concrete-variable=? x (variable-name (value-binding-variable b))))
    *value-bindings*))))

(define (make-sensitize e) (new-application (added-variable 'sensitize) e))

(define (make-zero e) (new-application (added-variable 'zero) e))

(define (make-plus e1 e2)
 (new-application (added-variable 'plus) (create-cons-expression e1 e2)))

(define (make-plus-binding p e) (make-parameter-binding p (make-plus p e)))

(define (make-*j-inverse e) (new-application (added-variable '*j-inverse) e))

;;; We no longer check for unsupported letrec-expression parameter.
(define (sensitivityify-parameter p) (sensitivity-transform p))

(define (reverseify-parameter p)
 (cond
  ((constant-expression? p)
   (without-abstract
    (lambda () (new-constant-expression (*j (constant-expression-value p))))))
  ((variable-access-expression? p) (reverseify-access p))
  ((lambda-expression? p) (reverse-transform p))
  ((letrec-expression? p)
   (assert (and (variable-access-expression? (letrec-expression-body p))
		(memp variable=?
		      (variable-access-expression-variable
		       (letrec-expression-body p))
		      (letrec-expression-procedure-variables p))))
   (new-letrec-expression
    (map reverseify (letrec-expression-procedure-variables p))
    (map-indexed (lambda (e i)
		  (reverse-transform-internal
		   e
		   (letrec-expression-procedure-variables p)
		   (letrec-expression-lambda-expressions p)
		   i))
		 (letrec-expression-lambda-expressions p))
    (reverseify-access (letrec-expression-body p))))
  ((cons-expression? p)
   (new-cons-expression (add-tag 'reverse (cons-expression-tags p))
			(reverseify-parameter (cons-expression-car p))
			(reverseify-parameter (cons-expression-cdr p))))
  (else (internal-error))))

(define (sensitivity-transform e)
 (if (and (lambda-expression? e) (lambda-expression-sensitivity-transform e))
     (lambda-expression-sensitivity-transform e)
     (let ((e1 (cond
		((constant-expression? e)
		 (without-abstract
		  (lambda ()
		   (new-constant-expression
		    (sensitize (constant-expression-value e))))))
		((variable-access-expression? e) (sensitivityify-access e))
		((lambda-expression? e)
		 (new-lambda-expression
		  (sensitivity-transform (lambda-expression-parameter e))
		  (sensitivity-transform (lambda-expression-body e))))
		((application? e)
		 (new-application
		  (sensitivity-transform (application-callee e))
		  (sensitivity-transform (application-argument e))))
		((letrec-expression? e)
		 (new-letrec-expression
		  (map sensitivityify
		       (letrec-expression-procedure-variables e))
		  (map sensitivity-transform
		       (letrec-expression-lambda-expressions e))
		  (sensitivity-transform (letrec-expression-body e))))
		((cons-expression? e)
		 (new-cons-expression
		  (add-tag 'sensitivity (cons-expression-tags e))
		  (sensitivity-transform (cons-expression-car e))
		  (sensitivity-transform (cons-expression-cdr e))))
		(else (internal-error)))))
      (when (lambda-expression? e)
       (assert
	(and (not (lambda-expression-sensitivity-transform e))
	     (not (lambda-expression-sensitivity-transform-inverse e1))))
       (set-lambda-expression-sensitivity-transform! e e1)
       (set-lambda-expression-sensitivity-transform-inverse! e1 e))
      e1)))

(define (sensitivity-transform-inverse? e)
 (assert (lambda-expression? e))
 (not (not (lambda-expression-sensitivity-transform-inverse e))))

(define (sensitivity-transform-inverse e)
 (assert (and (lambda-expression? e)
	      (lambda-expression-sensitivity-transform-inverse e)))
 (lambda-expression-sensitivity-transform-inverse e))

(define (reverse-transform-internal e xs0 es0 i)
 ;; e  is a lambda expression. Its body is in anf. Its body is a letrec
 ;;    expression, unless it has been optimized away.
 ;; xs1 is the procedure variables of the body of e, when it is a letrec
 ;;     expression. Otherwise it is empty.
 ;; es1 is the lambda expressions of the body of e, when it is a letrec
 ;;     expression. Otherwise it is empty.
 ;; xs0 is the procedure variables of the surrounding letrec or recursive
 ;;     closure when e is a letrec expression lambda expression or a recursive
 ;;     closure lambda expression. Otherwise it is empty.
 ;; es0 is the lambda expressions of the surrounding letrec or recursive
 ;;     closure when e is a letrec expression lambda expression or a recursive
 ;;     closure lambda expression. Otherwise it is empty.
 (assert (lambda-expression? e))
 (if (lambda-expression-reverse-transform e)
     (lambda-expression-reverse-transform e)
     (let* ((p (lambda-expression-parameter e))
	    (e1 (lambda-expression-body e))
	    (xs1 (if (letrec-expression? e1)
		     (letrec-expression-procedure-variables e1)
		     '()))
	    (es1 (if (letrec-expression? e1)
		     (letrec-expression-lambda-expressions e1)
		     '()))
	    ;; I am not 100% sure that this cannot cause name clash. One way to
	    ;; guarantee that there is no name clash is to find the highest
	    ;; index of a backpropagator variable in e1 and generate new
	    ;; indices larger than that.
	    (xs (map-n backpropagatorify (length (anf-let*-parameters e1))))
	    (e2
	     ;; The only portion of this that needs to be anf converted is the
	     ;; cons expression in the body of the let* that returns the primal
	     ;; paired with the backpropagator (except for the backpropagator
	     ;; which is independently alpha/anf converted).
	     (anf-convert-lambda-expression-shallow
	      ;; This doesn't need to be alpha converted since it is derived
	      ;; straightforwardly from an expression that is already alpha
	      ;; converted.
	      (new-lambda-expression
	       (reverseify-parameter p)
	       (new-letrec-expression
		(map reverseify xs1)
		(if (letrec-expression? e1)
		    (map-indexed
		     (lambda (e i) (reverse-transform-internal e xs1 es1 i))
		     es1)
		    '())
		(create-let*
		 ;; These are the bindings for the forward phase that come from
		 ;; the primal.
		 (map
		  (lambda (p e x)
		   (cond
		    ;;            /   /
		    ;;            _   _
		    ;; p = v -~-> p = v
		    ((constant-expression? e)
		     (make-parameter-binding
		      (reverseify-parameter p)
		      (without-abstract
		       (lambda ()
			(new-constant-expression
			 (*j (constant-expression-value e)))))))
		    ;;            /   /
		    ;;            _   _
		    ;; p = e -~-> p = e
		    ((variable-access-expression? e)
		     (make-parameter-binding
		      (reverseify-parameter p) (reverseify-access e)))
		    ;;                /   /
		    ;;                _   ______
		    ;; p = \ x e -~-> p = \ x e
		    ((lambda-expression? e)
		     (make-parameter-binding
		      (reverseify-parameter p) (reverse-transform e)))
		    ;;                /     /  /
		    ;;                _ _   __ __
		    ;; p = x1 x2 -~-> p,p = x1 x2
		    ((application? e)
		     (make-parameter-binding
		      (create-cons-expression
		       (reverseify-parameter p)
		       (new-variable-access-expression x))
		      (new-application
		       (reverseify-access (application-callee e))
		       (reverseify-access (application-argument e)))))
		    ;;                /   /  / /
		    ;;                _   __ _ __
		    ;; p = x1,x2 -~-> p = x1 , x2
		    ((cons-expression? e)
		     (make-parameter-binding
		      (reverseify-parameter p)
		      (new-cons-expression
		       (add-tag 'reverse (cons-expression-tags e))
		       (reverseify-access (cons-expression-car e))
		       (reverseify-access (cons-expression-cdr e)))))
		    (else (internal-error))))
		  (anf-let*-parameters e1)
		  (anf-let*-expressions e1)
		  xs)
		 ;; This conses the result of the forward phase with the
		 ;; backpropagator.
		 (create-cons-expression
		  ;; This is the result of the forward phase.
		  (reverseify-parameter (anf-parameter e1))
		  ;; This is the backpropagator.
		  (anf-convert-lambda-expression-for-reverse
		   (alpha-convert
		    (new-lambda-expression
		     (sensitivityify-access (anf-parameter e1))
		     (create-let*
		      (append
		       ;; These are the zeroing bindings for the reverse phase.
		       (map
			(lambda (x)
			 (make-parameter-binding
			  (sensitivity-access x)
			  (make-sensitize
			   (make-zero (make-*j-inverse (reverse-access x))))))
			(set-differencep
			 variable=?
			 (remove-duplicatesp
			  variable=?
			  (append
			   (parameter-variables p)
			   (map-reduce append
				       '()
				       parameter-variables
				       (anf-let*-parameters e1))
			   xs1
			   ;; needs work: Why is
			   ;;             (recursive-closure-free-variables
			   ;;              xs1 es1)
			   ;;             not here?
			   xs0
			   (if (= i -1)
			       (free-variables e)
			       (recursive-closure-free-variables xs0 es0))))
			 (parameter-variables (anf-parameter e1))))
		       ;; These are the bindings for the reverse phase that
		       ;; come from the primal.
		       (removeq
			#f
			(map
			 (lambda (p e x)
			  (cond
			   ;; p = v is eliminated
			   ((constant-expression? e) #f)
			   ;;            _    _
			   ;;            \    \
			   ;; p = e -~-> e += p
			   ((variable-access-expression? e)
			    (make-plus-binding (sensitivityify-access e)
					       (sensitivityify-parameter p)))
			   ;;                _____    _
			   ;;                \        \
			   ;; p = \ x e -~-> \ x e += p
			   ((lambda-expression? e)
			    (make-plus-binding (sensitivity-transform e)
					       (sensitivityify-parameter p)))
			   ;;                __ _ __    _ _
			   ;;                \  \ \       \
			   ;; p = x1 x2 -~-> x1 , x2 += p p
			   ;; We want the x1,x2 inside the sensitivity so that
			   ;; the aggregate is a sensitivity that can be added
			   ;; by plus, since for type correctness, plus adds
			   ;; only sensitivities.
			   ((application? e)
			    (make-plus-binding
			     (new-cons-expression
			      (add-tag 'sensitivity (empty-tags))
			      (sensitivityify-access (application-callee e))
			      (sensitivityify-access (application-argument e)))
			     (new-application
			      (new-variable-access-expression x)
			      (sensitivityify-parameter p))))
			   ;;                __ _ __    _
			   ;;                \  \ \     \
			   ;; p = x1,x2 -~-> x1 , x2 += p
			   ;; We want the x1,x2 inside the sensitivity so that
			   ;; the aggregate is a sensitivity that can be added
			   ;; by plus, since for type correctness, plus adds
			   ;; only sensitivities.
			   ((cons-expression? e)
			    (make-plus-binding
			     (new-cons-expression
			      (add-tag 'sensitivity (cons-expression-tags e))
			      (sensitivityify-access (cons-expression-car e))
			      (sensitivityify-access (cons-expression-cdr e)))
			     (sensitivityify-parameter p)))
			   (else (internal-error))))
			 (reverse (anf-let*-parameters e1))
			 (reverse (anf-let*-expressions e1))
			 (reverse xs)))
		       (map (lambda (x1)
			     ;; ______________________    __
			     ;; \                         \
			     ;; letrec xs1 = es1 in x1 += x1
			     (make-plus-binding
			      (sensitivity-transform
			       (new-letrec-expression
				xs1 es1 (new-variable-access-expression x1)))
			      (sensitivity-access x1)))
			    xs1)
		       (map (lambda (x0)
			     ;; ______________________    __
			     ;; \                         \
			     ;; letrec xs0 = es0 in x0 += x0
			     (make-plus-binding
			      (sensitivity-transform
			       (new-letrec-expression
				xs0 es0 (new-variable-access-expression x0)))
			      (sensitivity-access x0)))
			    xs0))
		      ;; This conses the sensitivity to the target with the
		      ;; sensitivity to the argument.
		      (new-cons-expression
		       (add-tag 'sensitivity (empty-tags))
		       ;; This is the sensitivity to the target.
		       (sensitivity-transform
			(if (= i -1)
			    ;; _
			    ;; \
			    ;; e
			    e
			    ;; ______________________
			    ;; \
			    ;; letrec xs0 = es0 in x0
			    (new-letrec-expression
			     xs0
			     es0
			     (new-variable-access-expression
			      (list-ref xs0 i)))))
		       ;; This is the sensitivity to the argument.
		       (sensitivityify-parameter p)))))))))))))
      (assert (and (not (lambda-expression-reverse-transform e))
		   (not (lambda-expression-reverse-transform-inverse e2))))
      (set-lambda-expression-reverse-transform! e e2)
      (set-lambda-expression-reverse-transform-inverse! e2 e)
      e2)))

(define (reverse-transform e) (reverse-transform-internal e '() '() -1))

(define (reverse-transform-inverse e)
 (assert (and (lambda-expression? e)
	      (lambda-expression-reverse-transform-inverse e)))
 (lambda-expression-reverse-transform-inverse e))

(define (sensitize v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  14
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v-sensitivity cs) v-sensitivity)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v-sensitivity (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v)
		 (cons (cons v v-sensitivity) cs)
		 (lambda (us-sensitivity cs)
		  (fill-union-values! v-sensitivity us-sensitivity)
		  (k v-sensitivity cs)))))
      ((vlad-empty-list? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((vlad-true? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((vlad-false? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((vlad-real? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((primitive-procedure? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((nonrecursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-sensitivity (make-nonrecursive-closure
			     'unfilled
			     (sensitivity-transform
			      (nonrecursive-closure-lambda-expression v))
			     #f
			     #f
			     #f
			     #f
			     #f
			     'unfilled)))
	(map-cps
	 loop
	 (get-nonrecursive-closure-values v)
	 (cons (cons v u-sensitivity) cs)
	 (lambda (vs-sensitivity cs)
	  (fill-nonrecursive-closure-values! u-sensitivity vs-sensitivity)
	  (k u-sensitivity cs)))))
      ((recursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-sensitivity
	      (make-recursive-closure
	       'unfilled
	       (map-vector sensitivityify
			   (recursive-closure-procedure-variables v))
	       (map-vector sensitivity-transform
			   (recursive-closure-lambda-expressions v))
	       (recursive-closure-index v)
	       #f
	       #f
	       #f
	       #f
	       #f
	       'unfilled)))
	(map-cps loop
		 (get-recursive-closure-values v)
		 (cons (cons v u-sensitivity) cs)
		 (lambda (vs-sensitivity cs)
		  (fill-recursive-closure-values! u-sensitivity vs-sensitivity)
		  (k u-sensitivity cs)))))
      ((perturbation-tagged-value? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((bundle? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((sensitivity-tagged-value? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((reverse-tagged-value? v)
       (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	(k u-sensitivity (cons (cons v u-sensitivity) cs))))
      ((tagged-pair? v)
       (let ((u-sensitivity
	      (make-tagged-pair (add-tag 'sensitivity (tagged-pair-tags v))
				'unfilled
				'unfilled
				#f
				#f
				#f
				#f
				#f
				'unfilled)))
	(loop (get-tagged-pair-car v)
	      (cons (cons v u-sensitivity) cs)
	      (lambda (v-car-sensitivity cs)
	       (loop (get-tagged-pair-cdr v)
		     cs
		     (lambda (v-cdr-sensitivity cs)
		      (fill-tagged-pair!
		       u-sensitivity v-car-sensitivity v-cdr-sensitivity)
		      (k u-sensitivity cs)))))))
      (else (internal-error))))))))

(define (unsensitize? v-sensitivity)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  15
  (let loop ((v-sensitivity v-sensitivity) (cs '()) (k (lambda (r? cs) r?)))
   (let ((found? (memq v-sensitivity cs)))
    (cond
     (found? (k #t cs))
     ((union? v-sensitivity)
      (every-cps loop (union-members v-sensitivity) (cons v-sensitivity cs) k))
     ((vlad-empty-list? v-sensitivity) (k #f cs))
     ((vlad-true? v-sensitivity) (k #f cs))
     ((vlad-false? v-sensitivity) (k #f cs))
     ((vlad-real? v-sensitivity) (k #f cs))
     ((primitive-procedure? v-sensitivity) (k #f cs))
     ((nonrecursive-closure? v-sensitivity)
      (if (and (tagged? 'sensitivity (nonrecursive-closure-tags v-sensitivity))
	       (sensitivity-transform-inverse?
		(nonrecursive-closure-lambda-expression v-sensitivity)))
	  ;; See the note in abstract-environment=?.
	  (every-cps loop
		     (get-nonrecursive-closure-values v-sensitivity)
		     (cons v-sensitivity cs)
		     k)
	  (k #f cs)))
     ((recursive-closure? v-sensitivity)
      (if (and
	   (tagged? 'sensitivity (recursive-closure-tags v-sensitivity))
	   (every-vector unsensitivityify?
			 (recursive-closure-procedure-variables v-sensitivity))
	   (every-vector sensitivity-transform-inverse?
			 (recursive-closure-lambda-expressions v-sensitivity)))
	  ;; See the note in abstract-environment=?.
	  (every-cps loop
		     (get-recursive-closure-values v-sensitivity)
		     (cons v-sensitivity cs)
		     k)
	  (k #f cs)))
     ((perturbation-tagged-value? v-sensitivity) (k #f cs))
     ((bundle? v-sensitivity) (k #f cs))
     ((sensitivity-tagged-value? v-sensitivity) (k #t (cons v-sensitivity cs)))
     ((reverse-tagged-value? v-sensitivity) (k #f cs))
     ((tagged-pair? v-sensitivity)
      (if (tagged? 'sensitivity (tagged-pair-tags v-sensitivity))
	  (loop (get-tagged-pair-car v-sensitivity)
		(cons v-sensitivity cs)
		(lambda (r? cs)
		 (if r?
		     (loop (get-tagged-pair-cdr v-sensitivity) cs k)
		     (k #f cs))))
	  (k #f cs)))
     (else (internal-error)))))))

(define (unsensitize v-sensitivity)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  16
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v-sensitivity v-sensitivity) (cs '()) (k (lambda (v cs) v)))
    (let ((found? (assq v-sensitivity cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v-sensitivity)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v-sensitivity)
		 (cons (cons v-sensitivity v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      ((vlad-empty-list? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((vlad-true? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((vlad-false? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((vlad-real? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((primitive-procedure? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((nonrecursive-closure? v-sensitivity)
       (if (tagged? 'sensitivity (nonrecursive-closure-tags v-sensitivity))
	   ;; See the note in abstract-environment=?.
	   (let ((u (make-nonrecursive-closure
		     'unfilled
		     (sensitivity-transform-inverse
		      (nonrecursive-closure-lambda-expression v-sensitivity))
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (map-cps loop
		     (get-nonrecursive-closure-values v-sensitivity)
		     (cons (cons v-sensitivity u) cs)
		     (lambda (vs cs)
		      (fill-nonrecursive-closure-values! u vs)
		      (k u cs))))
	   (let ((u (ad-error
		     "Argument to unsensitize ~a a non-sensitivity value"
		     v-sensitivity)))
	    (k u (cons (cons v-sensitivity u) cs)))))
      ((recursive-closure? v-sensitivity)
       (if (tagged? 'sensitivity (recursive-closure-tags v-sensitivity))
	   ;; See the note in abstract-environment=?.
	   (let ((u (make-recursive-closure
		     'unfilled
		     (map-vector
		      unsensitivityify
		      (recursive-closure-procedure-variables v-sensitivity))
		     (map-vector
		      sensitivity-transform-inverse
		      (recursive-closure-lambda-expressions v-sensitivity))
		     (recursive-closure-index v-sensitivity)
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (map-cps loop
		     (get-recursive-closure-values v-sensitivity)
		     (cons (cons v-sensitivity u) cs)
		     (lambda (vs cs)
		      (fill-recursive-closure-values! u vs)
		      (k u cs))))
	   (let ((u (ad-error
		     "Argument to unsensitize ~a a non-sensitivity value"
		     v-sensitivity)))
	    (k u (cons (cons v-sensitivity u) cs)))))
      ((perturbation-tagged-value? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((bundle? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((sensitivity-tagged-value? v-sensitivity)
       (let ((u (get-sensitivity-tagged-value-primal v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((reverse-tagged-value? v-sensitivity)
       (let ((u (ad-error "Argument to unsensitize ~a a non-sensitivity value"
			  v-sensitivity)))
	(k u (cons (cons v-sensitivity u) cs))))
      ((tagged-pair? v-sensitivity)
       (if (tagged? 'sensitivity (tagged-pair-tags v-sensitivity))
	   (let ((u (make-tagged-pair
		     (remove-tag 'sensitivity (tagged-pair-tags v-sensitivity))
		     'unfilled
		     'unfilled
		     #f
		     #f
		     #f
		     #f
		     #f
		     'unfilled)))
	    (loop (get-tagged-pair-car v-sensitivity)
		  (cons (cons v-sensitivity u) cs)
		  (lambda (v-car cs)
		   (loop (get-tagged-pair-cdr v-sensitivity)
			 cs
			 (lambda (v-cdr cs)
			  (fill-tagged-pair! u v-car v-cdr)
			  (k u cs))))))
	   (let ((u (ad-error
		     "Argument to unsensitize ~a a non-sensitivity value"
		     v-sensitivity)))
	    (k u (cons (cons v-sensitivity u) cs)))))
      (else (internal-error))))))))

(define (plus v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  17
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (v cs) v)))
    (let ((found? (find-if (lambda (c)
			    (and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
			   cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v1)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps (lambda (u1 cs k) (loop u1 v2 cs k))
		 (union-members v1)
		 (cons (cons (cons v1 v2) v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      ((union? v2)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps (lambda (u2 cs k) (loop v1 u2 cs k))
		 (union-members v2)
		 (cons (cons (cons v1 v2) v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      ((and (vlad-empty-list? v1) (vlad-empty-list? v2))
       (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (vlad-true? v1) (vlad-true? v2))
       (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (vlad-false? v1) (vlad-false? v2))
       (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (abstract-real? v1) (vlad-real? v2))
       (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (vlad-real? v1) (abstract-real? v2))
       (let ((u v2)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (real? v1) (real? v2))
       (let ((u (+ v1 v2))) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
       (let ((u v1)) (k u (cons (cons (cons v1 v2) u) cs))))
      ((and (nonrecursive-closure? v1)
	    (nonrecursive-closure? v2)
	    (dereferenced-nonrecursive-closure-match? v1 v2))
       ;; See the note in abstract-environment=?.
       (let ((u (make-nonrecursive-closure
		 'unfilled
		 (nonrecursive-closure-lambda-expression v1)
		 #f
		 #f
		 #f
		 #f
		 #f
		 'unfilled)))
	(map2-cps loop
		  (get-nonrecursive-closure-values v1)
		  (get-nonrecursive-closure-values v2)
		  (cons (cons (cons v1 v2) u) cs)
		  (lambda (vs cs)
		   (fill-nonrecursive-closure-values! u vs)
		   (k u cs)))))
      ((and (recursive-closure? v1)
	    (recursive-closure? v2)
	    (dereferenced-recursive-closure-match? v1 v2))
       ;; See the note in abstract-environment=?.
       (let ((u (make-recursive-closure
		 'unfilled
		 (recursive-closure-procedure-variables v1)
		 (recursive-closure-lambda-expressions v1)
		 (recursive-closure-index v1)
		 #f
		 #f
		 #f
		 #f
		 #f
		 'unfilled)))
	(map2-cps loop
		  (get-recursive-closure-values v1)
		  (get-recursive-closure-values v2)
		  (cons (cons (cons v1 v2) u) cs)
		  (lambda (vs cs)
		   (fill-recursive-closure-values! u vs)
		   (k u cs)))))
      ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
       (let ((u (make-perturbation-tagged-value
		 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-perturbation-tagged-value-primal v1)
	      (get-perturbation-tagged-value-primal v2)
	      (cons (cons (cons v1 v2) u) cs)
	      (lambda (v cs)
	       (fill-perturbation-tagged-value-primal! u v)
	       (k u cs)))))
      ((and (bundle? v1) (bundle? v2))
       (let ((u (make-bundle 'unfilled 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-bundle-primal v1)
	      (get-bundle-primal v2)
	      (cons (cons (cons v1 v2) u) cs)
	      (lambda (v-primal cs)
	       (loop (get-bundle-tangent v1)
		     (get-bundle-tangent v2)
		     cs
		     (lambda (v-tangent cs)
		      (fill-bundle! u v-primal v-tangent)
		      (k u cs)))))))
      ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
       (let ((u (make-sensitivity-tagged-value
		 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-sensitivity-tagged-value-primal v1)
	      (get-sensitivity-tagged-value-primal v2)
	      (cons (cons (cons v1 v2) u) cs)
	      (lambda (v cs)
	       (fill-sensitivity-tagged-value-primal! u v)
	       (k u cs)))))
      ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
       (let ((u (make-reverse-tagged-value 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-reverse-tagged-value-primal v1)
	      (get-reverse-tagged-value-primal v2)
	      (cons (cons (cons v1 v2) u) cs)
	      (lambda (v cs)
	       (fill-reverse-tagged-value-primal! u v)
	       (k u cs)))))
      ((and (tagged-pair? v1)
	    (tagged-pair? v2)
	    (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))
       (let ((u (make-tagged-pair (tagged-pair-tags v1)
				  'unfilled
				  'unfilled
				  #f
				  #f
				  #f
				  #f
				  #f
				  'unfilled)))
	(loop (get-tagged-pair-car v1)
	      (get-tagged-pair-car v2)
	      (cons (cons (cons v1 v2) u) cs)
	      (lambda (v-car cs)
	       (loop (get-tagged-pair-cdr v1)
		     (get-tagged-pair-cdr v2)
		     cs
		     (lambda (v-cdr cs)
		      (fill-tagged-pair! u v-car v-cdr)
		      (k u cs)))))))
      (else (if *abstract?*
		(let ((u (compile-time-warning
			  "Arguments to plus might not conform" v1 v2)))
		 (k u (cons (cons (cons v1 v2) u) cs)))
		(run-time-error "Arguments to plus do not conform" v1 v2)))))))))

(define (*j v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  18
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v-reverse cs) v-reverse)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v-reverse (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v)
		 (cons (cons v v-reverse) cs)
		 (lambda (us-reverse cs)
		  (fill-union-values! v-reverse us-reverse)
		  (k v-reverse cs)))))
      (else
       (let ((b (find-if
		 ;; This is safe because the arguments will never have
		 ;; unfilled values.
		 (lambda (b) (deep-abstract-value=? v (value-binding-value b)))
		 *value-bindings*)))
	(if b
	    (let ((u-reverse
		   (primitive-procedure-reverse (value-binding-value b))))
	     (k u-reverse (cons (cons v u-reverse) cs)))
	    (cond
	     ((vlad-empty-list? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((vlad-true? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((vlad-false? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((vlad-real? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((primitive-procedure? v) (internal-error))
	     ((nonrecursive-closure? v)
	      ;; See the note in abstract-environment=?.
	      (let ((u-reverse (make-nonrecursive-closure
				'unfilled
				(reverse-transform
				 (nonrecursive-closure-lambda-expression v))
				#f
				#f
				#f
				#f
				#f
				'unfilled)))
	       (map-cps
		loop
		(get-nonrecursive-closure-values v)
		(cons (cons v u-reverse) cs)
		(lambda (vs-reverse cs)
		 (fill-nonrecursive-closure-values! u-reverse vs-reverse)
		 (k u-reverse cs)))))
	     ((recursive-closure? v)
	      ;; See the note in abstract-environment=?.
	      (let ((u-reverse
		     (make-recursive-closure
		      'unfilled
		      (map-vector reverseify
				  (recursive-closure-procedure-variables v))
		      (map-n-vector
		       (lambda (i)
			(reverse-transform-internal
			 (vector-ref (recursive-closure-lambda-expressions v) i)
			 (vector->list
			  (recursive-closure-procedure-variables v))
			 (vector->list (recursive-closure-lambda-expressions v))
			 i))
		       (vector-length (recursive-closure-lambda-expressions v)))
		      (recursive-closure-index v)
		      #f
		      #f
		      #f
		      #f
		      #f
		      'unfilled)))
	       (map-cps loop
			(get-recursive-closure-values v)
			(cons (cons v u-reverse) cs)
			(lambda (vs-reverse cs)
			 (fill-recursive-closure-values! u-reverse vs-reverse)
			 (k u-reverse cs)))))
	     ((perturbation-tagged-value? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((bundle? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((sensitivity-tagged-value? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((reverse-tagged-value? v)
	      (let ((u-reverse (create-reverse-tagged-value v)))
	       (k u-reverse (cons (cons v u-reverse) cs))))
	     ((tagged-pair? v)
	      (let ((u-reverse
		     (make-tagged-pair (add-tag 'reverse (tagged-pair-tags v))
				       'unfilled
				       'unfilled
				       #f
				       #f
				       #f
				       #f
				       #f
				       'unfilled)))
	       (loop (get-tagged-pair-car v)
		     (cons (cons v u-reverse) cs)
		     (lambda (v-car-reverse cs)
		      (loop (get-tagged-pair-cdr v)
			    cs
			    (lambda (v-cdr-reverse cs)
			     (fill-tagged-pair!
			      u-reverse v-car-reverse v-cdr-reverse)
			     (k u-reverse cs)))))))
	     (else (internal-error))))))))))))

(define (*j-inverse v-reverse)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  19
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v-reverse v-reverse) (cs '()) (k (lambda (v cs) v)))
    (let ((found? (assq v-reverse cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v-reverse)
       (let ((v (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (union-members v-reverse)
		 (cons (cons v-reverse v) cs)
		 (lambda (us cs)
		  (fill-union-values! v us)
		  (k v cs)))))
      (else
       (let ((b (find-if
		 (lambda (b)
		  ;; This is safe because the arguments will never have
		  ;; unfilled values.
		  (deep-abstract-value=?
		   v-reverse
		   (primitive-procedure-reverse (value-binding-value b))))
		 *value-bindings*)))
	(if b
	    (let ((u (value-binding-value b)))
	     (k u (cons (cons v-reverse u) cs)))
	    (cond
	     ((vlad-empty-list? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((vlad-true? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((vlad-false? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((vlad-real? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((primitive-procedure? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((nonrecursive-closure? v-reverse)
	      (if (tagged? 'reverse (nonrecursive-closure-tags v-reverse))
		  ;; See the note in abstract-environment=?.
		  (let ((u (make-nonrecursive-closure
			    'unfilled
			    (reverse-transform-inverse
			     (nonrecursive-closure-lambda-expression
			      v-reverse))
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled)))
		   (map-cps loop
			    (get-nonrecursive-closure-values v-reverse)
			    (cons (cons v-reverse u) cs)
			    (lambda (vs cs)
			     (fill-nonrecursive-closure-values! u vs)
			     (k u cs))))
		  (let ((u (ad-error
			    "Argument to *j-inverse ~a a non-reverse value"
			    v-reverse)))
		   (k u (cons (cons v-reverse u) cs)))))
	     ((recursive-closure? v-reverse)
	      (if (tagged? 'reverse (recursive-closure-tags v-reverse))
		  ;; See the note in abstract-environment=?.
		  (let ((u (make-recursive-closure
			    'unfilled
			    (map-vector
			     unreverseify
			     (recursive-closure-procedure-variables v-reverse))
			    (map-vector
			     reverse-transform-inverse
			     (recursive-closure-lambda-expressions v-reverse))
			    (recursive-closure-index v-reverse)
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled)))
		   (map-cps loop
			    (get-recursive-closure-values v-reverse)
			    (cons (cons v-reverse u) cs)
			    (lambda (vs cs)
			     (fill-recursive-closure-values! u vs)
			     (k u cs))))
		  (let ((u (ad-error
			    "Argument to *j-inverse ~a a non-reverse value"
			    v-reverse)))
		   (k u (cons (cons v-reverse u) cs)))))
	     ((perturbation-tagged-value? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((bundle? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((sensitivity-tagged-value? v-reverse)
	      (let ((u (ad-error "Argument to *j-inverse ~a a non-reverse value"
				 v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((reverse-tagged-value? v-reverse)
	      (let ((u (get-reverse-tagged-value-primal v-reverse)))
	       (k u (cons (cons v-reverse u) cs))))
	     ((tagged-pair? v-reverse)
	      (if (tagged? 'reverse (tagged-pair-tags v-reverse))
		  (let ((u (make-tagged-pair
			    (remove-tag 'reverse (tagged-pair-tags v-reverse))
			    'unfilled
			    'unfilled
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled)))
		   (loop (get-tagged-pair-car v-reverse)
			 (cons (cons v-reverse u) cs)
			 (lambda (v-car cs)
			  (loop (get-tagged-pair-cdr v-reverse)
				cs
				(lambda (v-cdr cs)
				 (fill-tagged-pair! u v-car v-cdr)
				 (k u cs))))))
		  (let ((u (ad-error
			    "Argument to *j-inverse ~a a non-reverse value"
			    v-reverse)))
		   (k u (cons (cons v-reverse u) cs)))))
	     (else (internal-error))))))))))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitve
;;;  2. shadowing doesn't occur because of the interning of uninterned symbols
;;;     that occurs implicitly by print followed by read

(define (externalize-expression e)
 (cond
  ((let*? e)
   (let loop ((ps (let*-parameters e)) (es (let*-expressions e)) (bs '()))
    (if (null? ps)
	(case (length bs)
	 ((0) (internal-error))
	 ((1) `(let ,bs ,(externalize-expression (let*-body e))))
	 (else `(let* ,(reverse bs) ,(externalize-expression (let*-body e)))))
	(loop (rest ps)
	      (rest es)
	      (cons `(,(externalize-expression (first ps))
		      ,(externalize-expression (first es)))
		    bs)))))
  ;; needs work: There are several problems with this rendering of constant
  ;;             expressions.
  ;;              1. primitive procedures, nonrecursive closures, recursive
  ;;                 closures, perturbation tagged values, bundles, sensitivity
  ;;                 tagged values, reverse tagged values, abstract booleans,
  ;;                 and abstract real cannot be read back in.
  ;;              2. This doesn't properly interface with unabbreviate-*
  ((constant-expression? e)
   (if (or (boolean? (constant-expression-value e))
	   (real? (constant-expression-value e)))
       (externalize (constant-expression-value e))
       `',(externalize (constant-expression-value e))))
  ((variable-access-expression? e)
   (variable-name (variable-access-expression-variable e)))
  ((lambda-expression? e)
   `(lambda (,(externalize-expression (lambda-expression-parameter e)))
     ,(externalize-expression (lambda-expression-body e))))
  ((application? e)
   `(,(externalize-expression (application-callee e))
     ,(externalize-expression (application-argument e))))
  ((letrec-expression? e)
   `(letrec ,(map (lambda (x e)
		   `(,(variable-name x) ,(externalize-expression e)))
		  (letrec-expression-procedure-variables e)
		  (letrec-expression-lambda-expressions e))
     ,(externalize-expression (letrec-expression-body e))))
  ((cons-expression? e)
   (if (empty-tags? (cons-expression-tags e))
       `(cons ,(externalize-expression (cons-expression-car e))
	      ,(externalize-expression (cons-expression-cdr e)))
       ;; needs work: This cannot be read back in.
       `(cons ,(cons-expression-tags e)
	      ,(externalize-expression (cons-expression-car e))
	      ,(externalize-expression (cons-expression-cdr e)))))
  (else (internal-error))))

(define (quotable? v)
 (cond ((and (not *unabbreviate-transformed?*) (perturbation-value? v)) #f)
       ((and (not *unabbreviate-transformed?*) (forward-value? v)) #f)
       ((and (not *unabbreviate-transformed?*) (sensitivity-value? v)) #f)
       ((and (not *unabbreviate-transformed?*) (reverse-value? v)) #f)
       ((vlad-empty-list? v) #t)
       ((vlad-true? v) #t)
       ((vlad-false? v) #t)
       ((real? v) #t)
       ((abstract-real? v) #f)
       ((vlad-pair? v) (and (quotable? (vlad-car v)) (quotable? (vlad-cdr v))))
       ((primitive-procedure? v) #f)
       ((closure? v) #f)
       ((perturbation-tagged-value? v) #f)
       ((bundle? v) #f)
       ((sensitivity-tagged-value? v) #f)
       ((reverse-tagged-value? v) #f)
       (else (internal-error))))

(define (debugging-externalize v)
 ;; breaks structure sharing
 (let loop ((v v) (vs '()))
  (cond ((memq v vs) `(up ,(positionq v vs)))
	((union? v)
	 `(union ,@(map (lambda (u) (loop u (cons v vs))) (union-members v))))
	((vlad-empty-list? v) '())
	((vlad-true? v) #t)
	((vlad-false? v) #f)
	((real? v) v)
	((abstract-real? v) v)
	((primitive-procedure? v) (primitive-procedure-name v))
	((nonrecursive-closure? v)
	 `(nonrecursive-closure
	   ,@(map (lambda (x v) `(,x ,(loop v vs)))
		  (nonrecursive-closure-variables v)
		  (get-nonrecursive-closure-values v))))
	((recursive-closure? v)
	 `(recursive-closure
	   ,@(map (lambda (x v) `(,x ,(loop v vs)))
		  (recursive-closure-variables v)
		  (get-recursive-closure-values v))
	   ,(vector-ref (recursive-closure-procedure-variables v)
			(recursive-closure-index v))))
	((perturbation-tagged-value? v)
	 `(perturbation ,(loop (get-perturbation-tagged-value-primal v) vs)))
	((bundle? v) `(bundle ,(loop (get-bundle-primal v) vs)
			      ,(loop (get-bundle-tangent v) vs)))
	((sensitivity-tagged-value? v)
	 `(sensitivity ,(loop (get-sensitivity-tagged-value-primal v) vs)))
	((reverse-tagged-value? v)
	 `(reverse ,(loop (get-reverse-tagged-value-primal v) vs)))
	((tagged-pair? v) `(pair ,(tagged-pair-tags v)
				 ,(loop (get-tagged-pair-car v) vs)
				 ,(loop (get-tagged-pair-cdr v) vs)))
	(else (internal-error)))))

(define (externalize v)
 ;; breaks structure sharing
 (let ((v
	(let loop ((v v) (quote? #f) (vs '()))
	 (cond
	  ((memq v vs)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   `(up ,(positionq v vs)))
	  ((union? v)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   (cond ((empty-abstract-value? v) 'bottom)
		 ((null? (rest (union-members v))) (internal-error))
		 (else `(union ,@(map (lambda (u) (loop u quote? (cons v vs)))
				      (union-members v))))))
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(perturbation-value? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(perturb ,(loop (unperturb v) quote? vs)))
		 (else `(perturbation ,(loop (unperturb v) quote? vs)))))
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(forward-value? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(bundle ,(loop (primal v) quote? vs)
			   ,(loop (tangent v) quote? vs)))
		 (else `(forward ,(loop (primal v) quote? vs)
				 ,(loop (tangent v) quote? vs)))))
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(sensitivity-value? v)
		;; This is to prevent attempts to unsensitize backpropagators.
		(unsensitize? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(sensitize ,(loop (unsensitize v) quote? vs)))
		 (else `(sensitivity ,(loop (unsensitize v) quote? vs)))))
	  ;; It may not be possible to apply *j-inverse to a closure whose
	  ;; parameter is reverse tagged. Such a situation arises when you
	  ;; externalize an analysis. It may contain closures that result from
	  ;; lambda expressions that correspond to tails of anf forms of lambda
	  ;; expression bodies.
	  ((and (or (not *unabbreviate-transformed?*) (tagged-pair? v))
		(reverse-value? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(*j ,(loop (*j-inverse v) quote? vs)))
		 (else `(reverse ,(loop (*j-inverse v) quote? vs)))))
	  ((vlad-empty-list? v)
	   (if (and *unabbreviate-executably?* (not quote?)) ''() '()))
	  ((vlad-true? v) #t)
	  ((vlad-false? v) #f)
	  ((real? v) v)
	  ((abstract-real? v)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably"v))
	   v)
	  ((vlad-pair? v)
	   (if (and *unabbreviate-executably?* (not quote?))
	       (if (quotable? v)
		   `',(cons (loop (vlad-car v) #t vs)
			    (loop (vlad-cdr v) #t vs))
		   `(cons ,(loop (vlad-car v) #f vs)
			  ,(loop (vlad-cdr v) #f vs)))
	       (cons (loop (vlad-car v) quote? vs)
		     (loop (vlad-cdr v) quote? vs))))
	  ((primitive-procedure? v)
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  (string->symbol
		   (string-append (symbol->string (primitive-procedure-name v))
				  (symbol->string '-primitive))))
		 (else (primitive-procedure-name v))))
	  ((nonrecursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     (case (length (nonrecursive-closure-variables v))
	      ((0) (externalize-expression
		    (nonrecursive-closure-lambda-expression v)))
	      ((1) `(let ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
			       (nonrecursive-closure-variables v)
			       (get-nonrecursive-closure-values v))
		     ,(externalize-expression
		       (nonrecursive-closure-lambda-expression v))))
	      (else `(let ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
				(nonrecursive-closure-variables v)
				(get-nonrecursive-closure-values v))
		      ,(externalize-expression
			(nonrecursive-closure-lambda-expression v))))))
	    (*unabbreviate-nonrecursive-closures?*
	     `(nonrecursive-closure
	       ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
		     (nonrecursive-closure-variables v)
		     (get-nonrecursive-closure-values v))
	       ,(externalize-expression
		 (nonrecursive-closure-lambda-expression v))))
	    (else (externalize-expression
		   (nonrecursive-closure-lambda-expression v)))))
	  ((recursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     (case (length (recursive-closure-variables v))
	      ((0) `(letrec ,(vector->list
			      (map-vector
			       (lambda (x e) `(,x ,(externalize-expression e)))
			       (recursive-closure-procedure-variables v)
			       (recursive-closure-lambda-expressions v)))
		     ,(vector-ref (recursive-closure-procedure-variables v)
				  (recursive-closure-index v))))
	      ((1) `(let ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
			       (recursive-closure-variables v)
			       (get-recursive-closure-values v))
		     (letrec ,(vector->list
			       (map-vector
				(lambda (x e)
				 `(,x ,(externalize-expression e)))
				(recursive-closure-procedure-variables v)
				(recursive-closure-lambda-expressions v)))
		      ,(vector-ref (recursive-closure-procedure-variables v)
				   (recursive-closure-index v)))))
	      (else
	       `(let ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
			   (recursive-closure-variables v)
			   (get-recursive-closure-values v))
		 (letrec ,(vector->list
			   (map-vector
			    (lambda (x e) `(,x ,(externalize-expression e)))
			    (recursive-closure-procedure-variables v)
			    (recursive-closure-lambda-expressions v)))
		  ,(vector-ref (recursive-closure-procedure-variables v)
			       (recursive-closure-index v)))))))
	    (*unabbreviate-recursive-closures?*
	     `(recursive-closure
	       ,(map (lambda (x v) `(,x ,(loop v quote? vs)))
		     (recursive-closure-variables v)
		     (get-recursive-closure-values v))
	       ,(vector->list
		 (map-vector (lambda (x e) `(,x ,(externalize-expression e)))
			     (recursive-closure-procedure-variables v)
			     (recursive-closure-lambda-expressions v)))
	       ,(vector-ref (recursive-closure-procedure-variables v)
			    (recursive-closure-index v))))
	    (else (vector-ref (recursive-closure-procedure-variables v)
			      (recursive-closure-index v)))))
	  ((perturbation-tagged-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     `(perturb
	       ,(loop (get-perturbation-tagged-value-primal v) quote? vs)))
	    (else
	     `(perturbation
	       ,(loop (get-perturbation-tagged-value-primal v) quote? vs)))))
	  ((bundle? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(bundle ,(loop (get-bundle-primal v) quote? vs)
			   ,(loop (get-bundle-tangent v) quote? vs)))
		 (else `(forward ,(loop (get-bundle-primal v) quote? vs)
				 ,(loop (get-bundle-tangent v) quote? vs)))))
	  ((sensitivity-tagged-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     `(sensitize
	       ,(loop (get-sensitivity-tagged-value-primal v) quote? vs)))
	    (else
	     `(sensitivity
	       ,(loop (get-sensitivity-tagged-value-primal v) quote? vs)))))
	  ((reverse-tagged-value? v)
	   ;; Only needed for *unabbreviate-transformed?*.
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     `(*j ,(loop (get-reverse-tagged-value-primal v) quote? vs)))
	    (else
	     `(reverse
	       ,(loop (get-reverse-tagged-value-primal v) quote? vs)))))
	  (else (internal-error))))))
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

(define (externalize-environment xs vs)
 (assert (and (list? vs) (= (length xs) (length vs))))
 (map (lambda (x v) (list (variable-name x) (externalize v))) xs vs))

(define (externalize-environment-binding xs b)
 (assert (environment-binding? b))
 (list (externalize-environment xs (environment-binding-values b))
       (externalize (environment-binding-value b))))

(define (externalize-environment-bindings xs bs)
 (assert (and (list? bs) (every environment-binding? bs)))
 (map (lambda (b) (externalize-environment-binding xs b)) bs))

(define (externalize-analysis)
 (map (lambda (e)
       (list (externalize-expression e)
	     (externalize-environment-bindings
	      (free-variables e)
	      (expression-environment-bindings e))))
      (remove-if (lambda (e) (null? (expression-environment-bindings e)))
		 *expressions*)))

;;; Concrete Evaluator

(define (with-write-level n thunk)
 (let ((m (write-level)))
  (set-write-level! n)
  (thunk)
  (set-write-level! m)))

(define (with-write-length n thunk)
 (let ((m (write-length)))
  (set-write-length! n)
  (thunk)
  (set-write-length! m)))

(define (tag-check? v1 v2) (prefix-tags? (value-tags v1) (value-tags v2)))

;;; Environment Restriction/Construction

(define (restrict-environment vs e f)
 (assert (= (length vs) (length (free-variables e))))
 (map (lambda (x) (list-ref vs (positionp variable=? x (free-variables e))))
      (free-variables (f e))))

(define (letrec-restrict-environment vs e)
 (assert (= (length vs) (length (free-variables e))))
 (map (lambda (x) (list-ref vs (positionp variable=? x (free-variables e))))
      (letrec-expression-variables e)))

(define (letrec-nested-environment vs e)
 ;; The abstract values in vs might violate the syntactic constraints. We adopt
 ;; the constraint that all abstract values in all environment bindings satisfy
 ;; the syntactic constraints. We widen here so that we compare widened values
 ;; to widened values.
 (map (lambda (x)
       (if (memp variable=? x (letrec-expression-procedure-variables e))
	   ;; This may create an abstract value that violates the syntactic
	   ;; constraints.
	   (new-recursive-closure
	    (letrec-restrict-environment vs e)
	    (list->vector (letrec-expression-procedure-variables e))
	    (list->vector (letrec-expression-lambda-expressions e))
	    (positionp variable=? x (letrec-expression-procedure-variables e)))
	   (list-ref vs (positionp variable=? x (free-variables e)))))
      (free-variables (letrec-expression-body e))))

(define (concrete-destructure p v)
 (cond ((constant-expression? p)
	(unless (abstract-value=? (constant-expression-value p) v)
	 (run-time-error "Argument is not an equivalent value"
			 (constant-expression-value p)
			 v))
	'())
       ((variable-access-expression? p)
	(list (cons (variable-access-expression-variable p) v)))
       ((lambda-expression? p)
	(unless (and (nonrecursive-closure? v)
		     (dereferenced-expression-eqv?
		      p (nonrecursive-closure-lambda-expression v)))
	 (run-time-error
	  (format #f "Argument is not a matching nonrecursive closure for ~s"
		  (externalize-expression p))
	  v))
	(map cons (parameter-variables p) (get-nonrecursive-closure-values v)))
       ((letrec-expression? p)
	(assert (and (variable-access-expression? (letrec-expression-body p))
		     (memp variable=?
			   (variable-access-expression-variable
			    (letrec-expression-body p))
			   (letrec-expression-procedure-variables p))))
	(unless (and (recursive-closure? v)
		     (= (recursive-closure-index v)
			(positionp variable=?
				   (variable-access-expression-variable
				    (letrec-expression-body p))
				   (letrec-expression-procedure-variables p)))
		     (= (vector-length
			 (recursive-closure-procedure-variables v))
			(length (letrec-expression-procedure-variables p)))
		     (= (vector-length
			 (recursive-closure-lambda-expressions v))
			(length (letrec-expression-lambda-expressions p)))
		     (every
		      dereferenced-expression-eqv?
		      (vector->list (recursive-closure-lambda-expressions v))
		      (letrec-expression-lambda-expressions p)))
	 (run-time-error
	  (format #f "Argument is not a matching recursive closure for ~s"
		  (externalize-expression p))
	  v))
	(map cons (parameter-variables p) (get-recursive-closure-values v)))
       ((cons-expression? p)
	(unless (and (tagged-pair? v)
		     (equal-tags? (cons-expression-tags p)
				  (tagged-pair-tags v)))
	 (run-time-error
	  (format #f "Argument is not a matching tagged pair with tags ~s"
		  (cons-expression-tags p))
	  v))
	(append (concrete-destructure
		 (cons-expression-car p) (get-tagged-pair-car v))
		(concrete-destructure
		 (cons-expression-cdr p) (get-tagged-pair-cdr v))))
       (else (internal-error))))

(define (construct-concrete-environment v1 v2)
 (cond
  ((nonrecursive-closure? v1)
   (let ((alist (concrete-destructure (nonrecursive-closure-parameter v1) v2)))
    (map
     (lambda (x)
      (let ((result (assp variable=? x alist)))
       (if result
	   (cdr result)
	   (list-ref
	    (get-nonrecursive-closure-values v1)
	    (positionp variable=? x (nonrecursive-closure-variables v1))))))
     (free-variables
      (lambda-expression-body (nonrecursive-closure-lambda-expression v1))))))
  ((recursive-closure? v1)
   (let ((alist (concrete-destructure (recursive-closure-parameter v1) v2)))
    (map (lambda (x)
	  (let ((result (assp variable=? x alist)))
	   (cond
	    (result (cdr result))
	    ((some-vector (lambda (x1) (variable=? x x1))
			  (recursive-closure-procedure-variables v1))
	     (new-recursive-closure
	      (get-recursive-closure-values v1)
	      (recursive-closure-procedure-variables v1)
	      (recursive-closure-lambda-expressions v1)
	      (positionp-vector
	       variable=? x (recursive-closure-procedure-variables v1))))
	    (else
	     (list-ref
	      (get-recursive-closure-values v1)
	      (positionp variable=? x (recursive-closure-variables v1)))))))
	 (free-variables (lambda-expression-body
			  (vector-ref (recursive-closure-lambda-expressions v1)
				      (recursive-closure-index v1)))))))
  (else (internal-error))))

;;; needs work: This evaluator is not tail recursive.

(define (concrete-apply v1 v2)
 (unless (vlad-procedure? v1) (run-time-error "Target is not a procedure" v1))
 (unless (tag-check? v1 v2)
  (run-time-error "Argument has wrong type for target" v1 v2))
 (set! *stack* (cons (list v1 v2) *stack*))
 (when (cond ((primitive-procedure? v1) *trace-primitive-procedures?*)
	     ((nonrecursive-closure? v1) *trace-nonrecursive-closures?*)
	     ((recursive-closure? v1) *trace-recursive-closures?*)
	     (else (internal-error)))
  (if *trace-argument/result?*
      (format #t "~aentering ~s ~s~%"
	      (make-string *trace-level* #\space)
	      (externalize v1)
	      (externalize v2))
      (format #t "~aentering ~s~%"
	      (make-string *trace-level* #\space)
	      (externalize v1)))
  (set! *trace-level* (+ *trace-level* 1)))
 (when (and *metered?* (primitive-procedure? v1))
  (set-primitive-procedure-meter!
   v1 (+ (primitive-procedure-meter v1) 1)))
 (let ((result
	(cond
	 ((primitive-procedure? v1) ((primitive-procedure-procedure v1) v2))
	 ((closure? v1)
	  (concrete-eval
	   (closure-body v1) (construct-concrete-environment v1 v2)))
	 (else (internal-error)))))
  (set! *stack* (rest *stack*))
  (when (cond ((primitive-procedure? v1) *trace-primitive-procedures?*)
	      ((nonrecursive-closure? v1) *trace-nonrecursive-closures?*)
	      ((recursive-closure? v1) *trace-recursive-closures?*)
	      (else (internal-error)))
   (set! *trace-level* (- *trace-level* 1))
   (if *trace-argument/result?*
       (format #t "~aexiting ~s ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize v1)
	       (externalize result))
       (format #t "~aexiting ~s~%"
	       (make-string *trace-level* #\space)
	       (externalize v1))))
  result))

(define (concrete-eval e vs)
 (cond
  ((constant-expression? e) (constant-expression-value e))
  ((variable-access-expression? e) (first vs))
  ((lambda-expression? e) (new-nonrecursive-closure vs e))
  ((application? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((v1 (concrete-eval (application-callee e)
			     (restrict-environment vs e application-callee)))
	  (v2 (concrete-eval
	       (application-argument e)
	       (restrict-environment vs e application-argument))))
    (concrete-apply v1 v2)))
  ((letrec-expression? e)
   (concrete-eval (letrec-expression-body e) (letrec-nested-environment vs e)))
  ((cons-expression? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((v1 (concrete-eval (cons-expression-car e)
			     (restrict-environment vs e cons-expression-car)))
	  (v2 (concrete-eval (cons-expression-cdr e)
			     (restrict-environment vs e cons-expression-cdr))))
    (unless (prefix-tags? (cons-expression-tags e) (value-tags v1))
     (run-time-error
      (format #f "CAR argument has wrong type for target with tags ~s"
	      (cons-expression-tags e))
      v1))
    (unless (prefix-tags? (cons-expression-tags e) (value-tags v2))
     (run-time-error
      (format #f "CDR argument has wrong type for target with tags ~s"
	      (cons-expression-tags e))
      v2))
    (new-tagged-pair (cons-expression-tags e) v1 v2)))
  (else (internal-error))))

;;; Flow Analysis

;;; Abstract Values

(define (concrete-value->abstract-value v)
 ;; breaks structure sharing
 (cond
  ((scalar-value? v)
   (if (and *imprecise-inexacts?* (real? v) (inexact? v)) (abstract-real) v))
  ((nonrecursive-closure? v)
   (new-nonrecursive-closure
    (map concrete-value->abstract-value (get-nonrecursive-closure-values v))
    (nonrecursive-closure-lambda-expression v)))
  ((recursive-closure? v)
   (new-recursive-closure
    (map concrete-value->abstract-value (get-recursive-closure-values v))
    (recursive-closure-procedure-variables v)
    (recursive-closure-lambda-expressions v)
    (recursive-closure-index v)))
  ((perturbation-tagged-value? v)
   (new-perturbation-tagged-value
    (concrete-value->abstract-value (get-perturbation-tagged-value-primal v))))
  ((bundle? v)
   (new-bundle (concrete-value->abstract-value (get-bundle-primal v))
	       (concrete-value->abstract-value (get-bundle-tangent v))))
  ((sensitivity-tagged-value? v)
   (new-sensitivity-tagged-value
    (concrete-value->abstract-value (get-sensitivity-tagged-value-primal v))))
  ((reverse-tagged-value? v)
   (new-reverse-tagged-value
    (concrete-value->abstract-value (get-reverse-tagged-value-primal v))))
  ((tagged-pair? v)
   (new-tagged-pair (tagged-pair-tags v)
		    (concrete-value->abstract-value (get-tagged-pair-car v))
		    (concrete-value->abstract-value (get-tagged-pair-cdr v))))
  (else (internal-error))))

;;; Widen

;;; Width

(define (reduce-real-width limit v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  20
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       (let ((v-prime (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	(map-cps loop
		 (if (> (count-if real? (union-members v)) limit)
		     (cons (abstract-real) (remove-if real? (union-members v)))
		     (union-members v))
		 (cons (cons v v-prime) cs)
		 (lambda (us-prime cs)
		  (fill-union-values! v-prime us-prime)
		  (k v-prime cs)))))
      ((vlad-empty-list? v)
       (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
      ((vlad-true? v)
       (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
      ((vlad-false? v)
       (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
      ((vlad-real? v)
       (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
      ((primitive-procedure? v)
       (let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
      ((nonrecursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-prime (make-nonrecursive-closure
		       'unfilled
		       (nonrecursive-closure-lambda-expression v)
		       #f
		       #f
		       #f
		       #f
		       #f
		       'unfilled)))
	(map-cps loop
		 (get-nonrecursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-nonrecursive-closure-values! u-prime vs-prime)
		  (k u-prime cs)))))
      ((recursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-prime (make-recursive-closure
		       'unfilled
		       (recursive-closure-procedure-variables v)
		       (recursive-closure-lambda-expressions v)
		       (recursive-closure-index v)
		       #f
		       #f
		       #f
		       #f
		       #f
		       'unfilled)))
	(map-cps loop
		 (get-recursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-recursive-closure-values! u-prime vs-prime)
		  (k u-prime cs)))))
      ((perturbation-tagged-value? v)
       (let ((u-prime (make-perturbation-tagged-value
		       'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-perturbation-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-perturbation-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((bundle? v)
       (let ((u-prime
	      (make-bundle 'unfilled 'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-bundle-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-primal-prime cs)
	       (loop (get-bundle-tangent v)
		     cs
		     (lambda (v-tangent-prime cs)
		      (fill-bundle! u-prime v-primal-prime v-tangent-prime)
		      (k u-prime cs)))))))
      ((sensitivity-tagged-value? v)
       (let ((u-prime (make-sensitivity-tagged-value
		       'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-sensitivity-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-sensitivity-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((reverse-tagged-value? v)
       (let ((u-prime (make-reverse-tagged-value
		       'unfilled #f #f #f #f #f 'unfilled)))
	(loop (get-reverse-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-reverse-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((tagged-pair? v)
       (let ((u-prime (make-tagged-pair (tagged-pair-tags v)
					'unfilled
					'unfilled
					#f
					#f
					#f
					#f
					#f
					'unfilled)))
	(loop (get-tagged-pair-car v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-car-prime cs)
	       (loop (get-tagged-pair-cdr v)
		     cs
		     (lambda (v-cdr-prime cs)
		      (fill-tagged-pair! u-prime v-car-prime v-cdr-prime)
		      (k u-prime cs)))))))
      (else (internal-error))))))))

(define (limit-real-width v)
 (if (eq? *real-width-limit* #f) v (reduce-real-width *real-width-limit* v)))

(define (pick-values-to-coalesce-for-width-limit limit match? type? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  21
  (let outer ((v v) (vs '()) (k (lambda (vs) #f)))
   (cond
    ((real? v) (k vs))
    ((memq v vs) (k vs))
    ((union? v)
     (let* ((us (find-if (lambda (us) (> (length us) limit))
			 (transitive-equivalence-classesp
			  match? (remove-if-not type? (union-members v))))))
      (if us
	  (list (first us) (second us))
	  (let inner ((us (union-members v)) (vs (cons v vs)))
	   (if (null? us)
	       (k vs)
	       (outer (first us) vs (lambda (vs) (inner (rest us) vs))))))))
    ((scalar-value? v) (k vs))
    (else (let inner ((vs1 (aggregate-value-values v)) (vs vs))
	   (if (null? vs1)
	       (k vs)
	       (outer (first vs1) vs (lambda (vs) (inner (rest vs1) vs))))))))))

(define (merge-subabstract-values v u1 u2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  22
  (canonize-and-maybe-intern-abstract-value
   (let ((u12 (create-aggregate-value-with-new-values
	       u1
	       (map abstract-value-union
		    (aggregate-value-values u1)
		    (aggregate-value-values u2)))))
    (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
     (let ((found? (assq v cs)))
      (cond
       (found? (k (cdr found?) cs))
       ((or (eq? v u1) (eq? v u2)) (loop u12 cs k))
       ((union? v)
	(let ((v-prime (make-union 'unfilled #f #f #f #f #f 'unfilled)))
	 (map-cps loop
		  (union-members v)
		  (cons (cons v v-prime) cs)
		  (lambda (us-prime cs)
		   (fill-union-values! v-prime us-prime)
		   (k v-prime cs)))))
       ((vlad-empty-list? v)
	(let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
       ((vlad-true? v)
	(let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
       ((vlad-false? v)
	(let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
       ((vlad-real? v)
	(let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
       ((primitive-procedure? v)
	(let ((u-prime v)) (k u-prime (cons (cons v u-prime) cs))))
       ((nonrecursive-closure? v)
	;; See the note in abstract-environment=?.
	(let ((u-prime (make-nonrecursive-closure
			'unfilled
			(nonrecursive-closure-lambda-expression v)
			#f
			#f
			#f
			#f
			#f
			'unfilled)))
	 (map-cps loop
		  (get-nonrecursive-closure-values v)
		  (cons (cons v u-prime) cs)
		  (lambda (vs-prime cs)
		   (fill-nonrecursive-closure-values! u-prime vs-prime)
		   (k u-prime cs)))))
       ((recursive-closure? v)
	;; See the note in abstract-environment=?.
	(let ((u-prime (make-recursive-closure
			'unfilled
			(recursive-closure-procedure-variables v)
			(recursive-closure-lambda-expressions v)
			(recursive-closure-index v)
			#f
			#f
			#f
			#f
			#f
			'unfilled)))
	 (map-cps loop
		  (get-recursive-closure-values v)
		  (cons (cons v u-prime) cs)
		  (lambda (vs-prime cs)
		   (fill-recursive-closure-values! u-prime vs-prime)
		   (k u-prime cs)))))
       ((perturbation-tagged-value? v)
	(let ((u-prime (make-perturbation-tagged-value
			'unfilled #f #f #f #f #f 'unfilled)))
	 (loop (get-perturbation-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-perturbation-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((bundle? v)
	(let ((u-prime
	       (make-bundle 'unfilled 'unfilled #f #f #f #f #f 'unfilled)))
	 (loop (get-bundle-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-primal-prime cs)
		(loop (get-bundle-tangent v)
		      cs
		      (lambda (v-tangent-prime cs)
		       (fill-bundle! u-prime v-primal-prime v-tangent-prime)
		       (k u-prime cs)))))))
       ((sensitivity-tagged-value? v)
	(let ((u-prime (make-sensitivity-tagged-value
			'unfilled #f #f #f #f #f 'unfilled)))
	 (loop (get-sensitivity-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-sensitivity-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((reverse-tagged-value? v)
	(let ((u-prime (make-reverse-tagged-value
			'unfilled #f #f #f #f #f 'unfilled)))
	 (loop (get-reverse-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-reverse-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((tagged-pair? v)
	(let ((u-prime (make-tagged-pair (tagged-pair-tags v)
					 'unfilled
					 'unfilled
					 #f
					 #f
					 #f
					 #f
					 #f
					 'unfilled)))
	 (loop (get-tagged-pair-car v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-car-prime cs)
		(loop (get-tagged-pair-cdr v)
		      cs
		      (lambda (v-cdr-prime cs)
		       (fill-tagged-pair! u-prime v-car-prime v-cdr-prime)
		       (k u-prime cs)))))))
       (else (internal-error)))))))))

(define (limit-width limit match? type? v)
 (if (eq? limit #f)
     v
     (let loop ((v v))
      (let ((u1-u2
	     (pick-values-to-coalesce-for-width-limit limit match? type? v)))
       (if (eq? u1-u2 #f)
	   v
	   (let* ((v-prime
		   (merge-subabstract-values v (first u1-u2) (second u1-u2))))
	    (assert (abstract-value-subset? v v-prime))
	    (loop v-prime)))))))

;;; Depth

;;; A path is a list of abstract values. The first element of the list is the
;;; root and the last element is a leaf. The last element is either a scalar
;;; abstract value, an aggregate abstract value that has no children, or an up.
;;; Each abstract value is a slot or a member of the preceeding abstract value.

(define (path-of-greatest-depth match? type? v)
 ;; This is written in CPS so as not to break structure sharing.
 ;; We now adopt a more efficient representation of paths. A path is a set of
 ;; sets of abstract values. Each abstract values satisfies type? and each set
 ;; of abstract values is an equivalence class by match?. The depth is thus the
 ;; cardinality of the largest equivalence class.
 (time-it-bucket
  23
  (let outer ((v v)
	      (cs '())
	      (path '())
	      (depth-of-path 0)
	      (longest-path #f)
	      (depth-of-longest-path #f)
	      (k (lambda (longest-path depth-of-longest-path cs) longest-path)))
   (let ((found? (assq v cs)))
    (cond
     (found?
      (if (> depth-of-path (cdr found?))
	  (if (some (lambda (class) (memq v class)) path)
	      (k (if (or (eq? longest-path #f)
			 (> depth-of-path depth-of-longest-path))
		     path
		     longest-path)
		 (if (or (eq? longest-path #f)
			 (> depth-of-path depth-of-longest-path))
		     depth-of-path
		     depth-of-longest-path)
		 (map (lambda (c) (if (eq? (car c) v) (cons v depth-of-path) c))
		      cs))
	      (outer v
		     (remove-if (lambda (c) (eq? (car c) v)) cs)
		     path
		     depth-of-path
		     longest-path
		     depth-of-longest-path
		     k))
	  (k longest-path depth-of-longest-path cs)))
     ((union? v)
      ;; This assumes that unions never contribute to depth.
      (let inner ((us (get-union-values v))
		  (cs (cons (cons v depth-of-path) cs))
		  (longest-path
		   (if (or (eq? longest-path #f)
			   (> depth-of-path depth-of-longest-path))
		       path
		       longest-path))
		  (depth-of-longest-path
		   (if (or (eq? longest-path #f)
			   (> depth-of-path depth-of-longest-path))
		       depth-of-path
		       depth-of-longest-path)))
       (if (null? us)
	   (k longest-path depth-of-longest-path cs)
	   (outer
	    (first us)
	    cs
	    path
	    depth-of-path
	    longest-path
	    depth-of-longest-path
	    (lambda (longest-path depth-of-longest-path cs)
	     (inner (rest us) cs longest-path depth-of-longest-path))))))
     ((scalar-value? v)
      ;; This assumes that scalars never contribute to depth.
      (k (if (or (eq? longest-path #f) (> depth-of-path depth-of-longest-path))
	     path
	     longest-path)
	 (if (or (eq? longest-path #f) (> depth-of-path depth-of-longest-path))
	     depth-of-path
	     depth-of-longest-path)
	 (cons (cons v depth-of-path) cs)))
     (else
      ;; This assumes that only values of type? contribute to depth.
      (let* ((path (if (type? v)
		       (let loop ((path path))
			(cond ((null? path) (list (list v)))
			      ;; This assumes that match? is transitive.
			      ((match? v (first (first path)))
			       (cons (cons v (first path)) (rest path)))
			      (else (cons (first path) (loop (rest path))))))
		       path))
	     (depth-of-path (map-reduce max 0 length path)))
       (let inner ((vs (aggregate-value-values v))
		   (cs (cons (cons v depth-of-path) cs))
		   (longest-path
		    (if (or (eq? longest-path #f)
			    (> depth-of-path depth-of-longest-path))
			path
			longest-path))
		   (depth-of-longest-path
		    (if (or (eq? longest-path #f)
			    (> depth-of-path depth-of-longest-path))
			depth-of-path
			depth-of-longest-path)))
	(if (null? vs)
	    (k longest-path depth-of-longest-path cs)
	    (outer
	     (first vs)
	     cs
	     path
	     depth-of-path
	     longest-path
	     depth-of-longest-path
	     (lambda (longest-path depth-of-longest-path cs)
	      (inner (rest vs) cs longest-path depth-of-longest-path))))))))))))

(define (path-of-depth-greater-than-limit limit match? type? v)
 (let ((longest-path (path-of-greatest-depth match? type? v)))
  (if (and (not (eq? longest-path #f))
	   (> (map-reduce max 0 length longest-path) limit))
      longest-path
      #f)))

(define (pick-values-to-coalesce-for-depth-limit path)
 (let* ((k (map-reduce max 0 length path))
	;; We arbitrarily pick the first class.
	(class (find-if (lambda (class) (= (length class) k)) path)))
  ;; We arbitrarily pick the first two members of the class.
  (list (first class) (second class))))

(define (limit-depth limit match? type? v)
 (if (or (eq? limit #f)
	 (let ((vs (type-in-abstract-value type? v)))
	  (or (<= (length vs) limit)
	      (every (lambda (vs) (<= (length vs) limit))
		     (transitive-equivalence-classesp match? vs)))))
     v
     (let loop ((v v))
      (let ((path (path-of-depth-greater-than-limit limit match? type? v)))
       (if (eq? path #f)
	   v
	   (let* ((u1-u2 (pick-values-to-coalesce-for-depth-limit path))
		  (v-prime
		   (merge-subabstract-values v (first u1-u2) (second u1-u2))))
	    (assert (abstract-value-subset? v v-prime))
	    (loop v-prime)))))))

;;; Syntactic Constraints

(define (limit-closure-width v)
 (limit-width *closure-width-limit* closure-match? closure? v))

(define (limit-perturbation-tagged-value-width v)
 (limit-width *perturbation-tagged-value-width-limit*
	      (lambda (u1 u2) #t)
	      perturbation-tagged-value?
	      v))

(define (limit-bundle-width v)
 (limit-width *bundle-width-limit* (lambda (u1 u2) #t) bundle? v))

(define (limit-sensitivity-tagged-value-width v)
 (limit-width *sensitivity-tagged-value-width-limit*
	      (lambda (u1 u2) #t)
	      sensitivity-tagged-value?
	      v))

(define (limit-reverse-tagged-value-width v)
 (limit-width *reverse-tagged-value-width-limit*
	      (lambda (u1 u2) #t)
	      reverse-tagged-value?
	      v))

(define (limit-tagged-pair-width v)
 (limit-width *tagged-pair-width-limit*
	      (lambda (u1 u2)
	       (equal-tags? (tagged-pair-tags u1) (tagged-pair-tags u2)))
	      tagged-pair?
	      v))

(define (backpropagator? u)
 ;; needs work: This is a kludge and might not work because some
 ;;             backpropagators might be unsensitizable.
 (and (nonrecursive-closure? u)
      (not (null? (value-tags u)))
      ;; An optimization
      (memq 'sensitivity (value-tags u))
      (case (first (value-tags u))
       ((perturbation) (backpropagator? (unperturb u)))
       ((forward) (backpropagator? (primal u)))
       ((sensitivity)
	(or (not (unsensitize? u)) (backpropagator? (unsensitize u))))
       ((reverse) (backpropagator? (*j-inverse u)))
       (else (internal-error)))))

(define (backpropagator-variable? x)
 (let loop ((x (variable-name x)))
  (or (and (list? x)
	   (= (length x) 3)
	   (eq? (first x) 'alpha)
	   (loop (second x))
	   (integer? (third x))
	   (exact? (third x))
	   (not (negative? (third x))))
      (and (list? x)
	   (= (length x) 2)
	   (eq? (first x) 'backpropagator)
	   (integer? (second x))
	   (exact? (second x))
	   (not (negative? (second x))))
      (and (list? x)
	   (= (length x) 2)
	   (eq? (first x) 'perturbation)
	   (loop (second x)))
      (and (list? x)
	   (= (length x) 2)
	   (eq? (first x) 'forward)
	   (loop (second x)))
      (and (list? x)
	   (= (length x) 2)
	   (eq? (first x) 'sensitivity)
	   (loop (second x)))
      (and (list? x)
	   (= (length x) 2)
	   (eq? (first x) 'reverse)
	   (loop (second x))))))

(define (backpropagator-match? u1 u2)
 (and
  (nonrecursive-closure-match? u1 u2)
  (every abstract-value-unionable?
	 (get-nonrecursive-closure-values u1)
	 (get-nonrecursive-closure-values u2))
  (let ((p?s (map abstract-value=?
		  (get-nonrecursive-closure-values u1)
		  (get-nonrecursive-closure-values u2))))
   (and (= (countq #t p?s) (- (length (get-nonrecursive-closure-values u1)) 1))
	(backpropagator-variable?
	 (list-ref (free-variables (nonrecursive-closure-lambda-expression u1))
		   (positionq #f p?s)))
	(backpropagator-variable?
	 (list-ref (free-variables (nonrecursive-closure-lambda-expression u2))
		   (positionq #f p?s)))))))

(define (limit-backpropagator-depth v)
 (limit-depth
  *backpropagator-depth-limit* backpropagator-match? backpropagator? v))

(define (limit-closure-depth v)
 (limit-depth *closure-depth-limit* closure-match? closure? v))

(define (limit-perturbation-tagged-value-depth v)
 (limit-depth *perturbation-tagged-value-depth-limit*
	      (lambda (u1 u2) #t)
	      perturbation-tagged-value?
	      v))

(define (limit-bundle-depth v)
 (limit-depth *bundle-depth-limit* (lambda (u1 u2) #t) bundle? v))

(define (limit-sensitivity-tagged-value-depth v)
 (limit-depth *sensitivity-tagged-value-depth-limit*
	      (lambda (u1 u2) #t)
	      sensitivity-tagged-value?
	      v))

(define (limit-reverse-tagged-value-depth v)
 (limit-depth *reverse-tagged-value-depth-limit*
	      (lambda (u1 u2) #t)
	      reverse-tagged-value?
	      v))

(define (limit-tagged-pair-depth v)
 (limit-depth *tagged-pair-depth-limit*
	      (lambda (u1 u2)
	       (equal-tags? (tagged-pair-tags u1) (tagged-pair-tags u2)))
	      tagged-pair?
	      v))

(define (widen-abstract-value v)
 (let ((v (canonize-and-maybe-intern-abstract-value v)))
  (cond
   ((and (nonrecursive-closure? v) (nonrecursive-closure-widen v))
    (nonrecursive-closure-widen v))
   ((and (recursive-closure? v) (recursive-closure-widen v))
    (recursive-closure-widen v))
   ((and (perturbation-tagged-value? v) (perturbation-tagged-value-widen v))
    (perturbation-tagged-value-widen v))
   ((and (bundle? v) (bundle-widen v)) (bundle-widen v))
   ((and (sensitivity-tagged-value? v) (sensitivity-tagged-value-widen v))
    (sensitivity-tagged-value-widen v))
   ((and (reverse-tagged-value? v) (reverse-tagged-value-widen v))
    (reverse-tagged-value-widen v))
   ((and (tagged-pair? v) (tagged-pair-widen v)) (tagged-pair-widen v))
   ((and (union? v) (union-widen v)) (union-widen v))
   (else
    (let ((v-prime
	   (let loop ((v v))
	    (let ((v-prime (limit-tagged-pair-depth
			    (limit-reverse-tagged-value-depth
			     (limit-sensitivity-tagged-value-depth
			      (limit-bundle-depth
			       (limit-perturbation-tagged-value-depth
				(limit-backpropagator-depth
				 (limit-closure-depth
				  (limit-tagged-pair-width
				   (limit-reverse-tagged-value-width
				    (limit-sensitivity-tagged-value-width
				     (limit-bundle-width
				      (limit-perturbation-tagged-value-width
				       (limit-closure-width v)))))))))))))))
	     (if (abstract-value=? v v-prime)
		 (let ((v-prime (limit-real-width v)))
		  (assert (abstract-value-subset? v v-prime))
		  v-prime)
		 (loop v-prime))))))
     (cond
      ((nonrecursive-closure? v) (set-nonrecursive-closure-widen! v v-prime))
      ((recursive-closure? v) (set-recursive-closure-widen! v v-prime))
      ((perturbation-tagged-value? v)
       (set-perturbation-tagged-value-widen! v v-prime))
      ((bundle? v) (set-bundle-widen! v v-prime))
      ((sensitivity-tagged-value? v)
       (set-sensitivity-tagged-value-widen! v v-prime))
      ((reverse-tagged-value? v) (set-reverse-tagged-value-widen! v v-prime))
      ((tagged-pair? v) (set-tagged-pair-widen! v v-prime))
      ((union? v) (set-union-widen! v v-prime)))
     v-prime)))))

;;; Abstract Evaluator

(define (abstract-eval1 e vs)
 ;; The abstract values in vs might violate the syntactic constraints. We adopt
 ;; the constraint that all abstract values in all environment bindings satisfy
 ;; the syntactic constraints. We widen here so that we compare widened values
 ;; to widened values.
 (let ((vs (map widen-abstract-value vs)))
  (assert (<= (count-if
	       (lambda (b)
		(abstract-environment=? vs (environment-binding-values b)))
	       (expression-environment-bindings e))
	      1))
  (let ((b (find-if
	    (lambda (b)
	     (abstract-environment=? vs (environment-binding-values b)))
	    (expression-environment-bindings e))))
   (if b (environment-binding-value b) (empty-abstract-value)))))

(define (abstract-destructure p v)
 ;; The assumption is that v doesn't violate the syntactic constraints.
 (cond
  ((constant-expression? p)
   (cond
    ((union? v)
     (map-reduce
      append '() (lambda (u) (abstract-destructure p u)) (union-members v)))
    ((abstract-value=?
      ;; This can widen when the constant expression value violates the
      ;; syntactic constraints (presumably tagged pair depth limit). This would
      ;; correspond to the call A to c:widen in generate-destructure.
      (widen-abstract-value
       (concrete-value->abstract-value (constant-expression-value p)))
      v)
     '(()))
    ((abstract-value-nondisjoint?
      ;; This can widen when the constant expression value violates the
      ;; syntactic constraints (presumably tagged pair depth limit). This would
      ;; correspond to the call A to c:widen in generate-destructure.
      (widen-abstract-value
       (concrete-value->abstract-value (constant-expression-value p)))
      v)
     (compile-time-warning "Argument might not be an equivalent value"
			   (constant-expression-value p)
			   v)
     '(()))
    (else (compile-time-warning "Argument might not be an equivalent value"
				(constant-expression-value p)
				v)
	  '())))
  ((variable-access-expression? p)
   (list (list (cons (variable-access-expression-variable p) v))))
  ((lambda-expression? p)
   (cond
    ((union? v)
     (map-reduce
      append '() (lambda (u) (abstract-destructure p u)) (union-members v)))
    ((and (nonrecursive-closure? v)
	  (dereferenced-expression-eqv?
	   p (nonrecursive-closure-lambda-expression v)))
     (list
      (map cons (parameter-variables p) (get-nonrecursive-closure-values v))))
    (else
     (compile-time-warning
      (format #f "Argument might not be a matching nonrecursive closure for ~s"
	      (externalize-expression p))
      v)
     '())))
  ((letrec-expression? p)
   (assert (and (variable-access-expression? (letrec-expression-body p))
		(memp variable=?
		      (variable-access-expression-variable
		       (letrec-expression-body p))
		      (letrec-expression-procedure-variables p))))
   (cond
    ((union? v)
     (map-reduce
      append '() (lambda (u) (abstract-destructure p u)) (union-members v)))
    ((and (recursive-closure? v)
	  (= (recursive-closure-index v)
	     (positionp variable=?
			(variable-access-expression-variable
			 (letrec-expression-body p))
			(letrec-expression-procedure-variables p)))
	  (= (vector-length
	      (recursive-closure-procedure-variables v))
	     (length (letrec-expression-procedure-variables p)))
	  (= (vector-length
	      (recursive-closure-lambda-expressions v))
	     (length (letrec-expression-lambda-expressions p)))
	  (every dereferenced-expression-eqv?
		 (vector->list (recursive-closure-lambda-expressions v))
		 (letrec-expression-lambda-expressions p)))
     (list
      (map cons (parameter-variables p) (get-recursive-closure-values v))))
    (else
     (compile-time-warning
      (format #f "Argument might not be a matching recursive closure for ~s"
	      (externalize-expression p))
      v)
     '())))
  ((cons-expression? p)
   (cond
    ((union? v)
     (map-reduce
      append '() (lambda (u) (abstract-destructure p u)) (union-members v)))
    ((and (tagged-pair? v)
	  (equal-tags? (cons-expression-tags p) (tagged-pair-tags v)))
     (cross-product
      append
      (abstract-destructure (cons-expression-car p) (get-tagged-pair-car v))
      (abstract-destructure (cons-expression-cdr p) (get-tagged-pair-cdr v))))
    (else
     (compile-time-warning
      (format #f "Argument might not be a matching tagged pair with tags ~s"
	      (cons-expression-tags p))
      v)
     '())))
  (else (internal-error))))

(define (construct-abstract-environment u1 alist)
 ;; We don't need to enforce the constraint that the abstract values in the
 ;; result environment not violate the syntactic constraints since the result
 ;; environment is only passed to abstract-eval1, abstract-eval-prime!,
 ;; all-instances1-instances2, generate-letrec-bindings, and
 ;; generate-expression and the constraint is enforced there.
 (assert (not (union? u1)))
 (cond
  ((nonrecursive-closure? u1)
   (map (lambda (x)
	 (let ((result (assp variable=? x alist)))
	  (if result
	      (cdr result)
	      (list-ref
	       (get-nonrecursive-closure-values u1)
	       (positionp variable=? x (nonrecursive-closure-variables u1))))))
	(free-variables (lambda-expression-body
			 (nonrecursive-closure-lambda-expression u1)))))
  ((recursive-closure? u1)
   (map (lambda (x)
	 (let ((result (assp variable=? x alist)))
	  (cond
	   (result (cdr result))
	   ((some-vector (lambda (x1) (variable=? x x1))
			 (recursive-closure-procedure-variables u1))
	    ;; This may create an abstract value that violates the syntactic
	    ;; constraints.
	    (new-recursive-closure
	     (get-recursive-closure-values u1)
	     (recursive-closure-procedure-variables u1)
	     (recursive-closure-lambda-expressions u1)
	     (positionp-vector
	      variable=? x (recursive-closure-procedure-variables u1))))
	   (else
	    (list-ref
	     (get-recursive-closure-values u1)
	     (positionp variable=? x (recursive-closure-variables u1)))))))
	(free-variables (lambda-expression-body
			 (vector-ref (recursive-closure-lambda-expressions u1)
				     (recursive-closure-index u1))))))
  (else (internal-error))))

(define (construct-abstract-environments u1 v2)
 (assert (not (union? u1)))
 (map (lambda (alist) (construct-abstract-environment u1 alist))
      (abstract-destructure (closure-parameter u1) v2)))

(define (abstract-apply v1 v2)
 (if (empty-abstract-value? v2)
     v2
     (map-union
      (lambda (u1)
       (cond
	((primitive-procedure? u1) ((primitive-procedure-procedure u1) v2))
	((closure? u1)
	 (cond
	  ((every-value-tags
	    (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
	   (unionize (map (lambda (vs) (abstract-eval1 (closure-body u1) vs))
			  (construct-abstract-environments u1 v2))))
	  ((some-value-tags
	    (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
	   (compile-time-warning
	    "Argument might have wrong type for target" u1 v2)
	   (unionize (map (lambda (vs) (abstract-eval1 (closure-body u1) vs))
			  (construct-abstract-environments u1 v2))))
	  (else (compile-time-warning
		 "Argument might have wrong type for target" u1 v2))))
	(else (compile-time-warning "Target might not be a procedure" u1))))
      v1)))

(define (enqueue! e)
 (unless (expression-enqueue? e)
  (set-expression-enqueue?! e #t)
  (set! *queue* (cons e *queue*))))

(define (abstract-eval! e)
 (cond
  ((application? e)
   (for-each (lambda (b)
	      (abstract-apply-prime!
	       e
	       (abstract-eval1
		(application-callee e)
		(restrict-environment
		 (environment-binding-values b) e application-callee))
	       (abstract-eval1
		(application-argument e)
		(restrict-environment
		 (environment-binding-values b) e application-argument))))
	     (expression-environment-bindings e))
   (for-each
    (lambda (b)
     ;; This corresponds to call B to c:widen in generate-expression.
     (let ((v (widen-abstract-value
	       ;; Need to refresh my memory as to why this union is needed.
	       (abstract-value-union
		(environment-binding-value b)
		(abstract-apply
		 (abstract-eval1
		  (application-callee e)
		  (restrict-environment
		   (environment-binding-values b) e application-callee))
		 (abstract-eval1
		  (application-argument e)
		  (restrict-environment
		   (environment-binding-values b) e application-argument)))))))
      ;; With the above union the old value will always be a subset of the new
      ;; value by a precise calculation but might not be given that the subset
      ;; calculation is imprecise. Need to document example where this occurs.
      (unless (abstract-value-subset? v (environment-binding-value b))
       (set-environment-binding-value! b v)
       (for-each enqueue! (expression-parents e)))))
    (expression-environment-bindings e)))
  ((letrec-expression? e)
   (for-each
    (lambda (b)
     ;; This corresponds to call C to c:widen in generate-expression.
     (let ((v (widen-abstract-value
	       ;; See the above note.
	       (abstract-value-union
		(environment-binding-value b)
		(abstract-eval1 (letrec-expression-body e)
				(letrec-nested-environment
				 (environment-binding-values b) e))))))
      ;; See the above note.
      (unless (abstract-value-subset? v (environment-binding-value b))
       (set-environment-binding-value! b v)
       (for-each enqueue! (expression-parents e)))))
    (expression-environment-bindings e)))
  ((cons-expression? e)
   (for-each
    (lambda (b)
     (let ((v1 (abstract-eval1
		(cons-expression-car e)
		(restrict-environment
		 (environment-binding-values b) e cons-expression-car)))
	   (v2 (abstract-eval1
		(cons-expression-cdr e)
		(restrict-environment
		 (environment-binding-values b) e cons-expression-cdr))))
      (cond
       ((and
	 (every-value-tags
	  (lambda (tags1) (prefix-tags? (cons-expression-tags e) tags1)) v1)
	 (every-value-tags
	  (lambda (tags2) (prefix-tags? (cons-expression-tags e) tags2)) v2))
	;; This can widen when the tagged pair created violates the syntactic
	;; constraints (presumably tagged pair depth limit or some width
	;; limit). This corresponds to call D to c:widen in
	;; generate-expression.
	(let ((v (widen-abstract-value
		  ;; See the above note.
		  (abstract-value-union
		   (environment-binding-value b)
		   (new-tagged-pair (cons-expression-tags e) v1 v2)))))
	 ;; See the above note.
	 (unless (abstract-value-subset? v (environment-binding-value b))
	  (set-environment-binding-value! b v)
	  (for-each enqueue! (expression-parents e)))))
       ((and
	 (some-value-tags
	  (lambda (tags1) (prefix-tags? (cons-expression-tags e) tags1)) v1)
	 (some-value-tags
	  (lambda (tags2) (prefix-tags? (cons-expression-tags e) tags2)) v2))
	(unless (every-value-tags
		 (lambda (tags1) (prefix-tags? (cons-expression-tags e) tags1))
		 v1)
	 (compile-time-warning
	  (format #f
		  "CAR argument might have wrong type for target with tags ~s"
		  (cons-expression-tags e))
	  v1))
	(unless (every-value-tags
		 (lambda (tags2) (prefix-tags? (cons-expression-tags e) tags2))
		 v2)
	 (compile-time-warning
	  (format #f
		  "CDR argument might have wrong type for target with tags ~s"
		  (cons-expression-tags e))
	  v2))
	;; This can widen when the tagged pair created violates the syntactic
	;; constraints (presumably tagged pair depth limit or some width
	;; limit). This corresponds to call D to c:widen in
	;; generate-expression.
	(let ((v (widen-abstract-value
		  ;; See the above note.
		  (abstract-value-union
		   (environment-binding-value b)
		   (new-tagged-pair (cons-expression-tags e) v1 v2)))))
	 ;; See the above note.
	 (unless (abstract-value-subset? v (environment-binding-value b))
	  (set-environment-binding-value! b v)
	  (for-each enqueue! (expression-parents e)))))
       (else
	(unless (every-value-tags
		 (lambda (tags1) (prefix-tags? (cons-expression-tags e) tags1))
		 v1)
	 (compile-time-warning
	  (format #f
		  "CAR argument might have wrong type for target with tags ~s"
		  (cons-expression-tags e))
	  v1))
	(unless (every-value-tags
		 (lambda (tags2) (prefix-tags? (cons-expression-tags e) tags2))
		 v2)
	 (compile-time-warning
	  (format #f
		  "CDR argument might have wrong type for target with tags ~s"
		  (cons-expression-tags e))
	  v2))))))
    (expression-environment-bindings e)))
  (else (internal-error))))

(define (abstract-apply-closure! e u1 v2)
 (assert (not (union? u1)))
 (for-each (lambda (vs)
	    (let ((e1 (closure-body u1)))
	     ;; See the note in abstract-eval-prime!
	     (unless (memp expression-eqv? e (expression-parents e1))
	      (set-expression-parents! e1 (cons e (expression-parents e1)))
	      (enqueue! e))
	     (abstract-eval-prime! e1 vs)))
	   (construct-abstract-environments u1 v2)))

(define (abstract-apply-prime! e v1 v2)
 (unless (empty-abstract-value? v2)
  (for-each
   (lambda (u1)
    (cond ((primitive-procedure? u1)
	   ;; needs work: Should put this into slots of the primitive
	   ;;             procedures.
	   (when (eq? (primitive-procedure-name u1) 'if-procedure)
	    ((ternary-prime
	      (lambda (v1 v2 v3)
	       ;; When v3 and/or v2 is not a procedure the warning is issued by
	       ;; abstract-apply. If it is a primitive procedure we don't have
	       ;; to do anything here. In practise, it will always be a
	       ;; nonrecursive closure unless the user calls if-procedure
	       ;; outside the context of the if macro.
	       (if (vlad-false? v1)
		   (when (closure? v3)
		    (abstract-apply-closure! e v3 (vlad-empty-list)))
		   (when (closure? v2)
		    (abstract-apply-closure! e v2 (vlad-empty-list)))))
	      "if-procedure")
	     v2)))
	  ((closure? u1)
	   (cond ((every-value-tags
		   (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
		  (abstract-apply-closure! e u1 v2))
		 ((some-value-tags
		   (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
		  (compile-time-warning
		   "Argument might have wrong type for target" u1 v2)
		  (abstract-apply-closure! e u1 v2))
		 (else (compile-time-warning
			"Argument might have wrong type for target" u1 v2))))
	  (else (compile-time-warning "Target might not be a procedure" u1))))
   (union-members v1))))

(define (abstract-eval-prime! e vs)
 ;; Can't give an error if entry already exists since we call this
 ;; indiscriminantly in abstract-apply-prime!.
 ;; The abstract values in vs might violate the syntactic constraints. We adopt
 ;; the constraint that all abstract values in all environment bindings satisfy
 ;; the syntactic constraints. We widen here so that we compare widened values
 ;; to widened values. We also take care below to widen appropriately but delay
 ;; widening as long as possible.
 (let loop ((e e) (vs vs))
  (unless (let ((vs (map widen-abstract-value vs)))
	   (some (lambda (b)
		  (abstract-environment=? vs (environment-binding-values b)))
		 (expression-environment-bindings e)))
   (cond
    ((constant-expression? e)
     (set-expression-environment-bindings!
      e
      (cons (make-environment-binding
	     (map widen-abstract-value vs)
	     ;; This can widen when the constant expression value violates the
	     ;; syntactic constraints (presumably tagged pair depth limit).
	     ;; This corresponds to call E to c:widen in generate-expression.
	     (widen-abstract-value
	      (concrete-value->abstract-value (constant-expression-value e))))
	    (expression-environment-bindings e)))
     (for-each enqueue! (expression-parents e)))
    ((variable-access-expression? e)
     (set-expression-environment-bindings!
      e
      (let ((vs (map widen-abstract-value vs)))
       ;; There does not need to be a corresponding call F to c:widen in
       ;; generate-expression.
       (cons (make-environment-binding vs (first vs))
	     (expression-environment-bindings e))))
     (for-each enqueue! (expression-parents e)))
    ((lambda-expression? e)
     (set-expression-environment-bindings!
      e
      (cons (make-environment-binding
	     (map widen-abstract-value vs)
	     ;; This can widen when the closure created violates the syntactic
	     ;; constraints (presumably closure depth limit or backpropagator
	     ;; depth limit). Note that we don't widen vs before creating the
	     ;; closure. This corresponds to call G to c:widen in
	     ;; generate-expression.
	     (widen-abstract-value (new-nonrecursive-closure vs e)))
	    (expression-environment-bindings e)))
     (for-each enqueue! (expression-parents e)))
    ((application? e)
     (set-expression-environment-bindings!
      e
      (cons (make-environment-binding
	     (map widen-abstract-value vs) (empty-abstract-value))
	    (expression-environment-bindings e)))
     ;; Can't give an error if parent already in list since could have done
     ;; this for a different context.
     (unless (memp
	      expression-eqv? e (expression-parents (application-callee e)))
      (set-expression-parents!
       (application-callee e)
       (cons e (expression-parents (application-callee e)))))
     (unless (memp
	      expression-eqv? e (expression-parents (application-argument e)))
      (set-expression-parents!
       (application-argument e)
       (cons e (expression-parents (application-argument e)))))
     (loop (application-callee e)
	   (restrict-environment vs e application-callee))
     (loop (application-argument e)
	   (restrict-environment vs e application-argument))
     (enqueue! e))
    ((letrec-expression? e)
     (set-expression-environment-bindings!
      e
      (cons (make-environment-binding
	     (map widen-abstract-value vs) (empty-abstract-value))
	    (expression-environment-bindings e)))
     ;; Ditto.
     (unless (memp
	      expression-eqv? e (expression-parents (letrec-expression-body e)))
      (set-expression-parents!
       (letrec-expression-body e)
       (cons e (expression-parents (letrec-expression-body e)))))
     (loop (letrec-expression-body e)
	   ;; Note that we don't widen vs before passing to
	   ;; letrec-nested-environment and rely on abstract-eval-prime! to
	   ;; enforce the syntactic constraints.
	   (letrec-nested-environment vs e))
     (enqueue! e))
    ((cons-expression? e)
     (set-expression-environment-bindings!
      e
      (cons (make-environment-binding
	     (map widen-abstract-value vs) (empty-abstract-value))
	    (expression-environment-bindings e)))
     ;; Ditto.
     (unless (memp
	      expression-eqv? e (expression-parents (cons-expression-car e)))
      (set-expression-parents!
       (cons-expression-car e)
       (cons e (expression-parents (cons-expression-car e)))))
     (unless (memp
	      expression-eqv? e (expression-parents (cons-expression-cdr e)))
      (set-expression-parents!
       (cons-expression-cdr e)
       (cons e (expression-parents (cons-expression-cdr e)))))
     (loop (cons-expression-car e)
	   (restrict-environment vs e cons-expression-car))
     (loop (cons-expression-cdr e)
	   (restrict-environment vs e cons-expression-cdr))
     (enqueue! e))
    (else (internal-error))))))

(define (deep-empty-abstract-value? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  24
  (let outer ((v v) (vs '()) (k (lambda (r? vs) r?)))
   (cond ((real? v) (k #f vs))
	 ((memq v vs) (k #f vs))
	 ((union? v)
	  (if (null? (union-members v))
	      (k #t vs)
	      (let inner ((us (union-members v)) (vs (cons v vs)))
	       (if (null? us)
		   (k #f vs)
		   (outer (first us)
			  vs
			  (lambda (r? vs)
			   (if r? (k #t vs) (inner (rest us) vs))))))))
	 ((scalar-value? v) (k #f vs))
	 (else (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
		(if (null? vs1)
		    (k #f vs)
		    (outer (first vs1)
			   vs
			   (lambda (r? vs)
			    (if r? (k #t vs) (inner (rest vs1) vs)))))))))))

(define (value-contains-union? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  25
  (let outer ((v v) (vs '()) (k (lambda (r? vs) r?)))
   (cond ((real? v) (k #f vs))
	 ((memq v vs) (k #f vs))
	 ((union? v)
	  (if (>= (length (union-members v)) 2)
	      (k #t vs)
	      (let inner ((us (union-members v)) (vs (cons v vs)))
	       (if (null? us)
		   (k #f vs)
		   (outer (first us)
			  vs
			  (lambda (r? vs)
			   (if r? (k #t vs) (inner (rest us) vs))))))))
	 ((scalar-value? v) (k #f vs))
	 (else (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
		(if (null? vs1)
		    (k #f vs)
		    (outer (first vs1)
			   vs
			   (lambda (r? vs)
			    (if r? (k #t vs) (inner (rest vs1) vs)))))))))))

(define (unions-in-abstract-value v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  26
  (let outer ((v v) (vs '()) (n 0) (k (lambda (n vs) n)))
   (cond ((real? v) (k n vs))
	 ((memq v vs) (k n vs))
	 ((union? v)
	  (let inner ((us (union-members v))
		      (vs (cons v vs))
		      (n (+ n (if (>= (length (union-members v)) 2) 1 0))))
	   (if (null? us)
	       (k n vs)
	       (outer (first us)
		      vs
		      n
		      (lambda (n vs) (inner (rest us) vs n))))))
	 ((scalar-value? v) (k n vs))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   (vs (cons v vs))
			   (n n))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (type-in-abstract-value type? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  27
  (let outer ((v v) (vs '()) (n '()) (k (lambda (n vs) n)))
   (cond ((memq v vs) (k n vs))
	 ((union? v)
	  (let inner ((us (union-members v))
		      (vs (cons v vs))
		      (n (if (type? v) (cons v n) n)))
	   (if (null? us)
	       (k n vs)
	       (outer (first us)
		      vs
		      n
		      (lambda (n vs) (inner (rest us) vs n))))))
	 ((scalar-value? v) (k (if (type? v) (cons v n) n) vs))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   (vs (cons v vs))
			   (n (if (type? v) (cons v n) n)))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (concrete-reals-in-abstract-value v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  28
  (let outer ((v v) (vs '()) (n '()) (k (lambda (n vs) n)))
   (cond ((real? v) (k (if (memv v n) n (cons v n)) vs))
	 ((memq v vs) (k n vs))
	 ((union? v)
	  (let inner ((us (union-members v)) (vs (cons v vs)) (n n))
	   (if (null? us)
	       (k n vs)
	       (outer (first us)
		      vs
		      n
		      (lambda (n vs) (inner (rest us) vs n))))))
	 ((scalar-value? v) (k n vs))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   (vs (cons v vs))
			   (n n))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (value-size v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  29
  (let outer ((v v) (vs '()) (n 0) (k (lambda (n vs) n)))
   (cond ((memq v vs) (k n vs))
	 ;; We intentionally omit the special case for real here but not
	 ;; elsewhere.
	 ((union? v)
	  (let inner ((us (union-members v)) (vs (cons v vs)) (n (+ n 1)))
	   (if (null? us)
	       (k n vs)
	       (outer (first us) vs n (lambda (n vs) (inner (rest us) vs n))))))
	 ;; We intentionally cons here but not elsewhere.
	 ((scalar-value? v) (k (+ n 1) (cons v vs)))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   ;; We intentionally cons here but not elsewhere.
			   (vs (cons v vs))
			   (n (+ n 1)))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (value-max-width v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  30
  (let outer ((v v) (vs '()) (n 0) (k (lambda (n vs) n)))
   (cond ((real? v) (k (max n 1) vs))
	 ((memq v vs) (k n vs))
	 ((union? v)
	  (let inner ((us (union-members v))
		      (vs (cons v vs))
		      (n (max n (length (union-members v)))))
	   (if (null? us)
	       (k n vs)
	       (outer (first us) vs n (lambda (n vs) (inner (rest us) vs n))))))
	 ((scalar-value? v) (k (max n 1) vs))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   (vs (cons v vs))
			   (n (max n 1)))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (analysis-size)
 (map-reduce +
	     0
	     (lambda (e) (length (expression-environment-bindings e)))
	     *expressions*))

(define (max-flow-size)
 (map-reduce max
	     minus-infinity
	     (lambda (e) (length (expression-environment-bindings e)))
	     *expressions*))

(define (analysis-contains-union?)
 (some (lambda (e)
	(some (lambda (b)
	       (or (some value-contains-union?
			 (environment-binding-values b))
		   (value-contains-union? (environment-binding-value b))))
	      (expression-environment-bindings e)))
       *expressions*))

(define (unions-in-analysis)
 (map-reduce
  +
  0
  (lambda (e)
   (map-reduce
    +
    0
    (lambda (b)
     (+ (map-reduce
	 + 0 unions-in-abstract-value (environment-binding-values b))
	(unions-in-abstract-value (environment-binding-value b))))
    (expression-environment-bindings e)))
  *expressions*))

(define (concrete-reals-in-analysis)
 (map-reduce
  unionv
  '()
  (lambda (e)
   (map-reduce
    unionv
    '()
    (lambda (b)
     (unionv
      (map-reduce unionv
		  '()
		  concrete-reals-in-abstract-value
		  (environment-binding-values b))
      (concrete-reals-in-abstract-value (environment-binding-value b))))
    (expression-environment-bindings e)))
  *expressions*))

(define (bottoms-in-analysis)
 (map-reduce
  +
  0
  (lambda (e)
   (count-if (lambda (b) (empty-abstract-value? (environment-binding-value b)))
	     (expression-environment-bindings e)))
  *expressions*))

(define (analysis-max-size)
 (map-reduce
  max
  0
  (lambda (e)
   (map-reduce
    max
    0
    (lambda (b)
     (max (map-reduce max 0 value-size (environment-binding-values b))
	  (value-size (environment-binding-value b))))
    (expression-environment-bindings e)))
  *expressions*))

(define (analysis-max-width)
 (map-reduce
  max
  0
  (lambda (e)
   (map-reduce
    max
    0
    (lambda (b)
     (max (map-reduce max 0 value-max-width (environment-binding-values b))
	  (value-max-width (environment-binding-value b))))
    (expression-environment-bindings e)))
  *expressions*))

(define (check-abstract-value! v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  31
  (let outer ((v v) (vs '()) (k (lambda (vs) #f)))
   (cond ((real? v) (k vs))
	 ((memq v vs) (k vs))
	 ((union? v)
	  (assert (and (not (eq? (union-values v) 'unfilled))
		       (memq v *unions*)
		       (not (some union? (get-union-values v)))
		       (not (= (length (get-union-values v)) 1))))
	  (for-each-indexed
	   (lambda (u1 i1)
	    (for-each-indexed
	     (lambda (u2 i2)
	      (assert (or (= i1 i2) (not (abstract-value-subset? u1 u2)))))
	     (union-members v)))
	   (union-members v))
	  (let inner ((us (union-members v)) (vs (cons v vs)))
	   (if (null? us)
	       (k vs)
	       (outer (first us) vs (lambda (vs) (inner (rest us) vs))))))
	 ((scalar-value? v) (k vs))
	 (else
	  (cond
	   ((nonrecursive-closure? v)
	    (assert (and (not (eq? (nonrecursive-closure-values v) 'unfilled))
			 (memq v
			       (lambda-expression-nonrecursive-closures
				(nonrecursive-closure-lambda-expression v))))))
	   ((recursive-closure? v)
	    (assert
	     (and
	      (not (eq? (recursive-closure-values v) 'unfilled))
	      (memq
	       v
	       (lambda-expression-recursive-closures
		(vector-ref (recursive-closure-lambda-expressions v) 0))))))
	   ((perturbation-tagged-value? v)
	    (assert
	     (and (not (eq? (perturbation-tagged-value-primal v) 'unfilled))
		  (memq v *perturbation-tagged-values*))))
	   ((bundle? v)
	    (assert (and (not (eq? (bundle-primal v) 'unfilled))
			 (not (eq? (bundle-tangent v) 'unfilled))
			 (memq v *bundles*))))
	   ((sensitivity-tagged-value? v)
	    (assert
	     (and (not (eq? (sensitivity-tagged-value-primal v) 'unfilled))
		  (memq v *sensitivity-tagged-values*))))
	   ((reverse-tagged-value? v)
	    (assert (and (not (eq? (reverse-tagged-value-primal v) 'unfilled))
			 (memq v *reverse-tagged-values*))))
	   ((tagged-pair? v)
	    (assert (and (not (eq? (tagged-pair-car v) 'unfilled))
			 (not (eq? (tagged-pair-cdr v) 'unfilled))
			 (memq v *tagged-pairs*)))))
	  (assert (not (some empty-abstract-value? (aggregate-value-values v))))
	  (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
	   (if (null? vs1)
	       (k vs)
	       (outer (first vs1)
		      vs
		      (lambda (vs) (inner (rest vs1) vs))))))))))

(define (check-analysis!)
 (for-each
  (lambda (e)
   (for-each (lambda (b)
	      (for-each check-abstract-value! (environment-binding-values b))
	      (check-abstract-value! (environment-binding-value b)))
	     (expression-environment-bindings e)))
  *expressions*))

(define (verbosity)
 (format #t
	 "expressions: ~s, |analysis|=~s, max flow size: ~s, |queue|=~s~%unions: ~s, bottoms: ~s, max size: ~s, max width: ~s~%concrete reals: ~s~%"
	 (count-if
	  (lambda (e) (not (null? (expression-environment-bindings e))))
	  *expressions*)
	 (analysis-size)
	 (max-flow-size)
	 (length *queue*)
	 (unions-in-analysis)
	 (bottoms-in-analysis)
	 (analysis-max-size)
	 (analysis-max-width)
	 (concrete-reals-in-analysis)))

(define (flow-analysis! e bs)
 (set! *abstract?* #t)
 (abstract-eval-prime!
  e
  (map (lambda (x)
	(value-binding-value
	 (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs)))
       (free-variables e)))
 (let loop ((i 0))
  (when (and *verbose* (not (zero? *verbose*)) (zero? (remainder i *verbose*)))
   (verbosity))
  (unless (null? *queue*)
   (let ((e (first *queue*)))
    (set! *queue* (rest *queue*))
    (assert (expression-enqueue? e))
    (set-expression-enqueue?! e #f)
    (abstract-eval! e))
   (loop (+ i 1))))
 (check-analysis!)
 (when *verbose* (verbosity)))

;;; Code Generator

;;; Identifiers
;;; x  argument for add#, minus#, times#, divide#, atantwo#, eq#, lt#
;;;    gt#, le#, ge#, iszero#, positive#, negative#, if_procedure#,
;;;    real#, write_real, write#, zero#, primal#, tangent#, and bundle#
;;; x  argument for unioner
;;; x  argument for widener
;;; x  result value in read_real
;;; x# variable name; # is variable index
;;; x# variable slot of closure struct; # is variable index
;;; x# letrec binding; # is variable index
;;; y  target temporary in function call dispatch
;;; u# union name; # is c:index
;;; s# struct name; # is c:index
;;;    union member name; # is c:index of member
;;; p  primal slot of bundle struct and slots of perturbation, sensitivity, and
;;;    reverse tagged value structs
;;; t  tangent slot of bundle struct
;;;    tag slot of a union
;;; a  car slot of pair struct
;;; d  cdr slot of pair struct
;;; w# widener name;  # is index of the widener-instance in widener-instances
;;; f# function name; # is index of the function-instance in function-instances
;;; m# constructor name; # is c:index of value being constructed
;;; m#_# unioner name; first # is c:index of value being
;;       constructed; second # is c:index of argument
;;; r  result value in constructor definition
;;; c  environment argument for f#
;;; The following are primitive names; # is c:index of argument
;;; add#
;;; minus#
;;; times#
;;; divide#
;;; atantwo#
;;; eq#
;;; lt#
;;; gt#
;;; le#
;;; ge#
;;; iszero#
;;; positive#
;;; negative#
;;; if_procedure#
;;; read_real
;;; real#
;;; write_real
;;; write#
;;; zero#
;;; perturb#
;;; unperturb#
;;; primal#
;;; tangent#
;;; bundle#
;;; sensitize#
;;; unsensitize#
;;; plus#
;;; starj#
;;; starj_inverse#
;;; main

;;; We box abstract values, not slots of aggregates, not arguments, not return
;;; values, not local variables, not type tags, and not unions.

;;; here I am: In all or almost all of the cases where we eliminate void
;;;            parameters or arguments or functions that return void results
;;;            we unsoundly removes code that might do I/O, signal an error, or
;;;            not terminate.

(define (void? v)
 (let ((p?
	(cond
	 ((union? v) (union-void? v))
	 ((abstract-real? v) #f)
	 ((scalar-value? v) #t)
	 ((nonrecursive-closure? v) (nonrecursive-closure-void? v))
	 ((recursive-closure? v) (recursive-closure-void? v))
	 ((perturbation-tagged-value? v) (perturbation-tagged-value-void? v))
	 ((bundle? v) (bundle-void? v))
	 ((sensitivity-tagged-value? v) (sensitivity-tagged-value-void? v))
	 ((reverse-tagged-value? v) (reverse-tagged-value-void? v))
	 ((tagged-pair? v) (tagged-pair-void? v))
	 (else (internal-error)))))
  (assert (boolean? p?))
  p?))

(define (deep-void? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  32
  (let loop ((v v) (cs '()) (k (lambda (r? cs) r?)))
   (cond ((memq v cs) (k #t cs))
	 ((union? v)
	  ;; The empty abstract value is not considered void. This is because
	  ;; void parameter/arguments are eliminated and we cannot do that for
	  ;; code that will issue an error. That is why the following is = and
	  ;; not <=.
	  (if (= (length (get-union-values v)) 1)
	      (every-cps loop (get-union-values v) (cons v cs) k)
	      (k #f cs)))
	 ((abstract-real? v) (k #f cs))
	 ((scalar-value? v) (k #t cs))
	 (else (every-cps loop (aggregate-value-values v) (cons v cs) k))))))

(define (determine-void?!)
 (for-each
  (lambda (e)
   (when (lambda-expression? e)
    (for-each (lambda (v) (set-nonrecursive-closure-void?! v (deep-void? v)))
	      (lambda-expression-nonrecursive-closures e))
    (for-each (lambda (v) (set-recursive-closure-void?! v (deep-void? v)))
	      (lambda-expression-recursive-closures e))))
  *expressions*)
 (for-each (lambda (v) (set-perturbation-tagged-value-void?! v (deep-void? v)))
	   *perturbation-tagged-values*)
 (for-each (lambda (v) (set-bundle-void?! v (deep-void? v))) *bundles*)
 (for-each (lambda (v) (set-sensitivity-tagged-value-void?! v (deep-void? v)))
	   *sensitivity-tagged-values*)
 (for-each (lambda (v) (set-reverse-tagged-value-void?! v (deep-void? v)))
	   *reverse-tagged-values*)
 (for-each (lambda (v) (set-tagged-pair-void?! v (deep-void? v)))
	   *tagged-pairs*)
 (for-each (lambda (v) (set-union-void?! v (deep-void? v))) *unions*))

(define (union-abstract-values vs1 vs2) (unionp abstract-value=? vs1 vs2))

(define (all-abstract-values)
 (map-reduce
  union-abstract-values
  '()
  (lambda (e)
   (map-reduce union-abstract-values
	       '()
	       (lambda (b)
		(remove-duplicatesp abstract-value=?
				    (cons (environment-binding-value b)
					  (environment-binding-values b))))
	       (expression-environment-bindings e)))
  *expressions*))

(define (all-unary-abstract-subvalues descend? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  33
  (let outer ((v v) (vs '()) (n '()) (k (lambda (n vs) n)))
   (cond ((memq v vs) (k n vs))
	 ((union? v)
	  (let inner ((us (get-union-values v))
		      (vs (cons v vs))
		      (n (adjoinp abstract-value=? v n)))
	   (if (null? us)
	       (k n vs)
	       (outer (first us)
		      vs
		      n
		      (lambda (n vs) (inner (rest us) vs n))))))
	 ;; here I am: Need to return an empty abstract value for certain inputs
	 ;;            to certain AD primitives.
	 ((or (scalar-value? v) (not (descend? v)))
	  (k (adjoinp abstract-value=? v n) vs))
	 (else (let inner ((vs1 (aggregate-value-values v))
			   (vs (cons v vs))
			   (n (adjoinp abstract-value=? v n)))
		(if (null? vs1)
		    (k n vs)
		    (outer (first vs1)
			   vs
			   n
			   (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (all-binary-abstract-subvalues
	 descend? f? f f-inverse aggregates-match? v)
 ;; This is written in CPS so as not to break structure sharing.
 ;; here I am: The results of f and f-inverse might violate the syntactic
 ;;            constraints.
 (define (outer1 v vs cs n k)
  (cond ((memq v vs) (k n vs cs))
	((union? v)
	 (let inner ((us (get-union-values v))
		     (vs (cons v vs))
		     (cs cs)
		     (n (adjoinp abstract-value=? v n)))
	  (if (null? us)
	      (k n vs cs)
	      (outer1 (first us)
		      vs
		      cs
		      n
		      (lambda (n vs cs) (inner (rest us) vs cs n))))))
	((vlad-pair? v) (outer2 (vlad-car v) (vlad-cdr v) vs cs n k))
	(else (k n vs cs))))
 (define (outer2 v1 v2 vs cs n k)
  (cond ((some (lambda (c) (and (eq? (car c) v1) (eq? (cdr c) v2))) cs)
	 (k n vs cs))
	((union? v1)
	 (let inner ((us (get-union-values v1))
		     (vs vs)
		     (cs (cons (cons v1 v2) cs))
		     (n (adjoinp abstract-value=? (vlad-cons v1 v2) n)))
	  (if (null? us)
	      (k n vs cs)
	      (outer2 (first us)
		      v2
		      vs
		      cs
		      n
		      (lambda (n vs cs)
		       ;; This is needed because of a bug in Scheme->C
		       (let ((result (inner (rest us) vs cs n))) result))))))
	((union? v2)
	 (let inner ((us (get-union-values v2))
		     (vs vs)
		     (cs (cons (cons v1 v2) cs))
		     (n (adjoinp abstract-value=? (vlad-cons v1 v2) n)))
	  (if (null? us)
	      (k n vs cs)
	      (outer2 v1
		      (first us)
		      vs
		      cs
		      n
		      (lambda (n vs cs) (inner (rest us) vs cs n))))))
	;; The calls to f and f-inverse should never return an empty abstract
	;; value. The call to f-inverse might issue "might" warnings.
	((and (f? v2) (union? (f-inverse v2)))
	 (let inner ((us (get-union-values (f-inverse v2)))
		     (vs vs)
		     (cs (cons (cons v1 v2) cs))
		     (n (adjoinp abstract-value=? (vlad-cons v1 v2) n)))
	  (if (null? us)
	      (k n vs cs)
	      (outer2 v1
		      (f (first us))
		      vs
		      cs
		      n
		      (lambda (n vs cs) (inner (rest us) vs cs n))))))
	;; here I am: Need to return an empty abstract value for nonconforming
	;;            inputs.
	((or (scalar-value? v1) (not (descend? v1)))
	 (k (adjoinp abstract-value=? (vlad-cons v1 v2) n) vs cs))
	((aggregates-match? v1 v2)
	 (let inner ((vs1 (aggregate-value-values v1))
		     (vs2 (aggregate-value-values v2))
		     (vs vs)
		     (cs (cons (cons v1 v2) cs))
		     (n (adjoinp abstract-value=? (vlad-cons v1 v2) n)))
	  (if (null? vs1)
	      (k n vs cs)
	      (outer2 (first vs1)
		      (first vs2)
		      vs
		      cs
		      n
		      (lambda (n vs cs)
		       (inner (rest vs1) (rest vs2) vs cs n))))))
	;; here I am: Need to return an empty abstract value for nonconforming
	;;            inputs.
	(else (k (adjoinp abstract-value=? (vlad-cons v1 v2) n) vs cs))))
 (time-it-bucket
  34
  (outer1 v '() '() '() (lambda (n vs cs) n))))

(define (feedback-topological-sort vertex=? before choose vertices)
 ;; Minimal feedback set is the problem of computing the smallest set of edges
 ;; to remove from a digraph to make it acyclic. It is NP complete. This solves
 ;; a related problem of finding a minimal set of vertices to remove from a
 ;; digraph to make it acyclic. I don't know if this problem is NP hard. This
 ;; is a greedy heuristic for solving this problem. It partitions vertices into
 ;; two sets, vertices1 and vertices2, where vertices2 is the set of removed
 ;; vertices and vertices1 is topologically sorted. (before vertex) returns the
 ;; vertices that must come before vertex.
 (let loop ((vertices vertices)
	    (vertices1 '())
	    (vertices2 '())
	    ;; edges is a list of pairs (vertex1 vertex2) where vertex1 must
	    ;; come before vertex2.
	    (edges (map-reduce
		    append
		    '()
		    (lambda (vertex2)
		     (map (lambda (vertex1) (list vertex1 vertex2))
			  (remove-if-not
			   (lambda (vertex1) (memp vertex=? vertex1 vertices))
			   (before vertex2))))
		    vertices)))
  ;; Each time through the loop the graph only contains edges that both enter
  ;; and leave vertices in vertices.
  (if (null? vertices)
      (list (reverse vertices1) vertices2)
      ;; vertices-prime is the set of vertices in vertices with no in-edges.
      (let ((vertices-prime
	     (set-differencep vertex=? vertices (map second edges))))
       (if (null? vertices-prime)
	   ;; Each time through the loop the graph only contains edges that
	   ;; both enter and leave vertices in l.
	   (let ((vertex
		  (let loop ((vertices vertices) (edges edges))
		   ;; vertices-prime is the set of vertices in vertices with
		   ;; out-edges.
		   (let ((vertices-prime
			  (intersectionp
			   vertex=? vertices (map first edges))))
		    (if (= (length vertices) (length vertices-prime))
			(choose vertices)
			(loop vertices-prime
			      ;; Update the graph to contain only edges that
			      ;; leave vertices in vertices-prime which is
			      ;; the new vertices.
			      (remove-if-not
			       (lambda (edge)
				(memp vertex=? (second edge) vertices-prime))
			       edges)))))))
	    (loop (removep vertex=? vertex vertices)
		  vertices1
		  (cons vertex vertices2)
		  ;; We are removing vertex from vertices so remove all edges
		  ;; entering or leaving vertex.
		  (remove-if (lambda (edge)
			      (or (vertex=? (first edge) vertex)
				  (vertex=? (second edge) vertex)))
			     edges)))
	   (loop (set-differencep vertex=? vertices vertices-prime)
		 (append vertices-prime vertices1)
		 vertices2
		 ;; We are removing vertices-prime from vertices so remove all
		 ;; edges leaving vertices-prime. Since vertices-prime=
		 ;; (set-differenceq vertices (map second edges)) there
		 ;; can be no edges entering vertices-prime.
		 (remove-if
		  (lambda (edge) (memp vertex=? (first edge) vertices-prime))
		  edges)))))))

(define (all-unary-ad s descend?)
 ;; This is called redundantly thrice, once in all-unary-ad-widener-instances,
 ;; once to generate declarations, and once to generate definitions.
 (map-reduce
  union-abstract-values
  '()
  (lambda (v) (all-unary-abstract-subvalues descend? v))
  (map-reduce
   union-abstract-values
   '()
   (lambda (e)
    (if (application? e)
	(remove-duplicatesp
	 abstract-value=?
	 (removeq #f
		  (map (lambda (b)
			(let ((v1 (abstract-eval1
				   (application-callee e)
				   (restrict-environment
				    (environment-binding-values b)
				    e
				    application-callee))))
			 (if (and (primitive-procedure? v1)
				  (eq? (primitive-procedure-name v1) s))
			     (abstract-eval1 (application-argument e)
					     (restrict-environment
					      (environment-binding-values b)
					      e
					      application-argument))
			     #f)))
		       (expression-environment-bindings e))))
	'()))
   *expressions*)))

(define (abstract-values-before v)
 (cond ((union? v) (get-union-values v))
       ((scalar-value? v) '())
       (else (aggregate-value-values v))))

(define (all-sorted-unary-ad s descend?)
 ;; This is called redundantly twice, once to generate declarations and once to
 ;; generate definitions.
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 ;; here I am: Need better choice function.
 (feedback-topological-sort
  abstract-value=? abstract-values-before first (all-unary-ad s descend?)))

(define (all-binary-ad s descend? f? f f-inverse aggregates-match?)
 ;; This is called redundantly thrice, once in all-binary-ad-widener-instances,
 ;; once to generate declarations, and once to generate definitions.
 (map-reduce
  union-abstract-values
  '()
  (lambda (v)
   (all-binary-abstract-subvalues descend? f? f f-inverse aggregates-match? v))
  (map-reduce
   union-abstract-values
   '()
   (lambda (e)
    (if (application? e)
	(remove-duplicatesp
	 abstract-value=?
	 (removeq #f
		  (map (lambda (b)
			(let ((v1 (abstract-eval1
				   (application-callee e)
				   (restrict-environment
				    (environment-binding-values b)
				    e
				    application-callee))))
			 (if (and (primitive-procedure? v1)
				  (eq? (primitive-procedure-name v1) s))
			     (abstract-eval1 (application-argument e)
					     (restrict-environment
					      (environment-binding-values b)
					      e
					      application-argument))
			     #f)))
		       (expression-environment-bindings e))))
	'()))
   *expressions*)))

(define (all-sorted-binary-ad
	 s descend? f? f f-inverse aggregates-match? before)
 ;; This is called redundantly twice, once to generate declarations and once to
 ;; generate definitions.
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (feedback-topological-sort
  abstract-value=?
  before
  ;; here I am: Need better choice function.
  first
  (all-binary-ad s descend? f? f f-inverse aggregates-match?)))

(define (binary-ad-argument-and-result-abstract-values g-value vs)
 ;; here I am: The result of g-value might violate syntactic constraints.
 (map-reduce union-abstract-values
	     '()
	     ;; The call to g-value might issue "might" warnings and might
	     ;; return an empty abstract value.
	     (lambda (v) (union-abstract-values (list v) (list (g-value v))))
	     vs))

(define (bundle-value v)
 ;; here I am: Needs to give a warning on a nonpair.
 ;; here I am: Might violate syntactic constraints.
 (unionize (map (lambda (u) (bundle (vlad-car u) (vlad-cdr u)))
		(remove-if-not vlad-pair? (union-members v)))))

(define (plus-value v)
 ;; here I am: Needs to give a warning on a nonpair.
 ;; here I am: Might violate syntactic constraints.
 (unionize (map (lambda (u) (plus (vlad-car u) (vlad-cdr u)))
		(remove-if-not vlad-pair? (union-members v)))))

(define (bundle-aggregates-match? v1 v2)
 (or (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (perturbation-parameter? (nonrecursive-closure-parameter v2))
	  (dereferenced-nonrecursive-closure-match? v1 (unperturb v2)))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (perturbation-parameter? (recursive-closure-parameter v2))
	  (dereferenced-recursive-closure-match? v1 (unperturb v2)))
     (and (tagged-pair? v1)
	  (tagged-pair? v2)
	  (tagged? 'perturbation (tagged-pair-tags v2))
	  (equal-tags? (tagged-pair-tags v1)
		       (remove-tag 'perturbation (tagged-pair-tags v2))))))

(define (plus-aggregates-match? v1 v2)
 (or (and (nonrecursive-closure? v1)
	  (nonrecursive-closure? v2)
	  (dereferenced-nonrecursive-closure-match? v1 v2))
     (and (recursive-closure? v1)
	  (recursive-closure? v2)
	  (dereferenced-recursive-closure-match? v1 v2))
     (and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
     (and (bundle? v1) (bundle? v2))
     (and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
     (and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
     (and (tagged-pair? v1)
	  (tagged-pair? v2)
	  (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2)))))

(define (all-nested-abstract-values widener-instances)
 (feedback-topological-sort
  abstract-value=?
  abstract-values-before
  (lambda (vs)
   (let ((v (find-if backpropagator? vs)))
    (assert v)
    v))
  (adjoinp
   abstract-value=?
   ;; We are lazy and always generate this. This is needed to generate
   ;; real_real and write_real when the program otherwise has no abstract
   ;; reals.
   (abstract-real)
   (adjoinp
    abstract-value=?
    ;; We are lazy and always generate this. This is only needed if (a
    ;; potentially internal recursive call to) an AD primitive can give a
    ;; run-time error. All non-AD primitives that issue errors have C return
    ;; types corresponding to (abstract-real) or (abstract-boolean). And
    ;; currently we don't handle programs that contain expressions with empty
    ;; abstract values. Such can result from non-AD primitives that return
    ;; empty abstract values (even though the C code generated for those
    ;; primitives has non-empty return types). And from AD primitives that
    ;; return empty abstract values. And from destructuring errors. And from
    ;; invalid calls. And from calls that can never return (either because they
    ;; yield errors or involve infinite recursion). Flow analysis will yield an
    ;; empy abstract value in all of the above cases except for an internal
    ;; recursive call to an AD primitive. all-binary-abstract-subvalues doesn't
    ;; currently handle the cases requiring returning of empty abstract values.
    ;; binary-ad-argument-and-result-abstract-values does handle this case.
    ;; And currently, indicated by the comment below, unary AD primitives are
    ;; handled by a mechanism that is not aware of the particular error
    ;; characteristics of each primitive. And neither is
    ;; all-unary-abstract-subvalues. So for now we punt and always generate the
    ;; empty abstract value.
    (empty-abstract-value)
    (map-reduce
     union-abstract-values
     '()
     (lambda (v) (all-unary-abstract-subvalues (lambda (v) #t) v))
     ;; This assumes that the abstract values of the arguments of all internal
     ;; recursive calls to AD primitives are generated through
     ;; all-unary-abstract-subvalues.
     (union-abstract-values
      (union-abstract-values
       (union-abstract-values
	(binary-ad-argument-and-result-abstract-values
	 bundle-value
	 (all-binary-ad 'bundle
			(lambda (v)
			 (and (not (perturbation-tagged-value? v))
			      (not (bundle? v))
			      (not (sensitivity-tagged-value? v))
			      (not (reverse-tagged-value? v))))
			perturbation-tagged-value? perturb unperturb
			bundle-aggregates-match?))
	(binary-ad-argument-and-result-abstract-values
	 plus-value
	 (all-binary-ad 'plus (lambda (v) #t) (lambda (v) #f) identity identity
			plus-aggregates-match?)))
       (all-abstract-values))
      (union-abstract-values
       (map-reduce
	union-abstract-values
	'()
	(lambda (widener-instance)
	 (list (widener-instance-v1 widener-instance)))
	(append (first widener-instances) (second widener-instances)))
       (map-reduce
	union-abstract-values
	'()
	(lambda (widener-instance)
	 (list (widener-instance-v2 widener-instance)))
	(append (first widener-instances) (second widener-instances))))))))))

(define (function-instance=? function-instance1 function-instance2)
 (and (abstract-value=? (function-instance-v1 function-instance1)
			(function-instance-v1 function-instance2))
      (abstract-value=? (function-instance-v2 function-instance1)
			(function-instance-v2 function-instance2))))

(define (union-function-instances function-instances1 function-instances2)
 (unionp function-instance=? function-instances1 function-instances2))

(define (all-function-instances)
 (map-reduce
  union-function-instances
  '()
  (lambda (e)
   (if (application? e)
       (map-reduce
	union-function-instances
	'()
	(lambda (b)
	 (let ((v1 (abstract-eval1
		    (application-callee e)
		    (restrict-environment
		     (environment-binding-values b) e application-callee)))
	       (v2 (abstract-eval1
		    (application-argument e)
		    (restrict-environment
		     (environment-binding-values b) e application-argument))))
	  (cond
	   ((union? v1)
	    (map-reduce
	     union-function-instances
	     '()
	     (lambda (u1)
	      (cond
	       ((closure? u1) (list (make-function-instance u1 v2)))
	       ((and (primitive-procedure? u1)
		     (eq? (primitive-procedure-name u1) 'if-procedure))
		(assert (and (vlad-pair? v2)
			     (vlad-pair? (vlad-cdr v2))
			     (closure? (vlad-car (vlad-cdr v2)))
			     (closure? (vlad-cdr (vlad-cdr v2)))))
		(let* ((v3 (vlad-car v2))
		       (v4 (vlad-cdr v2))
		       (v5 (vlad-car v4))
		       (v6 (vlad-cdr v4)))
		 (if (void?
		      (cond ((and (some vlad-false? (union-members v3))
				  (some (lambda (u) (not (vlad-false? u)))
					(union-members v3)))
			     ;; here I am: The result might violate the
			     ;;            syntactic constraints.
			     (abstract-value-union
			      (abstract-apply v5 (vlad-empty-list))
			      (abstract-apply v6 (vlad-empty-list))))
			    ((some vlad-false? (union-members v3))
			     (abstract-apply v6 (vlad-empty-list)))
			    ((some (lambda (u) (not (vlad-false? u)))
				   (union-members v3))
			     (abstract-apply v5 (vlad-empty-list)))
			    (else (internal-error))))
		     '()
		     (cond
		      ((and (some vlad-false? (union-members v3))
			    (some (lambda (u) (not (vlad-false? u)))
				  (union-members v3)))
		       ;; We make the assumption that v5 and v6 will not be
		       ;; abstract-value=?. If this assumption is false then
		       ;; there may be duplicates.
		       (list (make-function-instance v5 (vlad-empty-list))
			     (make-function-instance v6 (vlad-empty-list))))
		      ((some vlad-false? (union-members v3))
		       (list (make-function-instance v6 (vlad-empty-list))))
		      ((some (lambda (u) (not (vlad-false? u)))
			     (union-members v3))
		       (list (make-function-instance v5 (vlad-empty-list))))
		      (else (internal-error))))))
	       (else '())))
	     (get-union-values v1)))
	   ((closure? v1) (list (make-function-instance v1 v2)))
	   ((and (primitive-procedure? v1)
		 (eq? (primitive-procedure-name v1) 'if-procedure))
	    (assert (and (vlad-pair? v2)
			 (vlad-pair? (vlad-cdr v2))
			 (closure? (vlad-car (vlad-cdr v2)))
			 (closure? (vlad-cdr (vlad-cdr v2)))))
	    (let* ((v3 (vlad-car v2))
		   (v4 (vlad-cdr v2))
		   (v5 (vlad-car v4))
		   (v6 (vlad-cdr v4)))
	     (if (void? (cond ((and (some vlad-false? (union-members v3))
				    (some (lambda (u) (not (vlad-false? u)))
					  (union-members v3)))
			       ;; here I am: The result might violate the
			       ;;            syntactic constraints.
			       (abstract-value-union
				(abstract-apply v5 (vlad-empty-list))
				(abstract-apply v6 (vlad-empty-list))))
			      ((some vlad-false? (union-members v3))
			       (abstract-apply v6 (vlad-empty-list)))
			      ((some (lambda (u) (not (vlad-false? u)))
				     (union-members v3))
			       (abstract-apply v5 (vlad-empty-list)))
			      (else (internal-error))))
		 '()
		 (cond
		  ((and (some vlad-false? (union-members v3))
			(some (lambda (u) (not (vlad-false? u)))
			      (union-members v3)))
		   ;; We make the assumption that v5 and v6 will not be
		   ;; abstract-value=?. If this assumption is false then
		   ;; there may be duplicates.
		   (list (make-function-instance v5 (vlad-empty-list))
			 (make-function-instance v6 (vlad-empty-list))))
		  ((some vlad-false? (union-members v3))
		   (list (make-function-instance v6 (vlad-empty-list))))
		  ((some (lambda (u) (not (vlad-false? u))) (union-members v3))
		   (list (make-function-instance v5 (vlad-empty-list))))
		  (else (internal-error))))))
	   (else '()))))
	(expression-environment-bindings e))
       '()))
  *expressions*))

(define (widener-instance=? widener-instance1 widener-instance2)
 (and (abstract-value=? (widener-instance-v1 widener-instance1)
			(widener-instance-v1 widener-instance2))
      (abstract-value=? (widener-instance-v2 widener-instance1)
			(widener-instance-v2 widener-instance2))))

(define (union-widener-instances widener-instances1 widener-instances2)
 (unionp widener-instance=? widener-instances1 widener-instances2))

(define (all-subwidener-instances v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  35
  (let outer ((v1 v1) (v2 v2) (cs '()) (n '()) (k (lambda (n cs) n)))
   (cond
    ((some (lambda (c) (and (eq? (car c) v1) (eq? (cdr c) v2))) cs) (k n cs))
    ((abstract-value=? v1 v2) (k n cs))
    ;; Note that we have syntactic constraints that widen (union r1 r2) to R but
    ;; not things like (union (perturbation r1) (perturbation r2)) to
    ;; (perturbation R). Because of this, v1 might be a union even though v2
    ;; might not be.
    ((union? v1)
     (let inner ((us (get-union-values v1))
		 (cs (cons (cons v1 v2) cs))
		 (n (adjoinp
		     widener-instance=? (make-widener-instance v1 v2) n)))
      (if (null? us)
	  (k n cs)
	  (outer (first us) v2 cs n (lambda (n cs) (inner (rest us) cs n))))))
    ;; If v2 is an empty abstract value then v1 will be and the first case where
    ;; (abstract-value=? v1 v2) will be taken and this case will never be.
    ((union? v2)
     (outer v1
	    ;; The fact that such a u2 exists that is a member of v2 relies on
	    ;; our imprecise notion of abstract-value subset. There may be more
	    ;; than one. Any will do, it is only a matter of efficiency to
	    ;; choose between the alternatives. I don't even know how to
	    ;; define/determine which alternative would be most efficient.
	    (find-if (lambda (u2) (abstract-value-subset? v1 u2))
		     (get-union-values v2))
	    cs
	    (adjoinp widener-instance=? (make-widener-instance v1 v2) n)
	    k))
    ((scalar-value? v2)
     (k (adjoinp widener-instance=? (make-widener-instance v1 v2) n) cs))
    ;; This will only be done on conforming structures since the
    ;; analysis is almost union free.
    (else (let inner ((vs1 (aggregate-value-values v1))
		      (vs2 (aggregate-value-values v2))
		      (cs (cons (cons v1 v2) cs))
		      (n (adjoinp
			  widener-instance=? (make-widener-instance v1 v2) n)))
	   (if (null? vs1)
	       (k n cs)
	       (outer (first vs1)
		      (first vs2)
		      cs
		      n
		      (lambda (n cs) (inner (rest vs1) (rest vs2) cs n))))))))))

(define (all-unary-ad-widener-instances s descend? f)
 ;; here I am: The result of f might violate the syntactic constraints.
 (map-reduce
  union-widener-instances
  '()
  (lambda (v)
   (if (union? v)
       (map-reduce union-widener-instances
		   '()
		   ;; The call to f might issue "might" warnings and might
		   ;; return an empty abstract value.
		   (lambda (u) (all-subwidener-instances (f u) (f v)))
		   (get-union-values v))
       '()))
  (all-unary-ad s descend?)))

(define (all-binary-ad-widener-instances
	 s descend? f? f f-inverse g g-value aggregates-match?)
 ;; here I am: The results of f, f-inverse, g, and g-value might violate the
 ;;            syntactic constraints.
 (map-reduce
  union-widener-instances
  '()
  (lambda (v)
   (cond
    ((union? v)
     (map-reduce
      union-widener-instances
      '()
      ;; The calls to g-value might issue "might" warnings and might return
      ;; empty abstract values.
      (lambda (u) (all-subwidener-instances (g-value u) (g-value v)))
      (get-union-values v)))
    ((vlad-pair? v)
     (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
      (cond ((union? v1)
	     (map-reduce
	      union-widener-instances
	      '()
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (lambda (u1) (all-subwidener-instances (g u1 v2) (g v1 v2)))
	      (get-union-values v1)))
	    ((union? v2)
	     (map-reduce
	      union-widener-instances
	      '()
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (lambda (u2) (all-subwidener-instances (g v1 u2) (g v1 v2)))
	      (get-union-values v2)))
	    ;; The calls to f and f-inverse should never return an empty
	    ;; abstract value. The call to f-inverse might issue "might"
	    ;; warnings.
	    ((and (f? v2) (union? (f-inverse v2)))
	     (map-reduce
	      union-widener-instances
	      '()
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (lambda (u2) (all-subwidener-instances (g v1 (f u2)) (g v1 v2)))
	      (get-union-values (f-inverse v2))))
	    (else '()))))
    (else '())))
  (all-binary-ad s descend? f? f f-inverse aggregates-match?)))

(define (all-widener-instances)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (feedback-topological-sort
  widener-instance=?
  (lambda (widener-instance)
   (cross-product
    make-widener-instance
    (abstract-values-before (widener-instance-v1 widener-instance))
    (abstract-values-before (widener-instance-v2 widener-instance))))
  ;; here I am: Need better choice function.
  first
  (union-widener-instances
   (map-reduce
    union-widener-instances
    '()
    (lambda (e)
     (map-reduce
      union-widener-instances
      '()
      (lambda (b)
       (cond
	((constant-expression? e)
	 (all-subwidener-instances
	  (constant-expression-value e) (environment-binding-value b)))
	((lambda-expression? e)
	 (all-subwidener-instances
	  (new-nonrecursive-closure (environment-binding-values b) e)
	  (environment-binding-value b)))
	((application? e)
	 (let ((v1 (abstract-eval1
		    (application-callee e)
		    (restrict-environment
		     (environment-binding-values b) e application-callee)))
	       (v2 (abstract-eval1
		    (application-argument e)
		    (restrict-environment
		     (environment-binding-values b) e application-argument))))
	  (union-widener-instances
	   (all-subwidener-instances
	    (abstract-apply v1 v2)
	    (environment-binding-value b))
	   (cond
	    ((union? v1)
	     (map-reduce union-widener-instances
			 '()
			 (lambda (u1)
			  (all-subwidener-instances
			   (abstract-apply u1 v2) (abstract-apply v1 v2)))
			 (get-union-values v1)))
	    ((closure? v1) '())
	    ((and (primitive-procedure? v1)
		  (eq? (primitive-procedure-name v1) 'if-procedure))
	     (assert (and (vlad-pair? v2)
			  (vlad-pair? (vlad-cdr v2))
			  (closure? (vlad-car (vlad-cdr v2)))
			  (closure? (vlad-cdr (vlad-cdr v2)))))
	     (let* ((v3 (vlad-car v2))
		    (v4 (vlad-cdr v2))
		    (v5 (vlad-car v4))
		    (v6 (vlad-cdr v4))
		    (v7 (cond ((and (some vlad-false? (union-members v3))
				    (some (lambda (u) (not (vlad-false? u)))
					  (union-members v3)))
			       ;; here I am: The result might violate the
			       ;;            syntactic constraints.
			       (abstract-value-union
				(abstract-apply v5 (vlad-empty-list))
				(abstract-apply v6 (vlad-empty-list))))
			      ((some vlad-false? (union-members v3))
			       (abstract-apply v6 (vlad-empty-list)))
			      ((some (lambda (u) (not (vlad-false? u)))
				     (union-members v3))
			       (abstract-apply v5 (vlad-empty-list)))
			      (else (internal-error)))))
	      (if (and (not (void? v7))
		       (some vlad-false? (union-members v3))
		       (some (lambda (u) (not (vlad-false? u)))
			     (union-members v3)))
		  (union-widener-instances
		   (all-subwidener-instances
		    (abstract-apply v5 (vlad-empty-list)) v7)
		   (all-subwidener-instances
		    (abstract-apply v6 (vlad-empty-list)) v7))
		  '())))
	    (else '())))))
	((letrec-expression? e)
	 (union-widener-instances
	  (all-subwidener-instances
	   (abstract-eval1
	    (letrec-expression-body e)
	    (letrec-nested-environment (environment-binding-values b) e))
	   (environment-binding-value b))
	  (map-reduce
	   union-widener-instances
	   '()
	   (lambda (x)
	    (let ((v (new-recursive-closure
		      (letrec-restrict-environment
		       (environment-binding-values b) e)
		      (list->vector (letrec-expression-procedure-variables e))
		      (list->vector (letrec-expression-lambda-expressions e))
		      (positionp variable=?
				 x
				 (letrec-expression-procedure-variables e)))))
	     (all-subwidener-instances v (widen-abstract-value v))))
	   (letrec-expression-procedure-variables e))))
	((cons-expression? e)
	 (all-subwidener-instances
	  (new-tagged-pair
	   (cons-expression-tags e)
	   (abstract-eval1
	    (cons-expression-car e)
	    (restrict-environment
	     (environment-binding-values b) e cons-expression-car))
	   (abstract-eval1
	    (cons-expression-cdr e)
	    (restrict-environment
	     (environment-binding-values b) e cons-expression-cdr)))
	  (environment-binding-value b)))
	(else '())))
      (expression-environment-bindings e)))
    *expressions*)
   (reduce
    union-widener-instances
    (list
     (all-unary-ad-widener-instances 'zero (lambda (v) #t) zero)
     (all-unary-ad-widener-instances
      'perturb
      (lambda (v)
       (and (not (perturbation-tagged-value? v))
	    (not (bundle? v))
	    (not (sensitivity-tagged-value? v))
	    (not (reverse-tagged-value? v))))
      perturb)
     (all-unary-ad-widener-instances
      'unperturb
      (lambda (v)
       (and (perturbation-value? v) (not (perturbation-tagged-value? v))))
      unperturb)
     (all-unary-ad-widener-instances
      'primal (lambda (v) (and (forward-value? v) (not (bundle? v)))) primal)
     (all-unary-ad-widener-instances
      'tangent (lambda (v) (and (forward-value? v) (not (bundle? v)))) tangent)
     (all-binary-ad-widener-instances
      'bundle
      (lambda (v)
       (and (not (perturbation-tagged-value? v))
	    (not (bundle? v))
	    (not (sensitivity-tagged-value? v))
	    (not (reverse-tagged-value? v))))
      perturbation-tagged-value? perturb unperturb bundle bundle-value
      bundle-aggregates-match?)
     (all-unary-ad-widener-instances
      'sensitize
      (lambda (v)
       (and (not (perturbation-tagged-value? v))
	    (not (bundle? v))
	    (not (sensitivity-tagged-value? v))
	    (not (reverse-tagged-value? v))))
      sensitize)
     (all-unary-ad-widener-instances
      'unsensitize
      (lambda (v)
       (and (sensitivity-value? v) (not (sensitivity-tagged-value? v))))
      unsensitize)
     (all-binary-ad-widener-instances
      'plus (lambda (v) #t) (lambda (v) #f) identity identity plus plus-value
      plus-aggregates-match?)
     (all-unary-ad-widener-instances
      '*j
      (lambda (v)
       (and (not (perturbation-tagged-value? v))
	    (not (bundle? v))
	    (not (sensitivity-tagged-value? v))
	    (not (reverse-tagged-value? v))))
      *j)
     (all-unary-ad-widener-instances
      '*j-inverse
      (lambda (v) (and (reverse-value? v) (not (reverse-tagged-value? v))))
      *j-inverse))
    '()))))

(define (all-primitives s)
 (map-reduce
  union-abstract-values
  '()
  (lambda (e)
   (if (application? e)
       (remove-duplicatesp
	abstract-value=?
	(removeq
	 #f
	 (map (lambda (b)
	       (let ((v1 (abstract-eval1 (application-callee e)
					 (restrict-environment
					  (environment-binding-values b)
					  e
					  application-callee)))
		     (v2 (abstract-eval1 (application-argument e)
					 (restrict-environment
					  (environment-binding-values b)
					  e
					  application-argument))))
		(if (and (not (union? v1))
			 (primitive-procedure? v1)
			 (eq? (primitive-procedure-name v1) s)
			 (not (void? (abstract-apply v1 v2))))
		    v2
		    #f)))
	      (expression-environment-bindings e))))
       '()))
  *expressions*))

(define (if-instance=? if-instance1 if-instance2)
 (abstract-value=? (if-instance-v if-instance1) (if-instance-v if-instance2)))

(define (if-and-function-instance=? instance1 instance2)
 (or (and (if-instance? instance1)
	  (if-instance? instance2)
	  (if-instance=? instance1 instance2))
     (and (function-instance? instance1)
	  (function-instance? instance2)
	  (function-instance=? instance1 instance2))))

(define (union-if-and-function-instances instances1 instances2)
 (unionp if-and-function-instance=? instances1 instances2))

(define (all-instances1-instances2 function-instances)
 ;; This topological sort is needed so that all INLINE definitions come before
 ;; their uses as required by gcc.
 (feedback-topological-sort
  if-and-function-instance=?
  (lambda (instance)
   (cond
    ((if-instance? instance)
     (list
      (make-function-instance (vlad-car (vlad-cdr (if-instance-v instance)))
			      (vlad-empty-list))
      (make-function-instance (vlad-cdr (vlad-cdr (if-instance-v instance)))
			      (vlad-empty-list))))
    ((function-instance? instance)
     (map-reduce
      union-if-and-function-instances
      '()
      (lambda (vs)
       (let loop ((e (closure-body (function-instance-v1 instance)))
		  (vs (map widen-abstract-value vs)))
	(assert (= (length vs) (length (free-variables e))))
	(cond
	 ((application? e)
	  (let ((v1 (abstract-eval1
		     (application-callee e)
		     (restrict-environment vs e application-callee)))
		(v2 (abstract-eval1
		     (application-argument e)
		     (restrict-environment vs e application-argument))))
	   (union-if-and-function-instances
	    (map-reduce
	     union-if-and-function-instances
	     '()
	     (lambda (u1)
	      (cond ((and (primitive-procedure? u1)
			  (eq? (primitive-procedure-name u1) 'if-procedure))
		     (assert (and (vlad-pair? v2)
				  (vlad-pair? (vlad-cdr v2))
				  (closure? (vlad-car (vlad-cdr v2)))
				  (closure? (vlad-cdr (vlad-cdr v2)))))
		     (list (make-if-instance v2)))
		    ((closure? u1) (list (make-function-instance u1 v2)))
		    (else '())))
	     (union-members v1))
	    (union-if-and-function-instances
	     (loop (application-callee e)
		   (restrict-environment vs e application-callee))
	     (loop (application-argument e)
		   (restrict-environment vs e application-argument))))))
	 ((letrec-expression? e)
	  (loop (letrec-expression-body e)
		(map widen-abstract-value (letrec-nested-environment vs e))))
	 ((cons-expression? e)
	  (union-if-and-function-instances
	   (loop (cons-expression-car e)
		 (restrict-environment vs e cons-expression-car))
	   (loop (cons-expression-cdr e)
		 (restrict-environment vs e cons-expression-cdr))))
	 (else '()))))
      (construct-abstract-environments (function-instance-v1 instance)
				       (function-instance-v2 instance))))
    (else (internal-error))))
  (lambda (instances)
   (let ((instance
	  (or (find-if
	       (lambda (instance)
		(and (function-instance? instance)
		     (recursive-closure? (function-instance-v1 instance))))
	       instances)
	      (find-if
	       (lambda (instance)
		(and (function-instance? instance)
		     (backpropagator? (function-instance-v1 instance))))
	       instances))))
    (assert instance)
    instance))
  (append (map (lambda (v)
		(assert (and (vlad-pair? v)
			     (vlad-pair? (vlad-cdr v))
			     (closure? (vlad-car (vlad-cdr v)))
			     (closure? (vlad-cdr (vlad-cdr v)))))
		(make-if-instance v))
	       (all-primitives 'if-procedure))
	  function-instances)))

(define (boxed? v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-boxed? v))
       ((recursive-closure? v) (recursive-closure-boxed? v))
       ((perturbation-tagged-value? v) (perturbation-tagged-value-boxed? v))
       ((bundle? v) (bundle-boxed? v))
       ((sensitivity-tagged-value? v) (sensitivity-tagged-value-boxed? v))
       ((reverse-tagged-value? v) (reverse-tagged-value-boxed? v))
       ((tagged-pair? v) (tagged-pair-boxed? v))
       ((union? v) (union-boxed? v))
       (else #f)))

(define (c:index v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-c:index v))
       ((recursive-closure? v) (recursive-closure-c:index v))
       ((perturbation-tagged-value? v) (perturbation-tagged-value-c:index v))
       ((bundle? v) (bundle-c:index v))
       ((sensitivity-tagged-value? v) (sensitivity-tagged-value-c:index v))
       ((reverse-tagged-value? v) (reverse-tagged-value-c:index v))
       ((tagged-pair? v) (tagged-pair-c:index v))
       ((union? v) (union-c:index v))
       (else (cdr (assp abstract-value=? v *c:indices*)))))

;;; Primitive C syntax generators

(define (c:sizeof code) (list "sizeof" "(" code ")"))

(define (c:pointer-cast code1 code2) (list "(" code1 " " "*" ")" code2))

(define (c:binary code1 code2 code3) (list code1 code2 code3))

(define (c:conditional code1 code2 code3) (list code1 "?" code2 ":" code3))

(define (c:assignment code1 code2) (list code1 "=" code2 ";"))

(define (c:return code) (list "return" " " code ";"))

(define (c:variable-name x) (list "x" (variable-index x)))

(define (c:specifier v)
 (assert (not (void? v)))
 (if (and (not (union? v)) (abstract-real? v))
     "double"
     (list "struct" " " (list "s" (c:index v)))))

(define (c:pointer-declarator code) (list "*" code))

(define (generate-slot-names v)
 ;; generate -~-> c:
 (cond
  ((union? v) (map (lambda (v) (list "s" (c:index v))) (get-union-values v)))
  ((nonrecursive-closure? v)
   (map c:variable-name (nonrecursive-closure-variables v)))
  ((recursive-closure? v)
   (map c:variable-name (recursive-closure-variables v)))
  ((perturbation-tagged-value? v) '("p"))
  ((bundle? v) '("p" "t"))
  ((sensitivity-tagged-value? v) '("p"))
  ((reverse-tagged-value? v) '("p"))
  ((tagged-pair? v) '("a" "d"))
  (else (internal-error))))

(define (c:parameter code1 code2) (list code1 " " code2))

(define (c:specifier-parameter v code)
 (if (void? v)
     '()
     (c:parameter (c:specifier v)
		  (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:declaration code1 code2) (list code1 " " code2 ";"))

(define (c:specifier-declaration v code)
 (if (void? v)
     '()
     (c:declaration (c:specifier v)
		    (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:init-declaration code1 code2 code3)
 (list code1 " " code2 "=" code3 ";"))

(define (c:specifier-init-declaration v code1 code2)
 (if (void? v)
     '()
     (c:init-declaration (c:specifier v)
			 (if (boxed? v) (c:pointer-declarator code1) code1)
			 code2)))

(define (c:let v code1 code2 code3)
 (list "(" "{" (c:specifier-init-declaration v code1 code2) code3 ";" "}" ")"))

(define (generate-struct-and-union-declarations vs1-vs2)
 ;; generate -~-> c:
 ;; abstraction
 (list
  ;; This generates forward declarations for the struct and union tags.
  ;; abstraction
  (map (lambda (v)
	(cond ((void? v) '())
	      ((union? v)
	       ;; abstraction
	       (list
		(if (every void? (get-union-values v))
		    '()
		    ;; abstraction
		    (list *union*
			  " "
			  ;; abstraction
			  (list "u" (c:index v))
			  ";"
			  #\newline))
		;; abstraction
		(list (c:specifier v) ";" #\newline)))
	      ((abstract-real? v) '())
	      (else
	       ;; abstraction
	       (list
		;; abstraction
		(list (c:specifier v) ";" #\newline)))))
       (second vs1-vs2))
  ;; abstraction
  (map (lambda (v)
	(cond ((void? v) '())
	      ((union? v)
	       ;; By fortuitous confluence, this will eliminate the union
	       ;; declaration for the empty abstract value and generate a
	       ;; struct declaration with just a type tag (which will never be
	       ;; used).
	       ;; abstraction
	       (list
		(if (every void? (get-union-values v))
		    '()
		    ;; abstraction
		    (list *union*
			  " "
			  ;; abstraction
			  (list "u" (c:index v))
			  "{"
			  (map c:specifier-declaration
			       (get-union-values v)
			       (generate-slot-names v))
			  "}"
			  ";"
			  #\newline))
		;; abstraction
		(list (c:specifier v)
		      "{"
		      ;; The type tag is always unboxed.
		      (c:declaration "int" "t")
		      (if (every void? (get-union-values v))
			  '()
			  ;; The union is always unboxed.
			  (c:declaration
			   ;; abstraction
			   (list *union*
				 " "
				 ;; abstraction
				 (list "u" (c:index v)))
			   "u"))
		      "}"
		      ";"
		      #\newline)))
	      ((abstract-real? v) '())
	      (else
	       ;; abstraction
	       (list
		;; abstraction
		(list (c:specifier v)
		      "{"
		      (map c:specifier-declaration
			   (aggregate-value-values v)
			   (generate-slot-names v))
		      "}"
		      ";"
		      #\newline)))))
       (append (first vs1-vs2) (second vs1-vs2)))))

(define (c:builtin-name code v) (list code (c:index v)))

(define (c:constructor-name v) (list "m" (c:index v)))

(define (c:unioner-name u v) (list "m" (c:index v) "_" (c:index u)))

(define (c:function-name v1 v2 function-instances)
 (assert (memp function-instance=?
	       (make-function-instance v1 v2)
	       function-instances))
 (list "f" (positionp function-instance=?
		      (make-function-instance v1 v2)
		      function-instances)))

(define (c:widener-name v1 v2 widener-instances)
 (assert (memp widener-instance=?
	       (make-widener-instance v1 v2)
	       (append (first widener-instances) (second widener-instances))))
 (list
  "w"
  (positionp widener-instance=?
	     (make-widener-instance v1 v2)
	     (append (first widener-instances) (second widener-instances)))))

(define (c:function-declarator* code codes)
 (list
  code
  "("
  (let ((codes (removeq '() codes)))
   (cond
    ((null? codes) "void")
    ((null? (rest codes)) (first codes))
    (else (reduce (lambda (code1 code2) (list code1 "," code2)) codes '()))))
  ")"))

(define (c:function-declaration p1? p2? p3? code1 code2)
 (list (if p1? (list "static" " ") '())
       (if p2? (list "INLINE" " ") '())
       (if p3? (list "NORETURN" " ") '())
       code1
       " "
       code2
       ";"
       #\newline))

(define (c:specifier-function-declaration p1? p2? p3? v code)
 (if (void? v)
     '()
     (c:function-declaration
      p1? p2? p3? (c:specifier v)
      (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:function-definition p1? p2? p3? code1 code2 code3)
 (list (if p1? (list "static" " ") '())
       (if p2? (list "INLINE" " ") '())
       (if p3? (list "NORETURN" " ") '())
       code1
       " "
       code2
       "{"
       code3
       "}"
       #\newline))

(define (c:specifier-function-definition p1? p2? p3? v code1 code2)
 (if (void? v)
     '()
     (c:function-definition p1? p2? p3? (c:specifier v)
			    (if (boxed? v) (c:pointer-declarator code1) code1)
			    code2)))

(define (c:call* code codes)
 (list
  code
  "("
  (let ((codes (removeq '() codes)))
   (cond
    ((null? codes) '())
    ((null? (rest codes)) (first codes))
    (else (reduce (lambda (code1 code2) (list code1 "," code2)) codes '()))))
  ")"))

(define (c:panic v code)
 (c:call (c:builtin-name "panic" v) (list "\"" code "\"")))

;;; Derived C syntax generators

(define (c:binary-boolean code)
 (lambda (code1 code2)
  (c:conditional (c:binary code1 code code2)
		 (c:call (c:unioner-name (vlad-true) (abstract-boolean)))
		 (c:call (c:unioner-name (vlad-false) (abstract-boolean))))))

(define (c:unary-boolean code)
 (lambda (code1)
  (c:conditional (c:binary code1 code "0.0")
		 (c:call (c:unioner-name (vlad-true) (abstract-boolean)))
		 (c:call (c:unioner-name (vlad-false) (abstract-boolean))))))

(define (c:function-declarator code . codes)
 (c:function-declarator* code codes))

(define (c:call code . codes) (c:call* code codes))

(define (c:slot v code1 code2)
 (if (void? v) 'error (c:binary code1 (if (boxed? v) "->" ".") code2)))

(define (c:tag v code) (c:slot v code "t"))

(define (c:union v code1 code2)
 ;; The union is always unboxed.
 (c:binary (c:slot v code1 "u") "." code2))

(define (c:dispatch v code codes)
 (assert (and (= (length (get-union-values v)) (length codes))
	      (>= (length (get-union-values v)) 2)))
 ;; This uses per-union tags here instead of per-program tags.
 ;; It would be better to use a switch but while there are conditional
 ;; expressions in C, there are no switch expressions. We could use the GNU C
 ;; statement expression extension. In the case of conditional expressions, we
 ;; could optimize the order (by profiling or static analysis). In the case of
 ;; a switch, could optimize the choice of which case becomes the default.
 (let loop ((codes codes) (i 0))
  (if (null? (rest codes))
      (first codes)
      ;; The type tag is always unboxed.
      (c:conditional (c:binary (c:tag v code) "==" i)
		     (first codes)
		     (loop (rest codes) (+ i 1))))))

(define (c:widen v1 v2 code widener-instances)
 (if (abstract-value=? v1 v2)
     code
     (c:call (c:widener-name v1 v2 widener-instances)
	     (if (void? v1) '() code))))

;;; Declaration generators

(define (generate-constructor-declarations vs1-vs2)
 ;; abstraction
 (map (lambda (v)
       (cond
	((void? v) '())
	((union? v)
	 ;; By fortuitous confluence, this will not generate constructor
	 ;; declarations for the empty abstract value.
	 ;; abstraction
	 (map (lambda (u)
	       (c:specifier-function-declaration
		#t #t #f v
		(c:function-declarator (c:unioner-name u v)
				       (c:specifier-parameter u "x"))))
	      (get-union-values v)))
	((abstract-real? v) '())
	(else (c:specifier-function-declaration
	       #t #t #f v
	       (c:function-declarator* (c:constructor-name v)
				       (map c:specifier-parameter
					    (aggregate-value-values v)
					    (generate-slot-names v)))))))
      (append (first vs1-vs2) (second vs1-vs2))))

(define (generate-widener-declaration widener-instance widener-instances p?)
 (let ((v1 (widener-instance-v1 widener-instance))
       (v2 (widener-instance-v2 widener-instance)))
  (c:specifier-function-declaration
   #t p? #f v2
   (c:function-declarator (c:widener-name v1 v2 widener-instances)
			  (c:specifier-parameter v1 "x")))))

(define (generate-widener-declarations widener-instances)
 ;; abstraction
 (append
  ;; abstraction
  (map (lambda (widener-instance)
	(generate-widener-declaration widener-instance widener-instances #t))
       (first widener-instances))
  ;; abstraction
  (map (lambda (widener-instance)
	(generate-widener-declaration widener-instance widener-instances #f))
       (second widener-instances))))

(define (generate-panic-declarations vs1-vs2)
 ;; abstraction
 (map (lambda (v)
       (c:specifier-function-declaration
	#t #t #t v
	(c:function-declarator
	 (c:builtin-name "panic" v)
	 (c:parameter "char" (c:pointer-declarator "x")))))
      (append (first vs1-vs2) (second vs1-vs2))))

(define (generate-real*real-primitive-declarations s v0 code)
 ;; abstraction
 (map (lambda (v)
       (c:specifier-function-declaration
	#t #t #f v0
	(c:function-declarator (c:builtin-name code v)
			       (c:specifier-parameter v "x"))))
      (all-primitives s)))

(define (generate-real-primitive-declarations s v0 code)
 ;; abstraction
 (map (lambda (v)
       (c:specifier-function-declaration
	#t #t #f v0
	(c:function-declarator (c:builtin-name code v)
			       (c:specifier-parameter v "x"))))
      (all-primitives s)))

(define (generate-unary-ad-delaration v f code p?)
 ;; here I am: The result of f might violate the syntactic constraints.
 (c:specifier-function-declaration
  ;; The call to f might issue "might" warnings and might return an empty
  ;; abstract value.
  #t p? #f (f v)
  (c:function-declarator (c:builtin-name code v)
			 (c:specifier-parameter v "x"))))

(define (generate-unary-ad-declarations s descend? f code)
 (let ((vs1a-vs2a (all-sorted-unary-ad s descend?)))
  ;; abstraction
  (append
   ;; abstraction
   (map (lambda (v) (generate-unary-ad-delaration v f code #t))
	(first vs1a-vs2a))
   ;; abstraction
   (map (lambda (v) (generate-unary-ad-delaration v f code #f))
	(second vs1a-vs2a)))))

(define (generate-binary-ad-declaration v g-value code p?)
 (c:specifier-function-declaration
  ;; The call to g-value might issue "might" warnings and might return
  ;; an empty abstract value.
  #t p? #f (g-value v)
  (c:function-declarator (c:builtin-name code v)
			 (c:specifier-parameter v "x"))))

(define (generate-binary-ad-declarations
	 s descend? f? f f-inverse g-value aggregates-match? before code)
 ;; here I am: The results of f, f-inverse, and g-value might violate the
 ;;            syntactic constraints.
 (let ((vs1a-vs2a (all-sorted-binary-ad
		   s descend? f? f f-inverse aggregates-match? before)))
  ;; abstraction
  (append
   ;; abstraction
   (map (lambda (v) (generate-binary-ad-declaration v g-value code #t))
	(first vs1a-vs2a))
   ;; abstraction
   (map (lambda (v) (generate-binary-ad-declaration v g-value code #f))
	(second vs1a-vs2a)))))

(define (generate-if-and-function-declaration instance function-instances p?)
 (cond
  ((if-instance? instance)
   (let* ((v (if-instance-v instance))
	  (v1 (vlad-car v))
	  (v2 (vlad-cdr v))
	  (v3 (vlad-car v2))
	  (v4 (vlad-cdr v2)))
    (c:specifier-function-declaration
     #t #t #f
     (cond ((and (some vlad-false? (union-members v1))
		 (some (lambda (u) (not (vlad-false? u))) (union-members v1)))
	    ;; here I am: The result might violate the syntactic constraints.
	    (abstract-value-union (abstract-apply v3 (vlad-empty-list))
				  (abstract-apply v4 (vlad-empty-list))))
	   ((some vlad-false? (union-members v1))
	    (abstract-apply v4 (vlad-empty-list)))
	   ((some (lambda (u) (not (vlad-false? u))) (union-members v1))
	    (abstract-apply v3 (vlad-empty-list)))
	   (else (internal-error)))
     (c:function-declarator (c:builtin-name "if_procedure" v)
			    (c:specifier-parameter v "x")))))
  ((function-instance? instance)
   (let ((v1 (function-instance-v1 instance))
	 (v2 (function-instance-v2 instance)))
    (c:specifier-function-declaration
     #t p? #f
     (abstract-apply v1 v2)
     (c:function-declarator (c:function-name v1 v2 function-instances)
			    (c:specifier-parameter v1 "c")
			    (c:specifier-parameter v2 "x")))))
  (else (internal-error))))

(define (generate-if-and-function-declarations
	 function-instances instances1-instances2)
 ;; abstraction
 (append
  ;; abstraction
  (map (lambda (instance)
	(generate-if-and-function-declaration instance function-instances #t))
       (first instances1-instances2))
  ;; abstraction
  (map (lambda (instance)
	(generate-if-and-function-declaration instance function-instances #f))
       (second instances1-instances2))))

;;; Expression generators

(define (generate-destructure p e v code)
 ;; here I am: Need to handle unions for everything except variable access
 ;;            expressions and to convert run-time-error to c:panic.
 (cond
  ((constant-expression? p)
   ;; needs work: To generate run-time equivalence check when the constant
   ;;             expression parameter and/or argument contain abstract
   ;;             booleans or abstract reals. When we do so, we need to call
   ;;             c:widen appropriately. These would correspond to the calls A
   ;;             to widen-abstract-value in abstract-destructure.
   (unless (abstract-value-nondisjoint?
	    (concrete-value->abstract-value (constant-expression-value p))
	    v)
    (run-time-error "Argument is not an equivalent value"
		    (constant-expression-value p)
		    v))
   '())
  ((variable-access-expression? p)
   ;; We get "warning: unused variable" messages from gcc. This is an
   ;; unsuccessful attempt to eliminate such messages. It is difficult to
   ;; soundly eliminate all unneeded destructuring bindings. This is sound but
   ;; eliminates only some. One can't simply check if the variable is
   ;; referenced in the VLAD source. Because suppose you have code like
   ;; (F (G X)). Even though X is not void, (G X) might be, and then code is
   ;; not generated for (G X). For example (REST '(3)) or (NULL? '(3)).
   (if (memp variable=?
	     (variable-access-expression-variable p)
	     (free-variables e))
       (c:specifier-init-declaration
	v (c:variable-name (variable-access-expression-variable p)) code)
       '()))
  ((lambda-expression? p)
   (unless (and (nonrecursive-closure? v)
		(dereferenced-expression-eqv?
		 p (nonrecursive-closure-lambda-expression v)))
    (run-time-error
     (format #f "Argument is not a matching nonrecursive closure for ~s"
	     (externalize-expression p))
     v))
   ;; abstraction
   (map (lambda (x1 x2 v1)
	 (generate-destructure (new-variable-access-expression x1)
			       e
			       v1
			       (c:slot v code (c:variable-name x2))))
	(parameter-variables p)
	(nonrecursive-closure-variables v)
	(get-nonrecursive-closure-values v)))
  ((letrec-expression? p)
   (assert (and (variable-access-expression? (letrec-expression-body p))
		(memp variable=?
		      (variable-access-expression-variable
		       (letrec-expression-body p))
		      (letrec-expression-procedure-variables p))))
   (unless (and (recursive-closure? v)
		(= (recursive-closure-index v)
		   (positionp variable=?
			      (variable-access-expression-variable
			       (letrec-expression-body p))
			      (letrec-expression-procedure-variables p)))
		(= (vector-length
		    (recursive-closure-procedure-variables v))
		   (length (letrec-expression-procedure-variables p)))
		(= (vector-length
		    (recursive-closure-lambda-expressions v))
		   (length (letrec-expression-lambda-expressions p)))
		(every dereferenced-expression-eqv?
		       (vector->list (recursive-closure-lambda-expressions v))
		       (letrec-expression-lambda-expressions p)))
    (run-time-error
     (format #f "Argument is not a matching recursive closure for ~s"
	     (externalize-expression p))
     v))
   ;; abstraction
   (map (lambda (x1 x2 v1)
	 (generate-destructure (new-variable-access-expression x1)
			       e
			       v1
			       (c:slot v code (c:variable-name x2))))
	(parameter-variables p)
	(recursive-closure-variables v)
	(get-recursive-closure-values v)))
  ((cons-expression? p)
   (unless (and (tagged-pair? v)
		(equal-tags? (cons-expression-tags p) (tagged-pair-tags v)))
    (run-time-error
     (format #f "Argument is not a matching tagged pair with tags ~s"
	     (cons-expression-tags p))
     v))
   ;; abstraction
   (append (generate-destructure (cons-expression-car p)
				 e
				 (get-tagged-pair-car v)
				 (c:slot v code "a"))
	   (generate-destructure (cons-expression-cdr p)
				 e
				 (get-tagged-pair-cdr v)
				 (c:slot v code "d"))))
  (else (internal-error))))

(define (generate-reference v x xs xs2)
 (cond ((memp variable=? x xs2) "c")
       ((memp variable=? x xs) (c:slot v "c" (c:variable-name x)))
       (else (c:variable-name x))))

(define (generate-expression
	 e vs v0 xs xs2 bs function-instances widener-instances)
 ;; xs is the list of free variables of the environent in which e is evaluated.
 ;; xs2 is the list of procedure variables of the environent in which e is
 ;;     evaluated.
 (cond
  ((constant-expression? e)
   (assert (void? (constant-expression-value e)))
   ;; This c:widen is necessary for the case where the constant expression
   ;; value is an inexact real and *imprecise-inexacts?* is true. It also is
   ;; necessary for the case where the constant expression value is widened
   ;; because it violates the syntactic constraints (presumably tagged pair
   ;; depth limit). This corresponds to call E to widen-abstract-value in
   ;; abstract-eval-prime!.
   (c:widen
    (constant-expression-value e) (abstract-eval1 e vs) '() widener-instances))
  ((variable-access-expression? e)
   ;; There does not need to be a call to c:widen to correspond to call F to
   ;; widen-abstract-value in abstract-eval-prime!.
   (generate-reference v0 (variable-access-expression-variable e) xs xs2))
  ((lambda-expression? e)
   ;; This c:widen is necessary for the case where the closure created violates
   ;; the syntactic constraints (presumably closure depth limit or
   ;; backpropagator depth limit). This corresponds to call G to
   ;; widen-abstract-value in abstract-eval-prime!.
   (c:widen
    (new-nonrecursive-closure vs e)
    (abstract-eval1 e vs)
    (c:call* (c:constructor-name (new-nonrecursive-closure vs e))
	     (map (lambda (x1 v1)
		   (if (void? v1) '() (generate-reference v0 x1 xs xs2)))
		  (free-variables e)
		  vs))
    widener-instances))
  ((application? e)
   ;; We don't check the "Argument has wrong type for target" condition.
   (let ((v1 (abstract-eval1 (application-callee e)
			     (restrict-environment vs e application-callee)))
	 (v2 (abstract-eval1
	      (application-argument e)
	      (restrict-environment vs e application-argument))))
    ;; This corresponds to call B to widen-abstract-value in abstract-eval!.
    (c:widen
     (abstract-apply v1 v2)
     (abstract-eval1 e vs)
     (cond
      ((union? v1)
       (c:let
	v1
	"y"
	(generate-expression (application-callee e)
			     (restrict-environment vs e application-callee)
			     v0
			     xs
			     xs2
			     bs
			     function-instances
			     widener-instances)
	(c:dispatch
	 v1
	 "y"
	 (map (lambda (code1 u1)
	       (c:widen
		(abstract-apply u1 v2)
		(abstract-apply v1 v2)
		(cond
		 ((primitive-procedure? u1)
		  (c:call ((primitive-procedure-generator u1) v2)
			  (if (void? v2)
			      '()
			      (generate-expression
			       (application-argument e)
			       (restrict-environment vs e application-argument)
			       v0
			       xs
			       xs2
			       bs
			       function-instances
			       widener-instances))))
		 ((closure? u1)
		  (c:call (c:function-name u1 v2 function-instances)
			  ;; here I am: widen?
			  (if (void? u1) '() (c:union v1 "y" code1))
			  ;; here I am: widen?
			  (if (void? v2)
			      '()
			      (generate-expression
			       (application-argument e)
			       (restrict-environment vs e application-argument)
			       v0
			       xs
			       xs2
			       bs
			       function-instances
			       widener-instances))))
		 (else (c:panic
			(abstract-apply u1 v2) "Target is not a procedure")))
		widener-instances))
	      (generate-slot-names v1)
	      (get-union-values v1)))))
      ((primitive-procedure? v1)
       (c:call ((primitive-procedure-generator v1) v2)
	       (if (void? v2)
		   '()
		   (generate-expression
		    (application-argument e)
		    (restrict-environment vs e application-argument)
		    v0
		    xs
		    xs2
		    bs
		    function-instances
		    widener-instances))))
      ((closure? v1)
       (c:call (c:function-name v1 v2 function-instances)
	       ;; here I am: widen?
	       (if (void? v1)
		   '()
		   (generate-expression
		    (application-callee e)
		    (restrict-environment vs e application-callee)
		    v0
		    xs
		    xs2
		    bs
		    function-instances
		    widener-instances))
	       ;; here I am: widen?
	       (if (void? v2)
		   '()
		   (generate-expression
		    (application-argument e)
		    (restrict-environment vs e application-argument)
		    v0
		    xs
		    xs2
		    bs
		    function-instances
		    widener-instances))))
      (else (c:panic (abstract-apply v1 v2) "Target is not a procedure")))
     widener-instances)))
  ((letrec-expression? e)
   ;; This corresponds to call C to widen-abstract-value in abstract-eval!.
   (c:widen (abstract-eval1 (letrec-expression-body e)
			    (letrec-nested-environment vs e))
	    (abstract-eval1 e vs)
	    (generate-expression
	     (letrec-expression-body e)
	     (map widen-abstract-value (letrec-nested-environment vs e))
	     v0
	     xs
	     xs2
	     bs
	     function-instances
	     widener-instances)
	    widener-instances))
  ((cons-expression? e)
   (let ((v1 (abstract-eval1 (cons-expression-car e)
			     (restrict-environment vs e cons-expression-car)))
	 (v2 (abstract-eval1 (cons-expression-cdr e)
			     (restrict-environment vs e cons-expression-cdr))))
    ;; This c:widen is necessary for the case where the tagged pair created
    ;; violates the syntactic constraints (presumably tagged pair depth limit)
    ;; or where the flow analysis widened due to imprecision. This corresponds
    ;; to calls D to widen-abstract-value in abstract-eval!.
    (c:widen
     (new-tagged-pair (cons-expression-tags e) v1 v2)
     (abstract-eval1 e vs)
     (c:call
      (c:constructor-name (new-tagged-pair (cons-expression-tags e) v1 v2))
      (if (void? v1)
	  '()
	  (generate-expression (cons-expression-car e)
			       (restrict-environment vs e cons-expression-car)
			       v0
			       xs
			       xs2
			       bs
			       function-instances
			       widener-instances))
      (if (void? v2)
	  '()
	  (generate-expression (cons-expression-cdr e)
			       (restrict-environment vs e cons-expression-cdr)
			       v0
			       xs
			       xs2
			       bs
			       function-instances
			       widener-instances)))
     widener-instances)))
  (else (internal-error))))

(define (generate-letrec-bindings e vs xs xs2 widener-instances)
 (cond
  ((constant-expression? e) '())
  ((variable-access-expression? e) '())
  ((lambda-expression? e) '())
  ((application? e)
   ;; abstraction
   (list
    (generate-letrec-bindings (application-callee e)
			      (restrict-environment vs e application-callee)
			      xs
			      xs2
			      widener-instances)
    (generate-letrec-bindings (application-argument e)
			      (restrict-environment vs e application-argument)
			      xs
			      xs2
			      widener-instances)))
  ((letrec-expression? e)
   ;; abstraction
   (list
    ;; abstraction
    (map (lambda (x)
	  (let* ((v (new-recursive-closure
		     (letrec-restrict-environment vs e)
		     (list->vector (letrec-expression-procedure-variables e))
		     (list->vector (letrec-expression-lambda-expressions e))
		     (positionp
		      variable=? x (letrec-expression-procedure-variables e))))
		 (v0 (widen-abstract-value v)))
	   (c:specifier-init-declaration
	    v0
	    (c:variable-name x)
	    ;; This c:widen is necessary for the case where the closure created
	    ;; violates the syntactic constraints (presumably closure depth
	    ;; limit or backpropagator depth limit).
	    (c:widen
	     v
	     v0
	     (c:call*
	      (c:constructor-name v)
	      (map (lambda (x1 v1)
		    (if (void? v1) '() (generate-reference v x1 xs xs2)))
		   (letrec-expression-variables e)
		   (letrec-restrict-environment vs e)))
	     widener-instances))))
	 (letrec-expression-procedure-variables e))
    (generate-letrec-bindings
     (letrec-expression-body e)
     (map widen-abstract-value (letrec-nested-environment vs e))
     xs
     xs2
     widener-instances)))
  ((cons-expression? e)
   ;; abstraction
   (list
    (generate-letrec-bindings (cons-expression-car e)
			      (restrict-environment vs e cons-expression-car)
			      xs
			      xs2
			      widener-instances)
    (generate-letrec-bindings (cons-expression-cdr e)
			      (restrict-environment vs e cons-expression-cdr)
			      xs
			      xs2
			      widener-instances)))
  (else (internal-error))))

;;; Definition generators

(define (generate-constructor-definitions vs1-vs2)
 ;; abstraction
 (map
  (lambda (v)
   (cond
    ((void? v) '())
    ((union? v)
     ;; By fortuitous confluence, this will not generate constructor
     ;; definitions for the empty abstract value.
     ;; abstraction
     (map (lambda (u)
	   (c:specifier-function-definition
	    #t #t #f v
	    (c:function-declarator (c:unioner-name u v)
				   (c:specifier-parameter u "x"))
	    ;; abstraction
	    (list (if (boxed? v)
		      ;; We don't check for out of memory.
		      (c:specifier-init-declaration
		       v
		       "r"
		       (c:pointer-cast
			(c:specifier v)
			(c:call "GC_malloc" (c:sizeof (c:specifier v)))))
		      (c:specifier-declaration v "r"))
		  (c:assignment
		   ;; The type tag is always unboxed.
		   (c:tag v "r")
		   ;; This uses per-union tags here instead of per-program
		   ;; tags.
		   (positionp abstract-value=? u (get-union-values v)))
		  (if (void? u)
		      '()
		      (c:assignment (c:union v
					     "r"
					     ;; abstraction
					     (list "s" (c:index u)))
				    "x"))
		  (c:return "r"))))
	  (get-union-values v)))
    ((abstract-real? v) '())
    (else
     (c:specifier-function-definition
      #t #t #f v
      (c:function-declarator* (c:constructor-name v)
			      (map c:specifier-parameter
				   (aggregate-value-values v)
				   (generate-slot-names v)))
      ;; abstraction
      (list (if (boxed? v)
		;; We don't check for out of memory.
		(c:specifier-init-declaration
		 v
		 "r"
		 (c:pointer-cast
		  (c:specifier v)
		  (c:call "GC_malloc" (c:sizeof (c:specifier v)))))
		(c:specifier-declaration v "r"))
	    (map
	     (lambda (code1 v1)
	      (if (void? v1) '() (c:assignment (c:slot v "r" code1) code1)))
	     (generate-slot-names v)
	     (aggregate-value-values v))
	    (c:return "r"))))))
  (append (first vs1-vs2) (second vs1-vs2))))

(define (generate-widener-definition widener-instance widener-instances p?)
 (let ((v1 (widener-instance-v1 widener-instance))
       (v2 (widener-instance-v2 widener-instance)))
  (c:specifier-function-definition
   #t p? #f v2
   (c:function-declarator (c:widener-name v1 v2 widener-instances)
			  (c:specifier-parameter v1 "x"))
   (if (empty-abstract-value? v1)
       ;; abstraction
       (list (c:specifier-declaration v2 "r") (c:return "r"))
       (c:return
	(cond
	 ;; See the note for this case in all-subwidener-instances.
	 ((union? v1)
	  (c:dispatch
	   v1
	   "x"
	   (map (lambda (code1 u1)
		 (c:widen u1 v2 (c:union v1 "x" code1) widener-instances))
		(generate-slot-names v1)
		(get-union-values v1))))
	 ;; See the notes for this case in all-subwidener-instances.
	 ((union? v2)
	  (let ((u2 (find-if (lambda (u2) (abstract-value-subset? v1 u2))
			     (get-union-values v2))))
	   (c:call (c:unioner-name u2 v2)
		   (if (void? u2) '() (c:widen v1 u2 "x" widener-instances)))))
	 ;; This assumes that Scheme inexact numbers are printed as C
	 ;; doubles.
	 ((real? v1) (exact->inexact v1))
	 (else
	  (c:call*
	   (c:constructor-name v2)
	   ;; This will only be done on conforming structures since the
	   ;; analysis is almost union free.
	   (map
	    (lambda (code1a v1a v2a)
	     (if (void? v2a)
		 '()
		 (c:widen v1a v2a (c:slot v1 "x" code1a) widener-instances)))
	    (generate-slot-names v1)
	    (aggregate-value-values v1)
	    (aggregate-value-values v2))))))))))

(define (generate-widener-definitions widener-instances)
 ;; abstraction
 (append
  ;; abstraction
  (map (lambda (widener-instance)
	(generate-widener-definition widener-instance widener-instances #t))
       (first widener-instances))
  ;; abstraction
  (map (lambda (widener-instance)
	(generate-widener-definition widener-instance widener-instances #f))
       (second widener-instances))))

(define (generate-panic-definitions vs1-vs2)
 ;; abstraction
 (map (lambda (v)
       (c:specifier-function-definition
	#t #t #t v
	(c:function-declarator (c:builtin-name "panic" v)
			       (c:parameter "char" (c:pointer-declarator "x")))
	;; abstraction
	"fputs(x,stderr);fputc('\\n',stderr);exit(EXIT_FAILURE);"))
      (append (first vs1-vs2) (second vs1-vs2))))

(define (generate-real*real-primitive-definitions s v0 code1 code2 generate)
 ;; abstraction
 (map
  (lambda (v)
   (c:specifier-function-definition
    #t #t #f v0
    (c:function-declarator (c:builtin-name code1 v)
			   (c:specifier-parameter v "x"))
    (c:return
     (cond
      ((union? v)
       (c:dispatch v
		   "x"
		   (map (lambda (code u)
			 (c:call (c:builtin-name code1 u)
				 (if (void? u) '() (c:union v "x" code))))
			(generate-slot-names v)
			(get-union-values v))))
      ((vlad-pair? v)
       (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
	(cond
	 ((union? v1)
	  (c:dispatch
	   v1
	   (c:slot v "x" "a")
	   (map
	    (lambda (code1 u1)
	     (c:call
	      (c:builtin-name code1 (vlad-cons u1 v2))
	      (if (void? (vlad-cons u1 v2))
		  '()
		  (c:call
		   (c:constructor-name (vlad-cons u1 v2))
		   (if (void? u1) '() (c:union v1 (c:slot v "x" "a") code1))
		   (if (void? v2) '() (c:slot v "x" "d"))))))
	    (generate-slot-names v1)
	    (get-union-values v1))))
	 ((union? v2)
	  (c:dispatch
	   v2
	   (c:slot v "x" "d")
	   (map
	    (lambda (code2 u2)
	     (c:call (c:builtin-name code1 (vlad-cons v1 u2))
		     (if (void? (vlad-cons v1 u2))
			 '()
			 (c:call (c:constructor-name (vlad-cons v1 u2))
				 (if (void? v1) '() (c:slot v "x" "a"))
				 (if (void? u2)
				     '()
				     (c:union v2 (c:slot v "x" "d") code2))))))
	    (generate-slot-names v2)
	    (get-union-values v2))))
	 ((and (vlad-real? v1) (vlad-real? v2))
	  (generate (if (void? v1) v1 (c:slot v "x" "a"))
		    (if (void? v2) v2 (c:slot v "x" "d"))))
	 (else (c:panic v0 (format #f "Argument to ~a is invalid" code2))))))
      (else (c:panic v0 (format #f "Argument to ~a is invalid" code2)))))))
  (all-primitives s)))

(define (generate-real-primitive-definitions s v0 code1 code2 generate)
 ;; abstraction
 (map
  (lambda (v)
   (c:specifier-function-definition
    #t #t #f v0
    (c:function-declarator (c:builtin-name code1 v)
			   (c:specifier-parameter v "x"))
    (c:return
     (cond
      ((union? v)
       (c:dispatch v
		   "x"
		   (map (lambda (code u)
			 (c:call (c:builtin-name code1 u)
				 (if (void? u) '() (c:union v "x" code))))
			(generate-slot-names v)
			(get-union-values v))))
      ((vlad-real? v) (generate (if (void? v) v "x")))
      (else (c:panic v0 (format #f "Argument to ~a is invalid" code2)))))))
  (all-primitives s)))

(define (generate-unary-ad-definition v f code generate p?)
 ;; here I am: The result of f might violate the syntactic constraints.
 (c:specifier-function-definition
  ;; The call to f might issue "might" warnings and might return an empty
  ;; abstract value.
  #t p? #f (f v)
  (c:function-declarator (c:builtin-name code v) (c:specifier-parameter v "x"))
  (c:return (generate v))))

(define (generate-unary-ad-definitions s descend? f code generate)
 (let ((vs1a-vs2a (all-sorted-unary-ad s descend?)))
  ;; abstraction
  (append
   ;; abstraction
   (map (lambda (v) (generate-unary-ad-definition v f code generate #t))
	(first vs1a-vs2a))
   ;; abstraction
   (map (lambda (v) (generate-unary-ad-definition v f code generate #f))
	(second vs1a-vs2a)))))

(define (generate-binary-ad-definition v g-value code generate p?)
 (c:specifier-function-definition
  ;; The call to g-value might issue "might" warnings and might return an empty
  ;; abstract value.
  #t p? #f (g-value v)
  (c:function-declarator (c:builtin-name code v) (c:specifier-parameter v "x"))
  (c:return (generate v))))

(define (generate-binary-ad-definitions
	 s descend? f? f f-inverse g-value aggregates-match? before code
	 generate)
 ;; here I am: The results of f, f-inverse, and g-value might violate the
 ;;            syntactic constraints.
 (let ((vs1a-vs2a (all-sorted-binary-ad
		   s descend? f? f f-inverse aggregates-match? before)))
  ;; abstraction
  (append
   ;; abstraction
   (map (lambda (v) (generate-binary-ad-definition v g-value code generate #t))
	(first vs1a-vs2a))
   ;; abstraction
   (map (lambda (v) (generate-binary-ad-definition v g-value code generate #f))
	(second vs1a-vs2a)))))

(define (generate-zero-definitions widener-instances)
 (generate-unary-ad-definitions
  'zero (lambda (v) #t) zero "zero"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (zero u)
		     (zero v)
		     (c:call (c:builtin-name "zero" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((or (nonrecursive-closure? v)
	 (recursive-closure? v)
	 (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v)
	 (tagged-pair? v))
     (c:call* (c:constructor-name (zero v))
	      (map (lambda (code1 v1)
		    (if (void? (zero v1))
			'()
			(c:call (c:builtin-name "zero" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else 'error)))))

(define (generate-perturb-definitions widener-instances)
 (generate-unary-ad-definitions
  'perturb
  (lambda (v)
   (and (not (perturbation-tagged-value? v))
	(not (bundle? v))
	(not (sensitivity-tagged-value? v))
	(not (reverse-tagged-value? v))))
  perturb "perturb"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (perturb u)
		     (perturb v)
		     (c:call (c:builtin-name "perturb" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((or (vlad-real? v)
	 (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v))
     (c:call (c:constructor-name (perturb v)) (if (void? v) '() "x")))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (perturb v))
	      (map (lambda (code1 v1)
		    (if (void? (perturb v1))
			'()
			(c:call (c:builtin-name "perturb" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else 'error)))))

(define (generate-unperturb-definitions widener-instances)
 (generate-unary-ad-definitions
  'unperturb
  (lambda (v)
   (and (perturbation-value? v) (not (perturbation-tagged-value? v))))
  unperturb "unperturb"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (unperturb u)
		     (unperturb v)
		     (c:call (c:builtin-name "unperturb" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((perturbation-tagged-value? v) (c:slot v "x" "p"))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (unperturb v))
	      (map (lambda (code1 v1)
		    (if (void? (unperturb v1))
			'()
			(c:call (c:builtin-name "unperturb" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else (c:panic (unperturb v)
		   "Argument to unperturb is a non-perturbation value"))))))

(define (generate-primal-definitions widener-instances)
 (generate-unary-ad-definitions
  'primal (lambda (v) (and (forward-value? v) (not (bundle? v))))
  primal "primal"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (primal u)
		     (primal v)
		     (c:call (c:builtin-name "primal" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((bundle? v) (c:slot v "x" "p"))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (primal v))
	      (map (lambda (code1 v1)
		    (if (void? (primal v1))
			'()
			(c:call (c:builtin-name "primal" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else (c:panic (primal v) "Argument to primal is a non-forward value"))))))

(define (generate-tangent-definitions widener-instances)
 (generate-unary-ad-definitions
  'tangent (lambda (v) (and (forward-value? v) (not (bundle? v))))
  tangent "tangent"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (tangent u)
		     (tangent v)
		     (c:call (c:builtin-name "tangent" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((bundle? v) (c:slot v "x" "t"))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (tangent v))
	      (map (lambda (code1 v1)
		    (if (void? (tangent v1))
			'()
			(c:call (c:builtin-name "tangent" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else
     (c:panic (tangent v) "Argument to tangent is a non-forward value"))))))

(define (bundle-before v)
 (cond
  ((union? v) (get-union-values v))
  ((vlad-pair? v)
   (cond ((union? (vlad-car v))
	  (map (lambda (u) (vlad-cons u (vlad-cdr v)))
	       (get-union-values (vlad-car v))))
	 ((union? (vlad-cdr v))
	  (map (lambda (u) (vlad-cons (vlad-car v) u))
	       (get-union-values (vlad-cdr v))))
	 ((bundle-aggregates-match? (vlad-car v) (vlad-cdr v))
	  (map (lambda (v) (vlad-cons (primal v) (tangent v)))
	       (aggregate-value-values (bundle (vlad-car v) (vlad-cdr v)))))
	 ((and (perturbation-tagged-value? (vlad-cdr v))
	       (union? (unperturb (vlad-cdr v))))
	  (map (lambda (u) (vlad-cons (vlad-car v) (perturb u)))
	       (get-union-values (unperturb (vlad-cdr v)))))
	 (else '())))
  (else '())))

(define (generate-bundle-definitions widener-instances)
 (generate-binary-ad-definitions
  'bundle
  (lambda (v)
   (and (not (perturbation-tagged-value? v))
	(not (bundle? v))
	(not (sensitivity-tagged-value? v))
	(not (reverse-tagged-value? v))))
  perturbation-tagged-value? perturb unperturb bundle-value
  bundle-aggregates-match? bundle-before "bundle"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (bundle-value u)
		     (bundle-value v)
		     (c:call (c:builtin-name "bundle" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((vlad-pair? v)
     (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
      (cond
       ((union? v1)
	(c:dispatch
	 v1
	 (c:slot v "x" "a")
	 (map (lambda (code1 u1)
	       (c:widen
		(bundle u1 v2)
		(bundle v1 v2)
		(c:call (c:builtin-name "bundle" (vlad-cons u1 v2))
			(if (void? (vlad-cons u1 v2))
			    '()
			    (c:call (c:constructor-name (vlad-cons u1 v2))
				    (if (void? u1)
					'()
					(c:union v1 (c:slot v "x" "a") code1))
				    (if (void? v2) '() (c:slot v "x" "d")))))
		widener-instances))
	      (generate-slot-names v1)
	      (get-union-values v1))))
       ((union? v2)
	(c:dispatch
	 v2
	 (c:slot v "x" "d")
	 (map
	  (lambda (code2 u2)
	   (c:widen
	    (bundle v1 u2)
	    (bundle v1 v2)
	    (c:call (c:builtin-name "bundle" (vlad-cons v1 u2))
		    (if (void? (vlad-cons v1 u2))
			'()
			(c:call (c:constructor-name (vlad-cons v1 u2))
				(if (void? v1) '() (c:slot v "x" "a"))
				(if (void? u2)
				    '()
				    (c:union v2 (c:slot v "x" "d") code2)))))
	    widener-instances))
	  (generate-slot-names v2)
	  (get-union-values v2))))
       ((and (perturbation-tagged-value? v2) (union? (unperturb v2)))
	(c:dispatch
	 (unperturb v2)
	 (c:slot v2 (c:slot v "x" "d") "p")
	 (map
	  (lambda (code2 u2)
	   (c:widen
	    (bundle v1 (perturb u2))
	    (bundle v1 v2)
	    (c:call
	     (c:builtin-name "bundle" (vlad-cons v1 (perturb u2)))
	     (if (void? (vlad-cons v1 (perturb u2)))
		 '()
		 (c:call
		  (c:constructor-name (vlad-cons v1 (perturb u2)))
		  (if (void? v1) '() (c:slot v "x" "a"))
		  (if (void? (perturb u2))
		      '()
		      (c:call (c:constructor-name (perturb u2))
			      (if (void? u2)
				  '()
				  (c:union (unperturb v2)
					   (c:slot v2 (c:slot v "x" "d") "p")
					   code2)))))))
	    widener-instances))
	  (generate-slot-names (unperturb v2))
	  (get-union-values (unperturb v2)))))
       ((and (or (vlad-empty-list? v1)
		 (vlad-true? v1)
		 (vlad-false? v1)
		 (primitive-procedure? v1))
	     (every-bundlable? v1 v2))
	;; In all cases, the result will be void so this case should never
	;; happen.
	'error)
       ((or (and (vlad-real? v1) (every-bundlable? v1 v2))
	    ;; here I am: need to check conformance
	    ;;            even when one or both arguments is void
	    ;;            and even when one or both arguments is deep
	    (perturbation-tagged-value? v1)
	    (bundle? v1)
	    (sensitivity-tagged-value? v1)
	    (reverse-tagged-value? v1))
	(c:call (c:constructor-name (bundle v1 v2))
		(if (void? v1) '() (c:slot v "x" "a"))
		(if (void? v2) '() (c:slot v "x" "d"))))
       ((or (and (nonrecursive-closure? v1)
		 (nonrecursive-closure? v2)
		 (perturbation-parameter? (nonrecursive-closure-parameter v2))
		 (dereferenced-nonrecursive-closure-match? v1 (unperturb v2)))
	    (and (recursive-closure? v1)
		 (recursive-closure? v2)
		 (perturbation-parameter? (recursive-closure-parameter v2))
		 (dereferenced-recursive-closure-match? v1 (unperturb v2)))
	    (and (tagged-pair? v1)
		 (tagged-pair? v2)
		 (tagged? 'perturbation (tagged-pair-tags v2))
		 (equal-tags?
		  (tagged-pair-tags v1)
		  (remove-tag 'perturbation (tagged-pair-tags v2)))))
	(c:call*
	 (c:constructor-name (bundle v1 v2))
	 (map
	  (lambda (code3a code3b v3)
	   (if (void? v3)
	       '()
	       (c:call
		(c:builtin-name "bundle" (vlad-cons (primal v3) (tangent v3)))
		(if (void? (vlad-cons (primal v3) (tangent v3)))
		    '()
		    (c:call
		     (c:constructor-name (vlad-cons (primal v3) (tangent v3)))
		     (if (void? (primal v3))
			 '()
			 (c:slot v1 (c:slot v "x" "a") code3a))
		     (if (void? (tangent v3))
			 '()
			 (c:slot v2 (c:slot v "x" "d") code3b)))))))
	  (generate-slot-names v1)
	  (generate-slot-names v2)
	  (aggregate-value-values (bundle v1 v2)))))
       (else
	(c:panic (bundle-value v) "Arguments to bundle do not conform")))))
    (else (c:panic (bundle-value v) "Arguments to bundle do not conform"))))))

(define (generate-sensitize-definitions widener-instances)
 (generate-unary-ad-definitions
  'sensitize
  (lambda (v)
   (and (not (perturbation-tagged-value? v))
	(not (bundle? v))
	(not (sensitivity-tagged-value? v))
	(not (reverse-tagged-value? v))))
  sensitize "sensitize"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (sensitize u)
		     (sensitize v)
		     (c:call (c:builtin-name "sensitize" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((or (vlad-real? v)
	 (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v))
     (c:call (c:constructor-name (sensitize v)) (if (void? v) '() "x")))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (sensitize v))
	      (map (lambda (code1 v1)
		    (if (void? (sensitize v1))
			'()
			(c:call (c:builtin-name "sensitize" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else 'error)))))

(define (generate-unsensitize-definitions widener-instances)
 (generate-unary-ad-definitions
  'unsensitize
  (lambda (v) (and (sensitivity-value? v) (not (sensitivity-tagged-value? v))))
  unsensitize "unsensitize"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (unsensitize u)
		     (unsensitize v)
		     (c:call (c:builtin-name "unsensitize" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((sensitivity-tagged-value? v) (c:slot v "x" "p"))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (unsensitize v))
	      (map (lambda (code1 v1)
		    (if (void? (unsensitize v1))
			'()
			(c:call (c:builtin-name "unsensitize" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else (c:panic (unsensitize v)
		   "Argument to unsensitize is a non-sensitivity value"))))))

(define (plus-before v)
 (cond ((union? v) (get-union-values v))
       ((vlad-pair? v)
	(cond ((union? (vlad-car v))
	       (map (lambda (u) (vlad-cons u (vlad-cdr v)))
		    (get-union-values (vlad-car v))))
	      ((union? (vlad-cdr v))
	       (map (lambda (u) (vlad-cons (vlad-car v) u))
		    (get-union-values (vlad-cdr v))))
	      ((plus-aggregates-match? (vlad-car v) (vlad-cdr v))
	       (map vlad-cons
		    (aggregate-value-values (vlad-car v))
		    (aggregate-value-values (vlad-cdr v))))
	      (else '())))
       (else '())))

(define (generate-plus-definitions widener-instances)
 (generate-binary-ad-definitions
  'plus
  (lambda (v) #t) (lambda (v) #f)
  identity identity plus-value plus-aggregates-match? plus-before "plus"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (plus-value u)
		     (plus-value v)
		     (c:call (c:builtin-name "plus" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((vlad-pair? v)
     (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
      (cond
       ((union? v1)
	(c:dispatch
	 v1
	 (c:slot v "x" "a")
	 (map (lambda (code1 u1)
	       (c:widen
		(plus u1 v2)
		(plus v1 v2)
		(c:call (c:builtin-name "plus" (vlad-cons u1 v2))
			(if (void? (vlad-cons u1 v2))
			    '()
			    (c:call (c:constructor-name (vlad-cons u1 v2))
				    (if (void? u1)
					'()
					(c:union v1 (c:slot v "x" "a") code1))
				    (if (void? v2) '() (c:slot v "x" "d")))))
		widener-instances))
	      (generate-slot-names v1)
	      (get-union-values v1))))
       ((union? v2)
	(c:dispatch
	 v2
	 (c:slot v "x" "d")
	 (map
	  (lambda (code2 u2)
	   (c:widen
	    (plus v1 u2)
	    (plus v1 v2)
	    (c:call (c:builtin-name "plus" (vlad-cons v1 u2))
		    (if (void? (vlad-cons v1 u2))
			'()
			(c:call (c:constructor-name (vlad-cons v1 u2))
				(if (void? v1) '() (c:slot v "x" "a"))
				(if (void? u2)
				    '()
				    (c:union v2 (c:slot v "x" "d") code2)))))
	    widener-instances))
	  (generate-slot-names v2)
	  (get-union-values v2))))
       ((or
	 (and (vlad-empty-list? v1) (vlad-empty-list? v2))
	 (and (vlad-true? v1) (vlad-true? v2))
	 (and (vlad-false? v1) (vlad-false? v2))
	 (and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2)))
	;; In all cases, the result will be void so this case should never
	;; happen.
	'error)
       ((and (vlad-real? v1) (vlad-real? v2))
  	(c:binary
	 ;; This assumes that Scheme inexact numbers are printed as C doubles.
	 (if (void? v1) (exact->inexact v1) (c:slot v "x" "a"))
	 "+"
	 ;; This assumes that Scheme inexact numbers are printed as C doubles.
	 (if (void? v2) (exact->inexact v2) (c:slot v "x" "d"))))
       ((or (and (nonrecursive-closure? v1)
		 (nonrecursive-closure? v2)
		 (dereferenced-nonrecursive-closure-match? v1 v2))
	    (and (recursive-closure? v1)
		 (recursive-closure? v2)
		 (dereferenced-recursive-closure-match? v1 v2))
	    (and (perturbation-tagged-value? v1)
		 (perturbation-tagged-value? v2))
	    (and (bundle? v1) (bundle? v2))
	    (and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	    (and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	    (and (tagged-pair? v1)
		 (tagged-pair? v2)
		 (equal-tags? (tagged-pair-tags v1) (tagged-pair-tags v2))))
	(c:call*
	 (c:constructor-name (plus v1 v2))
	 (map
	  (lambda (code3a code3b v3 v3a v3b)
	   (if (void? v3)
	       '()
	       (c:call
		(c:builtin-name "plus" (vlad-cons v3a v3b))
		(if (void? (vlad-cons v3a v3b))
		    '()
		    (c:call
		     (c:constructor-name (vlad-cons v3a v3b))
		     (if (void? v3a) '() (c:slot v1 (c:slot v "x" "a") code3a))
		     (if (void? v3b)
			 '()
			 (c:slot v2 (c:slot v "x" "d") code3b)))))))
	  (generate-slot-names v1)
	  (generate-slot-names v2)
	  (aggregate-value-values (plus v1 v2))
	  (aggregate-value-values v1)
	  (aggregate-value-values v2))))
       (else (c:panic (plus-value v) "Arguments to plus do not conform")))))
    (else (c:panic (plus-value v) "Arguments to plus do not conform"))))))

(define (generate-*j-definitions widener-instances)
 (generate-unary-ad-definitions
  '*j
  (lambda (v)
   (and (not (perturbation-tagged-value? v))
	(not (bundle? v))
	(not (sensitivity-tagged-value? v))
	(not (reverse-tagged-value? v))))
  *j "starj"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (*j u)
		     (*j v)
		     (c:call (c:builtin-name "starj" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((or (vlad-real? v)
	 (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v))
     (c:call (c:constructor-name (*j v)) (if (void? v) '() "x")))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (*j v))
	      (map (lambda (code1 v1)
		    (if (void? (*j v1))
			'()
			(c:call (c:builtin-name "starj" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else 'error)))))

(define (generate-*j-inverse-definitions widener-instances)
 (generate-unary-ad-definitions
  '*j-inverse
  (lambda (v) (and (reverse-value? v) (not (reverse-tagged-value? v))))
  *j-inverse "starj_inverse"
  (lambda (v)
   (cond
    ((union? v)
     (c:dispatch
      v
      "x"
      (map (lambda (code u)
	    (c:widen (*j-inverse u)
		     (*j-inverse v)
		     (c:call (c:builtin-name "starj_inverse" u)
			     (if (void? u) '() (c:union v "x" code)))
		     widener-instances))
	   (generate-slot-names v)
	   (get-union-values v))))
    ((reverse-tagged-value? v) (c:slot v "x" "p"))
    ((or (nonrecursive-closure? v) (recursive-closure? v) (tagged-pair? v))
     (c:call* (c:constructor-name (*j-inverse v))
	      (map (lambda (code1 v1)
		    (if (void? (*j-inverse v1))
			'()
			(c:call (c:builtin-name "starj_inverse" v1)
				(if (void? v1) '() (c:slot v "x" code1)))))
		   (generate-slot-names v)
		   (aggregate-value-values v))))
    (else (c:panic (*j-inverse v)
		   "Argument to *j-inverse is a non-reverse value"))))))

(define (generate-if-and-function-definition
	 instance bs function-instances widener-instances p?)
 (cond
  ((if-instance? instance)
   (let* ((v (if-instance-v instance))
	  (v1 (vlad-car v))
	  (v2 (vlad-cdr v))
	  (v3 (vlad-car v2))
	  (v4 (vlad-cdr v2))
	  (v5 (cond
	       ((and (some vlad-false? (union-members v1))
		     (some (lambda (u) (not (vlad-false? u)))
			   (union-members v1)))
		;; here I am: The result might violate the syntactic
		;;            constraints.
		(abstract-value-union (abstract-apply v3 (vlad-empty-list))
				      (abstract-apply v4 (vlad-empty-list))))
	       ((some vlad-false? (union-members v1))
		(abstract-apply v4 (vlad-empty-list)))
	       ((some (lambda (u) (not (vlad-false? u))) (union-members v1))
		(abstract-apply v3 (vlad-empty-list)))
	       (else (internal-error)))))
    (c:specifier-function-definition
     #t #t #f v5
     (c:function-declarator (c:builtin-name "if_procedure" v)
			    (c:specifier-parameter v "x"))
     (c:return
      (cond
       ((and (some vlad-false? (union-members v1))
	     (some (lambda (u) (not (vlad-false? u))) (union-members v1)))
	(let ((v6 (abstract-apply v3 (vlad-empty-list)))
	      (v7 (abstract-apply v4 (vlad-empty-list))))
	 (c:conditional
	  (c:binary
	   ;; The type tag is always unboxed.
	   (c:tag v1 (c:slot v "x" "a"))
	   "!="
	   ;; This uses per-union tags here instead of per-program tags.
	   (position-if vlad-false? (union-members v1)))
	  (c:widen
	   v6
	   v5
	   (c:call (c:function-name v3 (vlad-empty-list) function-instances)
		   ;; here I am: widen?
		   (if (void? v3) '() (c:slot v2 (c:slot v "x" "d") "a")))
	   widener-instances)
	  (c:widen
	   v7
	   v5
	   (c:call (c:function-name v4 (vlad-empty-list) function-instances)
		   ;; here I am: widen?
		   (if (void? v4) '() (c:slot v2 (c:slot v "x" "d") "d")))
	   widener-instances))))
       ((some vlad-false? (union-members v1))
	(c:call (c:function-name v4 (vlad-empty-list) function-instances)
		;; here I am: widen?
		(if (void? v4) '() (c:slot v2 (c:slot v "x" "d") "d"))))
       ((some (lambda (u) (not (vlad-false? u))) (union-members v1))
	(c:call (c:function-name v3 (vlad-empty-list) function-instances)
		;; here I am: widen?
		(if (void? v3) '() (c:slot v2 (c:slot v "x" "d") "a"))))
       (else (internal-error)))))))
  ((function-instance? instance)
   (let ((v1 (function-instance-v1 instance))
	 (v2 (function-instance-v2 instance)))
    (c:specifier-function-definition
     #t p? #f
     (abstract-apply v1 v2)
     (c:function-declarator (c:function-name v1 v2 function-instances)
			    (c:specifier-parameter v1 "c")
			    (c:specifier-parameter v2 "x"))
     ;; abstraction
     (list
      ;; here I am
      (generate-destructure (closure-parameter v1) (closure-body v1) v2 "x")
      (generate-letrec-bindings
       (closure-body v1)
       ;; here I am
       (let ((vss (construct-abstract-environments v1 v2)))
	(assert (= (length vss) 1))
	(map widen-abstract-value (first vss)))
       (closure-variables v1)
       (cond ((nonrecursive-closure? v1) '())
	     ((recursive-closure? v1)
	      (vector->list (recursive-closure-procedure-variables v1)))
	     (else (internal-error)))
       widener-instances)
      (c:return
       (generate-expression
	(closure-body v1)
	;; here I am
	(let ((vss (construct-abstract-environments v1 v2)))
	 (assert (= (length vss) 1))
	 (map widen-abstract-value (first vss)))
	v1
	(closure-variables v1)
	(cond ((nonrecursive-closure? v1) '())
	      ((recursive-closure? v1)
	       (vector->list (recursive-closure-procedure-variables v1)))
	      (else (internal-error)))
	bs
	function-instances
	widener-instances))))))
  (else (internal-error))))

(define (generate-if-and-function-definitions
	 bs function-instances widener-instances instances1-instances2)
 ;; abstraction
 (append
  ;; abstraction
  (map (lambda (instance)
	(generate-if-and-function-definition
	 instance bs function-instances widener-instances #t))
       (first instances1-instances2))
  ;; abstraction
  (map (lambda (instance)
	(generate-if-and-function-definition
	 instance bs function-instances widener-instances #f))
       (second instances1-instances2))))

;;; Top-level generator

(define (generate e bs bs0)
 (determine-void?!)
 (for-each-indexed (lambda (x i) (set-variable-index! x i)) *variables*)
 (let* ((function-instances (time-it (all-function-instances)))
	(widener-instances (time-it (all-widener-instances)))
	(vs1-vs2 (time-it (all-nested-abstract-values widener-instances)))
	(instances1-instances2 (time-it (all-instances1-instances2 function-instances))))
  (determine-void?!)
  (for-each-indexed
   (lambda (v i)
    (cond ((nonrecursive-closure? v) (set-nonrecursive-closure-c:index! v i))
	  ((recursive-closure? v) (set-recursive-closure-c:index! v i))
	  ((perturbation-tagged-value? v)
	   (set-perturbation-tagged-value-c:index! v i))
	  ((bundle? v) (set-bundle-c:index! v i))
	  ((sensitivity-tagged-value? v)
	   (set-sensitivity-tagged-value-c:index! v i))
	  ((reverse-tagged-value? v) (set-reverse-tagged-value-c:index! v i))
	  ((tagged-pair? v) (set-tagged-pair-c:index! v i))
	  ((union? v) (set-union-c:index! v i))
	  (else (set! *c:indices* (cons (cons v i) *c:indices*)))))
   (append (first vs1-vs2) (second vs1-vs2)))
  (for-each
   (lambda (v)
    (cond ((nonrecursive-closure? v) (set-nonrecursive-closure-boxed?! v #t))
	  ((recursive-closure? v) (set-recursive-closure-boxed?! v #t))
	  ((perturbation-tagged-value? v)
	   (set-perturbation-tagged-value-boxed?! v #t))
	  ((bundle? v) (set-bundle-boxed?! v #t))
	  ((sensitivity-tagged-value? v)
	   (set-sensitivity-tagged-value-boxed?! v #t))
	  ((reverse-tagged-value? v) (set-reverse-tagged-value-boxed?! v #t))
	  ((tagged-pair? v) (set-tagged-pair-boxed?! v #t))
	  ((union? v) (set-union-boxed?! v #t))
	  (else (internal-error))))
   (second vs1-vs2))
  ;; abstraction
  (list
   "#include <math.h>" #\newline
   "#include <stdio.h>" #\newline
   "#include <stdlib.h>" #\newline
   "#include <gc/gc.h>" #\newline
   "#define INLINE inline __attribute__ ((always_inline))" #\newline
   "#define NORETURN __attribute__ ((noreturn))" #\newline
   (time-it (generate-struct-and-union-declarations vs1-vs2))
   (time-it (generate-constructor-declarations vs1-vs2))
   (time-it (generate-widener-declarations widener-instances))
   (time-it (generate-panic-declarations vs1-vs2))
   (time-it (generate-real*real-primitive-declarations '+ (abstract-real) "add"))
   (time-it (generate-real*real-primitive-declarations '- (abstract-real) "minus"))
   (time-it (generate-real*real-primitive-declarations '* (abstract-real) "times"))
   (time-it (generate-real*real-primitive-declarations '/ (abstract-real) "divide"))
   (time-it (generate-real*real-primitive-declarations 'atan (abstract-real) "atantwo"))
   (time-it (generate-real*real-primitive-declarations '= (abstract-boolean) "eq"))
   (time-it (generate-real*real-primitive-declarations '< (abstract-boolean) "lt"))
   (time-it (generate-real*real-primitive-declarations '> (abstract-boolean) "gt"))
   (time-it (generate-real*real-primitive-declarations '<= (abstract-boolean) "le"))
   (time-it (generate-real*real-primitive-declarations '>= (abstract-boolean) "ge"))
   (time-it (generate-real-primitive-declarations 'zero? (abstract-boolean) "iszero"))
   (time-it (generate-real-primitive-declarations 'positive? (abstract-boolean) "positive"))
   (time-it (generate-real-primitive-declarations 'negative? (abstract-boolean) "negative"))
   ;; here I am: null, boolean, is_real, pair, procedure, perturbation,
   ;;            forward, sensitivity, and reverse
   (time-it (c:specifier-function-declaration
	     #t #t #f (abstract-real) (c:function-declarator "read_real")))
   (time-it (generate-real-primitive-declarations 'real (abstract-real) "real"))
   (time-it (c:specifier-function-declaration
	     #t #t #f (abstract-real)
	     (c:function-declarator
	      "write_real" (c:specifier-parameter (abstract-real) "x"))))
   (time-it (generate-real-primitive-declarations 'write (abstract-real) "write"))
   (time-it (generate-unary-ad-declarations 'zero (lambda (v) #t) zero "zero"))
   (time-it (generate-unary-ad-declarations
	     'perturb
	     (lambda (v)
	      (and (not (perturbation-tagged-value? v))
		   (not (bundle? v))
		   (not (sensitivity-tagged-value? v))
		   (not (reverse-tagged-value? v))))
	     perturb "perturb"))
   (time-it (generate-unary-ad-declarations
	     'unperturb
	     (lambda (v)
	      (and (perturbation-value? v) (not (perturbation-tagged-value? v))))
	     unperturb "unperturb"))
   (time-it (generate-unary-ad-declarations
	     'primal (lambda (v) (and (forward-value? v) (not (bundle? v))))
	     primal "primal"))
   (time-it (generate-unary-ad-declarations
	     'tangent (lambda (v) (and (forward-value? v) (not (bundle? v))))
	     tangent "tangent"))
   (time-it (generate-binary-ad-declarations
	     'bundle
	     (lambda (v)
	      (and (not (perturbation-tagged-value? v))
		   (not (bundle? v))
		   (not (sensitivity-tagged-value? v))
		   (not (reverse-tagged-value? v))))
	     perturbation-tagged-value? perturb unperturb bundle-value
	     bundle-aggregates-match? bundle-before "bundle"))
   (time-it (generate-unary-ad-declarations
	     'sensitize
	     (lambda (v)
	      (and (not (perturbation-tagged-value? v))
		   (not (bundle? v))
		   (not (sensitivity-tagged-value? v))
		   (not (reverse-tagged-value? v))))
	     sensitize "sensitize"))
   (time-it (generate-unary-ad-declarations
	     'unsensitize
	     (lambda (v)
	      (and (sensitivity-value? v) (not (sensitivity-tagged-value? v))))
	     unsensitize "unsensitize"))
   (time-it (generate-binary-ad-declarations
	     'plus (lambda (v) #t) (lambda (v) #f) identity identity plus-value
	     plus-aggregates-match? plus-before "plus"))
   (time-it (generate-unary-ad-declarations
	     '*j
	     (lambda (v)
	      (and (not (perturbation-tagged-value? v))
		   (not (bundle? v))
		   (not (sensitivity-tagged-value? v))
		   (not (reverse-tagged-value? v))))
	     *j "starj"))
   (time-it (generate-unary-ad-declarations
	     '*j-inverse
	     (lambda (v) (and (reverse-value? v) (not (reverse-tagged-value? v))))
	     *j-inverse "starj_inverse"))
   (time-it (generate-if-and-function-declarations
	     function-instances instances1-instances2))
   (time-it (c:function-declaration #f #f #f "int" (c:function-declarator "main")))
   (time-it (generate-constructor-definitions vs1-vs2))
   (time-it (generate-widener-definitions widener-instances))
   (time-it (generate-panic-definitions vs1-vs2))
   (time-it (generate-real*real-primitive-definitions
	     '+ (abstract-real) "add" "+"
	     (lambda (code1 code2) (c:binary code1 "+" code2))))
   (time-it (generate-real*real-primitive-definitions
	     '- (abstract-real) "minus" "-"
	     (lambda (code1 code2) (c:binary code1 "-" code2))))
   (time-it (generate-real*real-primitive-definitions
	     '* (abstract-real) "times" "*"
	     (lambda (code1 code2) (c:binary code1 "*" code2))))
   (time-it (generate-real*real-primitive-definitions
	     '/ (abstract-real) "divide" "/"
	     (lambda (code1 code2) (c:binary code1 "/" code2))))
   (time-it (generate-real*real-primitive-definitions
	     'atan (abstract-real) "atantwo" "atan"
	     (lambda (code1 code2) (c:call "atan2" code1 code2))))
   (time-it (generate-real*real-primitive-definitions
	     '= (abstract-boolean) "eq" "=" (c:binary-boolean "==")))
   (time-it (generate-real*real-primitive-definitions
	     '< (abstract-boolean) "lt" "<" (c:binary-boolean "<")))
   (time-it (generate-real*real-primitive-definitions
	     '> (abstract-boolean) "gt" ">" (c:binary-boolean ">")))
   (time-it (generate-real*real-primitive-definitions
	     '<= (abstract-boolean) "le" "<=" (c:binary-boolean "<=")))
   (time-it (generate-real*real-primitive-definitions
	     '>= (abstract-boolean) "ge" ">=" (c:binary-boolean ">=")))
   (time-it (generate-real-primitive-definitions
	     'zero? (abstract-boolean) "iszero" "zero?" (c:unary-boolean "==")))
   (time-it (generate-real-primitive-definitions
	     'positive? (abstract-boolean) "positive" "positive?" (c:unary-boolean ">")))
   (time-it (generate-real-primitive-definitions
	     'negative? (abstract-boolean) "negative" "negative?" (c:unary-boolean "<")))
   ;; here I am: null, boolean, is_real, pair, procedure, perturbation,
   ;;            forward, sensitivity, and reverse
   (time-it (c:specifier-function-definition
	     #t #t #f (abstract-real) (c:function-declarator "read_real")
	     ;; abstraction
	     (list (c:specifier-declaration (abstract-real) "x")
		   ;; abstraction
		   "scanf(\"%lf\",&x);"
		   (c:return "x"))))
   (time-it (generate-real-primitive-definitions
	     'real (abstract-real) "real" "real" (lambda (code) code)))
   (time-it (c:specifier-function-definition
	     #t #t #f (abstract-real)
	     (c:function-declarator
	      "write_real" (c:specifier-parameter (abstract-real) "x"))
	     ;; abstraction
	     (list
	      ;; abstraction
	      "printf(\"%.18lg\\n\",x);"
	      (c:return "x"))))
   (time-it (generate-real-primitive-definitions
	     'write (abstract-real) "write" "write"
	     (lambda (code) (c:call "write_real" code))))
   (time-it (generate-zero-definitions widener-instances))
   (time-it (generate-perturb-definitions widener-instances))
   (time-it (generate-unperturb-definitions widener-instances))
   (time-it (generate-primal-definitions widener-instances))
   (time-it (generate-tangent-definitions widener-instances))
   (time-it (generate-bundle-definitions widener-instances))
   (time-it (generate-sensitize-definitions widener-instances))
   (time-it (generate-unsensitize-definitions widener-instances))
   (time-it (generate-plus-definitions widener-instances))
   (time-it (generate-*j-definitions widener-instances))
   (time-it (generate-*j-inverse-definitions widener-instances))
   (time-it (generate-if-and-function-definitions
	     bs function-instances widener-instances instances1-instances2))
   (let ((vs (environment-binding-values
	      (first (expression-environment-bindings e)))))
    (time-it (c:function-definition
	      #f #f #f
	      "int"
	      (c:function-declarator "main")
	      ;; abstraction
	      (list
	       (generate-letrec-bindings
		e vs (free-variables e) '() widener-instances)
	       (if (void? (abstract-eval1
			   e
			   (environment-binding-values
			    (first (expression-environment-bindings e)))))
		   '()
		   ;; abstraction
		   (list
		    (generate-expression e
					 vs
					 ;; A placeholder.
					 (empty-abstract-value)
					 (free-variables e)
					 '()
					 bs
					 function-instances
					 widener-instances)
		    ;; abstraction
		    ";"))
	       (c:return "0"))))))))

(define (generate-file code pathname)
 (call-with-output-file (replace-extension pathname "c")
  (lambda (output-port)
   (let loop ((code code))
    (cond ((char? code) (write-char code output-port))
	  ((string? code) (display code output-port))
	  ((number? code) (write code output-port))
	  ((pair? code) (loop (car code)) (loop (cdr code)))
	  ((null? code) #f)
	  (else (internal-error)))))))

;;; Serialization

(define (all-subobjects object)
 (let ((objects '()))
  (let loop ((object object))
   (cond ((primitive-procedure? object) #f)
	 ((string? object)
	  (unless (memq object objects) (set! objects (cons object objects))))
	 ((pair? object)
	  (unless (memq object objects)
	   (set! objects (cons object objects))
	   (loop (car object))
	   (loop (cdr object))))
	 ((vector? object)
	  (unless (memq object objects)
	   (set! objects (cons object objects))
	   (for-each-vector loop object)))))
  objects))

(define (serialize-object object objects)
 (cond ((primitive-procedure? object)
	`(primitive-procedure
	  ,(positionq object (map value-binding-value *value-bindings*))))
       ((or (null? object)
	    (boolean? object)
	    (char? object)
	    (and (number? object) (exact? object))
	    (symbol? object))
	object)
       ((and (number? object) (inexact? object))
	`(double ,(double-part object 0)
		 ,(double-part object 1)
		 ,(double-part object 2)
		 ,(double-part object 3)))
       ((or (string? object) (pair? object) (vector? object))
	`(table ,(positionq object objects)))
       (else (internal-error "Cannot serialize this object"))))

(define (serialize object)
 (let ((objects (all-subobjects object)))
  (cons
   (serialize-object object objects)
   (map (lambda (object)
	 (cond ((primitive-procedure? object) (internal-error))
	       ((string? object) object)
	       ((pair? object)
		(cons (serialize-object (car object) objects)
		      (serialize-object (cdr object) objects)))
	       ((vector? object)
		(map-vector (lambda (object) (serialize-object object objects))
			    object))
	       (else (internal-error))))
	objects))))

(define (unserialize-object object objects)
 (cond ((or (null? object)
	    (boolean? object)
	    (char? object)
	    (and (number? object) (exact? object))
	    (symbol? object))
	object)
       ((pair? object)
	(case (first object)
	 ((primitive-procedure)
	  (value-binding-value (list-ref *value-bindings* (second object))))
	 ((double)
	  (make-double
	   (second object) (third object) (fourth object) (fifth object)))
	 ((table) (list-ref objects (second object)))
	 (else (internal-error "Cannot unserialize this object"))))
       (else (internal-error "Cannot unserialize this object"))))

(define (unserialize objects)
 (for-each
  (lambda (object)
   (cond
    ((string? object) #f)
    ((pair? object)
     (set-car! object (unserialize-object (car object) (rest objects)))
     (set-cdr! object (unserialize-object (cdr object) (rest objects))))
    ((vector? object)
     (for-each-n
      (lambda (i)
       (vector-set!
	object i (unserialize-object (vector-ref object i) (rest objects))))
      (vector-length object)))
    (else (internal-error))))
  (rest objects))
 (unserialize-object (first objects) (rest objects)))

(define (write-ebs-to-file bs pathname)
 (call-with-output-file (replace-extension pathname "ebs")
  (lambda (port) (write (serialize bs) port) (newline port))))

(define (read-ebs-from-file pathname)
 (unserialize (read-object-from-file (replace-extension pathname "ebs"))))

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

(define (read-real v)
 (cond (*abstract?*
	(if (vlad-empty-list? v)
	    (abstract-real)
	    (compile-time-warning
	     "Argument might not be an equivalent value" (vlad-empty-list) v)))
       (else (unless (vlad-empty-list? v)
	      (run-time-error
	       "Argument is not an equivalent value" (vlad-empty-list) v))
	     (unimplemented "read-real"))))

(define (unary f s) (lambda (v) (if *abstract?* (map-union f v) (f v))))

(define (unary-ad f s) f)

(define (unary-predicate f s)
 (lambda (v)
  (if *abstract?*
      (map-union (lambda (u) (if (f u) (vlad-true) (vlad-false))) v)
      (if (f v) (vlad-true) (vlad-false)))))

(define (unary-real f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union (lambda (u)
		     (if (vlad-real? u)
			 (if (real? u) (f u) (abstract-real))
			 (compile-time-warning
			  (format #f "Argument to ~a might be invalid" s) u)))
		    v))
	(else (unless (vlad-real? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (f v)))))

(define (unary-real-predicate f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union (lambda (u)
		     (if (vlad-real? u)
			 (if (real? u)
			     (if (f u) (vlad-true) (vlad-false))
			     (abstract-boolean))
			 (compile-time-warning
			  (format #f "Argument to ~a might be invalid" s) u)))
		    v))
	(else (unless (vlad-real? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (if (f v) (vlad-true) (vlad-false))))))

(define (binary-ad f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union
	  (lambda (u)
	   (if (vlad-pair? u)
	       (f (vlad-car u) (vlad-cdr u))
	       (compile-time-warning
		(format #f "Argument to ~a might be invalid" s) u)))
	  v))
	(else (unless (vlad-pair? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (f (vlad-car v) (vlad-cdr v))))))

(define (binary-real f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union
	  (lambda (u)
	   (if (vlad-pair? u)
	       (cross-union
		(lambda (u1 u2)
		 (if (and (vlad-real? u1) (vlad-real? u2))
		     ;; needs work: This may be imprecise for *, /, and atan.
		     (if (and (real? u1) (real? u2)) (f u1 u2) (abstract-real))
		     (compile-time-warning
		      (format #f "Argument to ~a might be invalid" s) u)))
		(vlad-car u)
		(vlad-cdr u))
	       (compile-time-warning
		(format #f "Argument to ~a might be invalid" s) u)))
	  v))
	(else (unless (vlad-pair? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
	       (unless (and (vlad-real? v1) (vlad-real? v2))
		(run-time-error (format #f "Argument to ~a is invalid" s) v))
	       (f v1 v2))))))

(define (binary-real-predicate f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union
	  (lambda (u)
	   (if (vlad-pair? u)
	       (cross-union
		(lambda (u1 u2)
		 (if (and (vlad-real? u1) (vlad-real? u2))
		     (if (and (real? u1) (real? u2))
			 (if (f u1 u2) (vlad-true) (vlad-false))
			 (abstract-boolean))
		     (compile-time-warning
		      (format #f "Argument to ~a might be invalid" s) u)))
		(vlad-car u)
		(vlad-cdr u))
	       (compile-time-warning
		(format #f "Argument to ~a might be invalid" s) u)))
	  v))
	(else (unless (vlad-pair? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
	       (unless (and (vlad-real? v1) (vlad-real? v2))
		(run-time-error (format #f "Argument to ~a is invalid" s) v))
	       (if (f v1 v2) (vlad-true) (vlad-false)))))))

(define (ternary f s)
 (lambda (v)
  (cond (*abstract?*
	 (map-union
	  (lambda (u)
	   (if (vlad-pair? u)
	       (cross-union
		(lambda (u1 u2)
		 (if (vlad-pair? u2)
		     (cross-union (lambda (u21 u22) (f u1 u21 u22))
				  (vlad-car u2)
				  (vlad-cdr u2))
		     (compile-time-warning
		      (format #f "Argument to ~a might be invalid" s) u)))
		(vlad-car u)
		(vlad-cdr u))
	       (compile-time-warning
		(format #f "Argument to ~a might be invalid" s) u)))
	  v))
	(else (unless (vlad-pair? v)
	       (run-time-error (format #f "Argument to ~a is invalid" s) v))
	      (let ((v23 (vlad-cdr v)))
	       (unless (vlad-pair? v23)
		(run-time-error (format #f "Argument to ~a is invalid" s) v))
	       (f (vlad-car v) (vlad-car v23) (vlad-cdr v23)))))))

(define (ternary-prime f s)
 (lambda (v)
  (assert *abstract?*)
  (for-each
   (lambda (u)
    (cond
     ((vlad-pair? u)
      (for-each
       (lambda (u1)
	(for-each
	 (lambda (u2)
	  (cond ((vlad-pair? u2)
		 (for-each (lambda (u21)
			    (for-each (lambda (u22) (f u1 u21 u22))
				      (union-members (vlad-cdr u2))))
			   (union-members (vlad-car u2))))
		(else (compile-time-warning
		       (format #f "Argument to ~a might be invalid" s) u))))
	 (union-members (vlad-cdr u))))
       (union-members (vlad-car u))))
     (else (compile-time-warning
	    (format #f "Argument to ~a might be invalid" s) u))))
   (union-members v))))

(define (define-primitive-procedure x procedure generator forward reverse)
 (set! *value-bindings*
       (cons
	(make-value-binding
	 (new-variable x)
	 (make-primitive-procedure x procedure generator forward reverse 0))
	*value-bindings*)))

(define (constant-unconvert e)
 ;; This is particular to the way the forward and reverse transforms of the
 ;; basis are written. It doesn't handle lexical scope shadowing.
 (cond ((constant-expression? e) e)
       ((variable-access-expression? e)
	(let ((b (find-if (lambda (b)
			   (variable=? (variable-access-expression-variable e)
				       (value-binding-variable b)))
			  *value-bindings*)))
	 (if b (new-constant-expression (value-binding-value b)) e)))
       ((lambda-expression? e)
	(new-lambda-expression
	 (lambda-expression-parameter e)
	 (constant-unconvert (lambda-expression-body e))))
       ((application? e)
	(new-application (constant-unconvert (application-callee e))
			 (constant-unconvert (application-argument e))))
       ((letrec-expression? e)
	(new-letrec-expression
	 (letrec-expression-procedure-variables e)
	 (map constant-unconvert (letrec-expression-lambda-expressions e))
	 (constant-unconvert (letrec-expression-body e))))
       ((cons-expression? e)
	(new-cons-expression (cons-expression-tags e)
			     (constant-unconvert (cons-expression-car e))
			     (constant-unconvert (cons-expression-cdr e))))
       (else (internal-error))))

(define (evaluate-in-top-level-environment e)
 (let ((wizard? *wizard?*))
  (set! *wizard?* #t)
  (syntax-check-expression! e)
  (set! *wizard?* wizard?))
 (new-nonrecursive-closure
  '()
  (anf-convert-lambda-expression
   (alpha-convert (constant-unconvert (internalize-expression e))))))

(define (initialize-forwards-and-reverses!)
 (for-each (lambda (b)
	    (set-primitive-procedure-forward!
	     (value-binding-value b)
	     (evaluate-in-top-level-environment
	      (primitive-procedure-forward (value-binding-value b))))
	    (set-primitive-procedure-reverse!
	     (value-binding-value b)
	     (evaluate-in-top-level-environment
	      (primitive-procedure-reverse (value-binding-value b)))))
	   *value-bindings*))

(define (initialize-basis!)
 (set! *empty-abstract-value* (create-union '()))
 (set! *unions* (cons (empty-abstract-value) *unions*))
 (set-union-interned?! *empty-abstract-value* #t)
 (set! *abstract-boolean* (new-union (list (vlad-true) (vlad-false))))
 (define-primitive-procedure '+
  (binary-real + "+")
  (lambda (v) (c:builtin-name "add" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (+ x1 x2) (perturb (+ x1-unperturbed x2-unperturbed)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (+ x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons +
			     (cons (unsensitize (sensitivity y))
				   (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure '-
  (binary-real - "-")
  (lambda (v) (c:builtin-name "minus" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (- x1 x2) (perturb (- x1-unperturbed x2-unperturbed)))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (- x1 x2))
	       (lambda ((sensitivity y))
		(sensitize
		 (cons -
		       (cons (unsensitize (sensitivity y))
			     (- 0.0 (unsensitize (sensitivity y))))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons
	  (*j (- x1 x2))
	  (lambda ((sensitivity y))
	   (sensitize
	    (cons -
		  (cons (unsensitize (sensitivity y))
			(- (real 0) (unsensitize (sensitivity y))))))))))))
 (define-primitive-procedure '*
  (binary-real * "*")
  (lambda (v) (c:builtin-name "times" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (* x1 x2)
	     (perturb (+ (* x2 x1-unperturbed) (* x1 x2-unperturbed))))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (* x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize
	     (cons *
		   (cons (* x2 (unsensitize (sensitivity y)))
			 (* x1 (unsensitize (sensitivity y)))))))))))
 (define-primitive-procedure '/
  (binary-real divide "/")
  (lambda (v) (c:builtin-name "divide" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (/ x1 x2)
	     (perturb (/ (- (* x2 x1-unperturbed) (* x1 x2-unperturbed))
			 (* x2 x2))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (/ x1 x2))
	       (lambda ((sensitivity y))
		(sensitize
		 (cons /
		       (cons (/ (unsensitize (sensitivity y)) x2)
			     (- 0.0
				(/ (* x1 (unsensitize (sensitivity y)))
				   (* x2 x2))))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (/ x1 x2))
	       (lambda ((sensitivity y))
		(sensitize
		 (cons /
		       (cons (/ (unsensitize (sensitivity y)) x2)
			     (- (real 0)
				(/ (* x1 (unsensitize (sensitivity y)))
				   (* x2 x2))))))))))))
 (define-primitive-procedure 'sqrt
  (unary-real sqrt "sqrt")
  (lambda (v) "sqrt")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle
      (sqrt x)
      (perturb (/ (unperturb (perturbation x)) (+ (sqrt x) (sqrt x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (sqrt x))
      (lambda ((sensitivity y))
       (sensitize
	(cons sqrt
	      (/ (unsensitize (sensitivity y)) (+ (sqrt x) (sqrt x))))))))))
 (define-primitive-procedure 'exp
  (unary-real exp "exp")
  (lambda (v) "exp")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (exp x) (perturb (* (exp x) (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (exp x))
      (lambda ((sensitivity y))
       (sensitize (cons exp (* (exp x) (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'log
  (unary-real log "log")
  (lambda (v) "log")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (log x) (perturb (/ (unperturb (perturbation x)) x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (log x))
	   (lambda ((sensitivity y))
	    (sensitize (cons log (/ (unsensitize (sensitivity y)) x))))))))
 (define-primitive-procedure 'sin
  (unary-real sin "sin")
  (lambda (v) "sin")
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (sin x) (perturb (* (cos x) (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (sin x))
      (lambda ((sensitivity y))
       (sensitize (cons sin (* (cos x) (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'cos
  (unary-real cos "cos")
  (lambda (v) "cos")
  (if *imprecise-inexacts?*
      '(lambda ((forward x))
	(let ((x (primal (forward x)))
	      ((perturbation x) (tangent (forward x))))
	 (bundle
	  (cos x) (perturb (- 0.0 (* (sin x) (unperturb (perturbation x))))))))
      '(lambda ((forward x))
	(let ((x (primal (forward x)))
	      ((perturbation x) (tangent (forward x))))
	 (bundle
	  (cos x)
	  (perturb (- (real 0) (* (sin x) (unperturb (perturbation x)))))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons
	  (*j (cos x))
	  (lambda ((sensitivity y))
	   (sensitize
	    (cons cos (- 0.0 (* (sin x) (unsensitize (sensitivity y))))))))))
      '(lambda ((reverse x))
	(let ((x (*j-inverse (reverse x))))
	 (cons
	  (*j (cos x))
	  (lambda ((sensitivity y))
	   (sensitize
	    (cons
	     cos
	     (- (real 0) (* (sin x) (unsensitize (sensitivity y))))))))))))
 (define-primitive-procedure 'atan
  (binary-real atan "atan")
  (lambda (v) (c:builtin-name "atantwo" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (atan x2 x1)
	     (perturb (/ (- (* x1 x2-unperturbed) (* x2 x1-unperturbed))
			 (+ (* x1 x1) (* x2 x2)))))))
  (if *imprecise-inexacts?*
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(sensitize
		 (cons atan
		       (cons (- 0.0
				(/ (* x2 (unsensitize (sensitivity y)))
				   (+ (* x1 x1) (* x2 x2))))
			     (/ (* x1 (unsensitize (sensitivity y)))
				(+ (* x1 x1) (* x2 x2))))))))))
      '(lambda ((reverse x))
	(let (((cons x1 x2) (*j-inverse (reverse x))))
	 (cons (*j (atan x2 x1))
	       (lambda ((sensitivity y))
		(sensitize
		 (cons atan
		       (cons (- (real 0)
				(/ (* x2 (unsensitize (sensitivity y)))
				   (+ (* x1 x1) (* x2 x2))))
			     (/ (* x1 (unsensitize (sensitivity y)))
				(+ (* x1 x1) (* x2 x2))))))))))))
 (define-primitive-procedure '=
  (binary-real-predicate = "=")
  (lambda (v) (c:builtin-name "eq" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons = (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '<
  (binary-real-predicate < "<")
  (lambda (v) (c:builtin-name "lt" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (< x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (< x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons < (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '>
  (binary-real-predicate > ">")
  (lambda (v) (c:builtin-name "gt" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (> x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (> x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons > (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '<=
  (binary-real-predicate <= "<=")
  (lambda (v) (c:builtin-name "le" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (<= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (<= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons <= (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '>=
  (binary-real-predicate >= ">=")
  (lambda (v) (c:builtin-name "ge" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (>= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (>= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons >= (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure 'zero?
  (unary-real-predicate zero? "zero?")
  (lambda (v) (c:builtin-name "iszero" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (zero? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x))
	   (lambda ((sensitivity y)) (sensitize (cons zero? (zero x))))))))
 (define-primitive-procedure 'positive?
  (unary-real-predicate positive? "positive?")
  (lambda (v) (c:builtin-name "positive" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (positive? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (positive? x))
	   (lambda ((sensitivity y)) (sensitize (cons positive? (zero x))))))))
 (define-primitive-procedure 'negative?
  (unary-real-predicate negative? "negative?")
  (lambda (v) (c:builtin-name "negative" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (negative? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (negative? x))
	   (lambda ((sensitivity y)) (sensitize (cons negative? (zero x))))))))
 (define-primitive-procedure 'null?
  (unary-predicate vlad-empty-list? "null?")
  (lambda (v) (c:builtin-name "null" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (null? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x))
	   (lambda ((sensitivity y)) (sensitize (cons null? (zero x))))))))
 (define-primitive-procedure 'boolean?
  (unary-predicate vlad-boolean? "boolean?")
  (lambda (v) (c:builtin-name "boolean" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (boolean? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x))
	   (lambda ((sensitivity y)) (sensitize (cons boolean? (zero x))))))))
 (define-primitive-procedure 'real?
  (unary-predicate vlad-real? "real?")
  (lambda (v) (c:builtin-name "is_real" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (real? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x))
	   (lambda ((sensitivity y)) (sensitize (cons real? (zero x))))))))
 (define-primitive-procedure 'pair?
  (unary-predicate vlad-pair? "pair?")
  (lambda (v) (c:builtin-name "pair" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (pair? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x))
	   (lambda ((sensitivity y)) (sensitize (cons pair? (zero x))))))))
 (define-primitive-procedure 'procedure?
  ;; needs work: This should probably return #f for any transformed procedure.
  (unary-predicate vlad-procedure? "procedure?")
  (lambda (v) (c:builtin-name "procedure" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (procedure? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (procedure? x))
      (lambda ((sensitivity y)) (sensitize (cons procedure? (zero x))))))))
 ;; The perturbation?, forward?, sensitivity? and reverse? primitives are not
 ;; referentially transparent and violate the forward-transformation rule for
 ;; functions that only rearrange data.
 (define-primitive-procedure 'perturbation?
  (unary-predicate perturbation-value? "perturbation?")
  (lambda (v) (c:builtin-name "perturbation" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (perturbation? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (perturbation? x))
      (lambda ((sensitivity y)) (sensitize (cons perturbation? (zero x))))))))
 (define-primitive-procedure 'forward?
  (unary-predicate forward-value? "forward?")
  (lambda (v) (c:builtin-name "forward" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (forward? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x))
	   (lambda ((sensitivity y)) (sensitize (cons forward? (zero x))))))))
 (define-primitive-procedure 'sensitivity?
  (unary-predicate sensitivity-value? "sensitivity?")
  (lambda (v) (c:builtin-name "sensitivity" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (sensitivity? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (sensitivity? x))
      (lambda ((sensitivity y)) (sensitize (cons sensitivity? (zero x))))))))
 (define-primitive-procedure 'reverse?
  (unary-predicate reverse-value? "reverse?")
  (lambda (v) (c:builtin-name "reverse" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (j* (reverse? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (reverse? x))
	   (lambda ((sensitivity y)) (sensitize (cons reverse? (zero x))))))))
 (define-primitive-procedure 'if-procedure
  (ternary (lambda (v1 v2 v3)
	    (if *abstract?*
		(if (vlad-false? v1)
		    (abstract-apply v3 (vlad-empty-list))
		    (abstract-apply v2 (vlad-empty-list)))
		(if (vlad-false? v1)
		    (concrete-apply v3 (vlad-empty-list))
		    (concrete-apply v2 (vlad-empty-list)))))
	   "if-procedure")
  (lambda (v) (c:builtin-name "if_procedure" v))
  '(lambda ((forward x))
    (let (((cons* x1 x2 x3) (primal (forward x)))
	  ((cons* x1-unperturbed x2-unperturbed x3-unperturbed)
	   (unperturb (tangent (forward x))))
	  (j* (lambda (x) (bundle x (perturb (zero x))))))
     (if x1
	 ((bundle x2 (perturb x2-unperturbed)) (j* '()))
	 ((bundle x3 (perturb x3-unperturbed)) (j* '())))))
  '(lambda ((reverse x))
    (let (((cons* x1 x2 x3) (*j-inverse (reverse x))))
     (if x1
	 (let (((cons (reverse y) y-backpropagator) ((*j x2) (*j '()))))
	  (cons
	   (reverse y)
	   (lambda ((sensitivity y))
	    (sensitize
	     (cons
	      if-procedure
	      (cons*
	       (zero x1)
	       ;; (sensitize
	       ;;  (cdr (unsensitize (y-backpropagator (sensitivity y)))))
	       ;; should be the sensitivity to the ignored '() argument of x2
	       ((lambda ((cons x y)) x)
		(unsensitize (y-backpropagator (sensitivity y))))
	       (zero x3)))))))
	 (let (((cons (reverse y) y-backpropagator) ((*j x3) (*j '()))))
	  (cons
	   (reverse y)
	   (lambda ((sensitivity y))
	    (sensitize
	     (cons
	      if-procedure
	      (cons*
	       (zero x1)
	       (zero x2)
	       ;; (sensitize
	       ;;  (cdr (unsensitize (y-backpropagator (sensitivity y)))))
	       ;; should be the sensitivity to the ignored '() argument of x3
	       ((lambda ((cons x y)) x)
		(unsensitize (y-backpropagator (sensitivity y))))))))))))))
 (define-primitive-procedure 'read-real
  (unary read-real "read-real")
  (lambda (v) "read_real")
  (if *imprecise-inexacts?*
      `(lambda (',(j* (vlad-empty-list)))
	(bundle (read-real) (perturb 0.0)))
      `(lambda (',(j* (vlad-empty-list)))
	(bundle (read-real) (perturb (real 0)))))
  `(lambda (',(*j (vlad-empty-list)))
    (cons (*j (read-real))
	  (lambda ((sensitivity y)) (sensitize (cons read-real '()))))))
 (define-primitive-procedure 'real
  (unary-real (lambda (v) (if *abstract?* (abstract-real) v)) "real")
  (lambda (v) (c:builtin-name "real" v))
  ;; These widen the tangent and cotangent as well. Nothing requires us to do
  ;; so. It is just a design decision.
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (real x) (perturb (real (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real x))
	   (lambda ((sensitivity y))
	    (sensitize (cons real (real (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'write
  (unary (lambda (v)
	  (unless *abstract?* ((if *pp?* pp write) (externalize v)) (newline))
	  v)
	 "write")
  (lambda (v) (c:builtin-name "write" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     ;; The unperturb composed with perturb could be optimized away.
     (bundle (write x) (perturb (unperturb (perturbation x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write x))
	   (lambda ((sensitivity y))
	    (sensitize (cons write (unsensitize (sensitivity y)))))))))
 (define-primitive-procedure 'zero
  (unary-ad zero "zero")
  (lambda (v) (c:builtin-name "zero" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     ;; The unperturb-perturb could be optimized away.
     (bundle (zero x) (perturb (zero (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x))
	   (lambda ((sensitivity y)) (sensitize (cons zero (zero x))))))))
 (define-primitive-procedure 'perturb
  (unary-ad perturb "perturb")
  (lambda (v) (c:builtin-name "perturb" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     ;; The unperturb composed with perturb could be optimized away.
     (bundle (perturb x) (perturb (perturb (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (perturb x))
      ;; The argument must be called y-perturbation so as not to confuse the
      ;; tags.
      (lambda ((sensitivity y-perturbation))
       (sensitize
	(cons perturb
	      (unperturb (unsensitize (sensitivity y-perturbation))))))))))
 (define-primitive-procedure 'unperturb
  (unary-ad unperturb "unperturb")
  (lambda (v) (c:builtin-name "unperturb" v))
  ;; The argument must be called x-perturbation so as not to confuse the tags.
  '(lambda ((forward x-perturbation))
    (let ((x-perturbation (primal (forward x-perturbation)))
	  ((perturbation x-perturbation) (tangent (forward x-perturbation))))
     (bundle (unperturb x-perturbation)
	     ;; The unperturb composed with perturb could be optimized away.
	     (perturb (unperturb (unperturb (perturbation x-perturbation)))))))
  ;; The argument must be called x-perturbation so as not to confuse the tags.
  '(lambda ((reverse x-perturbation))
    (let ((x-perturbation (*j-inverse (reverse x-perturbation))))
     (cons (*j (unperturb x-perturbation))
	   (lambda ((sensitivity y))
	    (sensitize
	     (cons unperturb (perturb (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'primal
  (unary-ad primal "primal")
  (lambda (v) (c:builtin-name "primal" v))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  ((perturbation x-forward) (tangent (forward x-forward))))
     (bundle (primal x-forward)
	     (perturb (primal (unperturb (perturbation x-forward)))))))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward))))
     (cons (*j (primal x-forward))
	   (lambda ((sensitivity y))
	    (sensitize
	     (cons primal
		   ;; needs work: I'm not sure that this is the inverse of
		   ;;             primal.
		   (bundle (unsensitize (sensitivity y))
			   (zero (tangent x-forward))))))))))
 (define-primitive-procedure 'tangent
  (unary-ad tangent "tangent")
  (lambda (v) (c:builtin-name "tangent" v))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((forward x-forward))
    (let ((x-forward (primal (forward x-forward)))
	  ((perturbation x-forward) (tangent (forward x-forward))))
     (bundle (tangent x-forward)
	     (perturb (tangent (unperturb (perturbation x-forward)))))))
  ;; The argument must be called x-forward so as not to confuse the tags.
  '(lambda ((reverse x-forward))
    (let ((x-forward (*j-inverse (reverse x-forward))))
     (cons (*j (tangent x-forward))
	   ;; The argument must be called y-perturbation so as not to confuse
	   ;; the tags.
	   (lambda ((sensitivity y-perturbation))
	    (sensitize
	     (cons tangent
		   ;; needs work: I'm not sure that this is the inverse of
		   ;;             tangent.
		   (bundle (zero (primal x-forward))
			   (unsensitize (sensitivity y-perturbation))))))))))
 (define-primitive-procedure 'bundle
  (binary-ad bundle "bundle")
  (lambda (v) (c:builtin-name "bundle" v))
  '(lambda ((forward x))
    (let (((cons x1 (perturbation x2)) (primal (forward x)))
	  ((cons x1-unperturbed (perturbation x2-unperturbed))
	   (unperturb (tangent (forward x)))))
     (bundle
      ;; The unperturb composed with perturb could be optimized away.
      (bundle x1 (perturb (unperturb (perturbation x2))))
      (perturb
       (bundle x1-unperturbed
	       ;; The unperturb composed with perturb could be optimized away.
	       (perturb (unperturb (perturbation x2-unperturbed))))))))
  '(lambda ((reverse x))
    (let (((cons x1 (perturbation x2)) (*j-inverse (reverse x))))
     (cons
      (*j (bundle x1 (perturbation x2)))
      ;; The argument must be called y-forward so as not to confuse the tags.
      (lambda ((sensitivity y-forward))
       (sensitize
	(cons bundle
	      (cons (primal (unsensitize (sensitivity y-forward)))
		    (tangent (unsensitize (sensitivity y-forward)))))))))))
 (define-primitive-procedure 'sensitize
  (unary-ad sensitize "sensitize")
  (lambda (v) (c:builtin-name "sensitize" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle
      (sensitize x) (perturb (sensitize (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (sensitize x))
      ;; The argument must be called y-sensitivity so as not to confuse the
      ;; tags.
      (lambda ((sensitivity y-sensitivity))
       (sensitize
	(cons sensitize
	      (unsensitize (unsensitize (sensitivity y-sensitivity))))))))))
 (define-primitive-procedure 'unsensitize
  (unary-ad unsensitize "unsensitize")
  (lambda (v) (c:builtin-name "unsensitize" v))
  ;; The argument must be called x-sensitivity so as not to confuse the tags.
  '(lambda ((forward x-sensitivity))
    (let ((x-sensitivity (primal (forward x-sensitivity)))
	  ((perturbation x-sensitivity) (tangent (forward x-sensitivity))))
     (bundle
      (unsensitize x-sensitivity)
      (perturb (unsensitize (unperturb (perturbation x-sensitivity)))))))
  ;; The argument must be called x-sensitivity so as not to confuse the tags.
  '(lambda ((reverse x-sensitivity))
    (let ((x-sensitivity (*j-inverse (reverse x-sensitivity))))
     (cons
      (*j (unsensitize x-sensitivity))
      (lambda ((sensitivity y))
       (sensitize
	;; The unsensitize composed with sensitize could be optimized away.
	(cons unsensitize (sensitize (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'plus
  (binary-ad plus "plus")
  (lambda (v) (c:builtin-name "plus" v))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (plus x1 x2) (perturb (plus x1-unperturbed x2-unperturbed)))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (plus x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons plus
			     (cons (unsensitize (sensitivity y))
				   (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure '*j
  (unary-ad *j "*j")
  (lambda (v) (c:builtin-name "starj" v))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (*j x) (perturb (*j (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    ;; The *j-inverse composed with *j could be optimized away.
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (*j x))
	   ;; The argument must be called y-reverse so as not to confuse the
	   ;; tags.
	   (lambda ((sensitivity y-reverse))
	    (sensitize
	     (cons *j (*j-inverse (unsensitize (sensitivity y-reverse))))))))))
 (define-primitive-procedure '*j-inverse
  (unary-ad *j-inverse "*j-inverse")
  (lambda (v) (c:builtin-name "starj_inverse" v))
  ;; The argument must be called x-reverse so as not to confuse the tags.
  '(lambda ((forward x-reverse))
    (let ((x-reverse (primal (forward x-reverse)))
	  ((perturbation x-reverse) (tangent (forward x-reverse))))
     (bundle (*j-inverse x-reverse)
	     (perturb (*j-inverse (unperturb (perturbation x-reverse)))))))
  ;; The argument must be called x-reverse so as not to confuse the tags.
  '(lambda ((reverse x-reverse))
    (let ((x-reverse (*j-inverse (reverse x-reverse))))
     ;; The *j-inverse composed with *j could be optimized away.
     (cons
      (*j (*j-inverse x-reverse))
      (lambda ((sensitivity y))
       (sensitize (cons *j-inverse (*j (unsensitize (sensitivity y))))))))))
 (initialize-forwards-and-reverses!))

;;; Commands

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
