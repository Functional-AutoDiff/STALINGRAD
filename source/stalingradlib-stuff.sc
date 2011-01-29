(MODULE STALINGRADLIB-STUFF)
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004, 2005, 2006, 2007, 2008, 2009, and 2010 Purdue University.
;;; All rights reserved.

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
;;;    http://engineering.purdue.edu/~qobi
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
(include "stalingradlib-stuff.sch")

;;; needs work
;;;  1. zero, perturb, unperturb, primal, tangent, bundle, sensitize,
;;;     unsensitize, plus, *j, and *j-inverse should be lazy.
;;;  2. Really need to get rid of anonymous gensyms to get read/write
;;;     invariance.
;;;  3. unary -
;;;  4. begin, case, delay, do, quasiquote, unquote, unquote-splicing,
;;;     internal defines
;;;  5. chars, ports, eof object, symbols, continuations, strings, vectors

;;; Key
;;;  e: concrete or abstract expression
;;;  p: concrete or abstract parameter
;;;  x: concrete or abstract variable
;;;  b: concrete syntactic, variable, or value binding
;;;  v: concrete or abstract value
;;;  d: definition
;;;  record, gensym, result, free-variables, message, callee, argument,
;;;  procedure

;;; Macros

(define-macro assert
 (lambda (form expander)
  (unless (= (length form) 2)
   (error 'assert "Wrong number of arguments: ~s" form))
  (expander `(assert-internal
	      (lambda () ,(second form)) ,(format #f "~s" (second form)))
	    expander)))

(define-macro trace-it
 (lambda (form expander)
  (unless (= (length form) 3)
   (error 'assert "Wrong number of arguments: ~s" form))
  (expander `(trace-it-internal (lambda () ,(second form)) ,(third form))
	    expander)))

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
   (if #f				;debugging
       `(time-bucket ,(second form) (lambda () ,(third form)))
       (third form))
   expander)))

;;; Structures

(define-structure variable
 name
 c:index
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
 ;; We don't do dereferenced-expression-eqv? when accessing the next two slots.
 ;; I'm not sure whether we have to.
 parents
 environment-bindings
 free-variables
 parameter
 body
 body-free-variable-indices
 body-free-variable-indices1
 body-free-variable-indices2)

;;; We can determine that a constant expression has been transformed by looking
;;; at its value. (Only because we don't allow transformed constants in the
;;; source program.) We can determine that a variable access expression is
;;; transformed by looking at the variable tags. We can determine that a lambda
;;; expression is transformed by looking at the parameter tags. We can
;;; determine that a letrec expression is transformed by looking at the
;;; parameter tags of some lambda expression. And we can determine that a cons
;;; expression is transformed by looking at its tag. We need to have such tags
;;; to know to do a transformed cons. (This is only because cons is syntax, not
;;; a primitive procedure.) But we don't have a way to determine that an
;;; application is transformed.

(define-structure application
 parents
 environment-bindings
 enqueue?
 free-variables
 callee
 argument
 callee-indices
 argument-indices
 let-free-variable-indices)

(define-structure letrec-expression
 parents
 environment-bindings
 enqueue?
 free-variables
 procedure-variables
 lambda-expressions
 body
 indices
 body-free-variable-procedure-variable?
 body-free-variable-indices)

(define-structure cons-expression
 parents
 environment-bindings
 enqueue?
 free-variables
 tags
 car
 cdr
 car-indices
 cdr-indices)

(define-structure variable-binding variable expression)

(define-structure parameter-binding parameter expression)

(define-structure value-binding variable value)

(define-structure alpha-binding variable1 variable2)

(define-structure primitive-procedure
 symbol
 name
 c:name
 concrete
 abstract
 alias
 all-instances!
 generate
 forward
 reverse
 meter
 instances)

;;; debugging: might be able to remove {zero,perturb,unperturb,primal,tangent,
;;             bundle-sensitize,unsensitize,*j,*j-inverse}-cache

(define-structure nonrecursive-closure
 values
 lambda-expression
 body-free-variable-indices
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 unperturb-cache
 primal-cache
 tangent-cache
 sensitize-cache
 unsensitize-cache
 *j-cache
 *j-inverse-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 function-instances
 widener-instances
 flag?)

(define-structure recursive-closure
 values
 procedure-variables			;vector
 lambda-expressions			;vector
 index
 body-free-variable-indices
 body-free-variable-procedure-variable-indices
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 unperturb-cache
 primal-cache
 tangent-cache
 sensitize-cache
 unsensitize-cache
 *j-cache
 *j-inverse-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 function-instances
 widener-instances
 flag?)

(define-structure perturbation-tagged-value
 primal
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 sensitize-cache
 *j-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure bundle
 primal
 tangent
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 sensitize-cache
 *j-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure sensitivity-tagged-value
 primal
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 sensitize-cache
 *j-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure reverse-tagged-value
 primal
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 sensitize-cache
 *j-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure vlad-pair
 car
 cdr
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 bundle-cache
 sensitize-cache
 plus-cache
 *j-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure union
 values
 canonize-cache
 intern-cache
 zero-cache
 perturb-cache
 unperturb-cache
 primal-cache
 tangent-cache
 bundle-cache
 sensitize-cache
 unsensitize-cache
 plus-cache
 *j-cache
 *j-inverse-cache
 widen
 c:index
 boxed?
 void?
 alias
 new-aliases
 equivalent-slot-indices
 widener-instances
 flag?)

(define-structure environment-binding values value)

(define-structure function-instance
 v1
 v2
 c:index
 number-of-call-sites
 inline?
 input-alias
 new-input-aliases
 output-alias
 il
 flag?)

(define-structure widener-instance
 v1
 v2
 c:index
 number-of-call-sites
 inline?
 input-alias
 new-input-aliases
 output-alias
 il
 flag?)

(define-structure primitive-procedure-instance
 symbol
 v
 number-of-call-sites
 inline?
 input-alias
 new-input-aliases
 output-alias
 il
 flag?)

(define-structure il:t index)

(define-structure il:a instance index)

(define-structure il:r instance index)

(define-structure il:empty v)

(define-structure il:tag u v)

(define-structure il:constant number)

;;; il1 should never be void
;;; il2 can be void
(define-structure il:let v x il1 il2)

;;; il should never be void
;;; members of ils can be void
(define-structure il:dispatch v0 v il ils)

(define-structure il:panic string)

;;; il should never be void
(define-structure il:closure-ref v il x)

;;; il should never be void
(define-structure il:perturbation-tagged-value-primal v il)

;;; il should never be void
(define-structure il:bundle-primal v il)

;;; il should never be void
(define-structure il:bundle-tangent v il)

;;; il should never be void
(define-structure il:sensitivity-tagged-value-primal v il)

;;; il should never be void
(define-structure il:reverse-tagged-value-primal v il)

;;; il should never be void
(define-structure il:car v il)

;;; il should never be void
(define-structure il:cdr v il)

;;; il should never be void
(define-structure il:union-ref v u il)

;;; members of ils should never be void
(define-structure il:construct* v ils)

;;; il should never be void
(define-structure il:construct-union u v il)

(define-structure il:construct-union0 u v)

;;; members of ils should never be void
(define-structure il:call* instance ils)

;;; il1 and il2 should never be void
(define-structure il:binary il1 string il2)

;;; il1 and il2 should never be void
(define-structure il:binary-boolean il1 string il2)

;;; il1 should never be void
;;; il2 can be void
(define-structure il:mv-let vs xs il1 il2)

;;; members of ils should never be void
(define-structure il:values* v ils)

;;; Variables

(define *time-buckets* #f)		; belongs in QobiScheme

(define *gensym* 0)

(define *alpha* 0)

(define *value-bindings* '())

(define *stack* '())

(define *trace-level* 0)

(define *error* #f)

(define *error?* #f)

(define *mode* 'concrete)

(define *with-concrete?* #f)

(define *variables* '())

(define *backpropagator-variables* (vector #f))

(define *anf-variables* (vector #f))

(define *expressions* '())

(define *queue* '())

(define *frozen?* #f)			;means cannot intern

;;; Can better index the following eight.

;;; We used to index closures on their lambda expression. But that caused bugs
;;; due to dereferenced-expression-eqv?.

(define *nonrecursive-closures* '())

(define *recursive-closures* '())

(define *perturbation-tagged-values* '())

(define *bundles* '())

(define *sensitivity-tagged-values* '())

(define *reverse-tagged-values* '())

(define *vlad-pairs* '())

(define *unions* '())

(define *empty-abstract-value* #f)

(define *abstract-boolean* #f)

(define *function-instances* '())

(define *widener-instances* '())

(define *scalar-widener-instances* '())

(define *vs* '())

(define *flagged-abstract-values* '())

;;; Can better index the following.

(define *c:indices* '())

(define *il* #f)

(define *il:t* 0)

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

(define *pair-width-limit* #f)

(define *closure-depth-limit* #f)

(define *backpropagator-depth-limit* #f)

(define *perturbation-tagged-value-depth-limit* #f)

(define *bundle-depth-limit* #f)

(define *sensitivity-tagged-value-depth-limit* #f)

(define *reverse-tagged-value-depth-limit* #f)

(define *pair-depth-limit* #f)

(define *order-limit* #f)

(define *widen-lists?* #f)

(define *almost-union-free?* #f)

(define *canonized?* #f)

(define *interned?* #f)

(define *expensive-checks?* #f)

(define *alias?* #f)

(define *union* "struct")		;not exposed

(define *inline?* #f)

(define *number-of-call-sites* #f)

(define *anf-convert?* #f)

(define *sra?* #f)

(define *il?* #f)

(define *abstract-values?* #f)		;not exposed

(define *profile?* #f)

(define *il:multiply-out-dispatches-cost-limit* #f)

;;; Procedures

;;; General

(define (profile format-string thunk)
 (if *profile?* (time format-string thunk) (thunk)))

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

(define (rest* l k) (if (zero? k) l (rest* (rest l) (- k 1))))

(define (maximal-elements <=? s)
 ;; belongs in QobiScheme
 (remove-if
  (lambda (e)
   (some (lambda (e-prime) (and (not (eq? e-prime e)) (<=? e e-prime))) s))
  s))

(define (cross-product f l1 l2)
 ;; belongs in QobiScheme
 (map-reduce append '() (lambda (x1) (map (lambda (x2) (f x1 x2)) l2)) l1))

(define (with-concrete thunk)
 ;; needs work: To disable errors.
 (let ((mode *mode*) (with-concrete? *with-concrete?*))
  (set! *mode* 'concrete)
  (set! *with-concrete?* #t)
  (let ((result (thunk)))
   (set! *mode* mode)
   (set! *with-concrete?* with-concrete?)
   result)))

(define (with-abstract thunk)
 (let ((mode *mode*) (canonized? *canonized?*) (interned? *interned?*))
  (set! *mode* 'abstract)
  (set! *canonized?* #t)
  (set! *interned?* #t)
  (let ((result (thunk)))
   (set! *mode* mode)
   (set! *canonized?* canonized?)
   (set! *interned?* interned?)
   result)))

(define (without-warnings thunk)
 (let ((warnings? *warnings?*))
  (set! *warnings?* #f)
  (let ((result (thunk)))
   (set! *warnings?* warnings?)
   result)))

(define (with-safe-externalize thunk)
 (let ((unabbreviate-transformed? *unabbreviate-transformed?*)
       (unabbreviate-nonrecursive-closures?
	*unabbreviate-nonrecursive-closures?*)
       (unabbreviate-recursive-closures?
	*unabbreviate-recursive-closures?*))
  (set! *unabbreviate-transformed?* #t)
  (set! *unabbreviate-nonrecursive-closures?* #f)
  (set! *unabbreviate-recursive-closures?* #f)
  (let ((result (thunk)))
   (set! *unabbreviate-transformed?*  unabbreviate-transformed?)
   (set! *unabbreviate-nonrecursive-closures?*
	 unabbreviate-nonrecursive-closures?)
   (set! *unabbreviate-recursive-closures?* unabbreviate-recursive-closures?)
   result)))

;;; debugging: might be able to eliminate some cps variants

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

(define (map-cps-non-cs p l k)
 (let loop ((l l) (n '()))
  (if (null? l)
      (k (reverse n))
      (p (first l) (lambda (r) (loop (rest l) (cons r n)))))))

(define (map2-cps p l1 l2 cs k)
 (let loop ((l1 l1) (l2 l2) (cs cs) (n '()))
  (if (null? l1)
      (k (reverse n) cs)
      (p (first l1)
	 (first l2)
	 cs
	 (lambda (r cs) (loop (rest l1) (rest l2) cs (cons r n)))))))

(define (map2-cps-non-cs p l1 l2 k)
 (let loop ((l1 l1) (l2 l2) (n '()))
  (if (null? l1)
      (k (reverse n))
      (p (first l1)
	 (first l2)
	 (lambda (r) (loop (rest l1) (rest l2) (cons r n)))))))

(define (reduce-cps p l i cs k)
 (let loop ((l l) (cs cs) (i i))
  (if (null? l)
      (k i cs)
      (p i (first l) cs (lambda (i cs) (loop (rest l) cs i))))))

;;; Error handing

(define (internal-error . arguments)
 (if (null? arguments)
     (panic "Internal error")
     (apply panic
	    (format #f "Internal error: ~a" (first arguments))
	    (rest arguments))))

(define (assert-internal thunk string)
 (when *assert?*
  (unless (thunk) (internal-error (format #f "assert: ~a" string)))))

(define (trace-it-internal thunk string)
 (format #t "Entering ~a~%" string)
 (let ((result (thunk)))
  (format #t "Leaving ~a~%" string)
  result))

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
 (assert (eq? *mode* 'abstract))
 (when *warnings?*
  (without-warnings
   (lambda ()
    (for-each (lambda (v)
	       ((if *pp?* pp write) (externalize v) stderr-port)
	       (newline stderr-port))
	      vs)))
  (display "Warning: " stderr-port)
  (display message stderr-port)
  (newline stderr-port))
 (empty-abstract-value))

(define (run-time-warning message . vs)
 (assert (eq? *mode* 'concrete))
 (when *warnings?*
  (when *error?*
   (display "Nested warning: " stderr-port)
   (display message stderr-port)
   (newline stderr-port)
   (display "Error: " stderr-port)
   (display *error* stderr-port)
   (newline stderr-port)
   (exit -1))
  (set! *error* message)
  (set! *error?* #t)
  (without-warnings
   (lambda ()
    (unless *with-concrete?*
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
	      vs)))
  (display "Warning: " stderr-port)
  (display message stderr-port)
  (newline stderr-port)
  (set! *error?* #f)))

(define (run-time-error message . vs)
 (assert (eq? *mode* 'concrete))
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
 (without-warnings
  (lambda ()
   (unless *with-concrete?*
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
	     vs)))
 (display "Error: " stderr-port)
 (display message stderr-port)
 (newline stderr-port)
 (exit -1))

(define (ad-warning message . vs)
 (case *mode*
  ((concrete) (apply run-time-warning message vs))
  ((abstract) (apply compile-time-warning message vs))
  (else (internal-error))))

(define (ad-error message . vs)
 (case *mode*
  ((concrete) (apply run-time-error (format #f message "is not") vs))
  ((abstract)
   (apply compile-time-warning (format #f message "might not be") vs))
  (else (internal-error))))

;;; Tags

(define (empty-tags) '())

(define (empty-tags? tags) (null? tags))

(define (add-tag tag tags) (cons tag tags))

(define (tagged? tag tags)
 (and (not (empty-tags? tags)) (eq? (first tags) tag)))

(define (remove-tag tag tags)
 (assert (tagged? tag tags))
 (rest tags))

(define (prefix-tags? tags1 tags2)
 (or (empty-tags? tags1)
     (and (not (empty-tags? tags1))
	  (not (empty-tags? tags2))
	  (eq? (first tags1) (first tags2))
	  (prefix-tags? (rest tags1) (rest tags2)))))

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

(define (variable-order x)
 (max (if (variable-unperturbationify x)
	  (+ (variable-order (variable-unperturbationify x)) 1)
	  0)
      (if (variable-unforwardify x)
	  (+ (variable-order (variable-unforwardify x)) 1)
	  0)
      (if (variable-unsensitivityify x)
	  (+ (variable-order (variable-unsensitivityify x)) 1)
	  0)
      (if (variable-unreverseify x)
	  (+ (variable-order (variable-unreverseify x)) 1)
	  0)))

(define (perturbationify x)
 (or (variable-perturbationify x)
     (let ((x0 (new-variable `(perturbation ,(variable-name x)))))
      (when (and *order-limit* (>= (variable-order x) *order-limit*))
       (compile-time-error "Order limit exceeded"))
      (set-variable-perturbationify! x x0)
      (set-variable-unperturbationify! x0 x)
      x0)))

(define (forwardify x)
 (or (variable-forwardify x)
     (let ((x0 (new-variable `(forward ,(variable-name x)))))
      (when (and *order-limit* (>= (variable-order x) *order-limit*))
       (compile-time-error "Order limit exceeded"))
      (set-variable-forwardify! x x0)
      (set-variable-unforwardify! x0 x)
      x0)))

(define (sensitivityify x)
 (or (variable-sensitivityify x)
     (let ((x0 (new-variable `(sensitivity ,(variable-name x)))))
      (when (and *order-limit* (>= (variable-order x) *order-limit*))
       (compile-time-error "Order limit exceeded"))
      (set-variable-sensitivityify! x x0)
      (set-variable-unsensitivityify! x0 x)
      x0)))

(define (reverseify x)
 (or (variable-reverseify x)
     (let ((x0 (new-variable `(reverse ,(variable-name x)))))
      (when (and *order-limit* (>= (variable-order x) *order-limit*))
       (compile-time-error "Order limit exceeded"))
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
 (assert (not *frozen?*))
 (let ((e0 (make-constant-expression '() '() value)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (allocate-variable-access-expression variable)
 (assert (variable? variable))
 (make-variable-access-expression '() '() variable))

(define (new-variable-access-expression variable)
 (assert (and (variable? variable) (not *frozen?*)))
 (let ((e0 (make-variable-access-expression '() '() variable)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-lambda-expression p e)
 (assert (and (not (duplicatesp? variable=? (parameter-variables p)))
	      (not *frozen?*)))
 (let* ((xs (sort-variables
	     (set-differencep
	      variable=? (free-variables e) (parameter-variables p))))
	(e0 (make-lambda-expression
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
	     xs
	     p
	     e
	     (map (lambda (x) (positionp variable=? x xs)) (free-variables e))
	     'unfilled
	     'unfilled)))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-application e1 e2)
 (assert (not *frozen?*))
 (let* ((xs (sort-variables
	     (union-variables (free-variables e1) (free-variables e2))))
	(e0 (make-application
	     '()
	     '()
	     #f
	     xs
	     e1
	     e2
	     (map (lambda (x) (positionp variable=? x xs))
		  (free-variables e1))
	     (map (lambda (x) (positionp variable=? x xs))
		  (free-variables e2))
	     (and (lambda-expression? e1)
		  (map (lambda (x) (positionp variable=? x xs))
		       (free-variables (lambda-expression-body e1)))))))
  (set! *expressions* (cons e0 *expressions*))
  e0))

(define (new-letrec-expression xs es e)
 (assert
  (and (= (length xs) (length es)) (every variable? xs) (not *frozen?*)))
 (if (null? xs)
     e
     (let* ((xs0 (sort-variables
		  (set-differencep
		   variable=?
		   (union-variables
		    (map-reduce union-variables '() free-variables es)
		    (free-variables e))
		   xs)))
	    (xs1 (recursive-closure-free-variables xs es))
	    (e0 (make-letrec-expression
		 '()
		 '()
		 #f
		 xs0
		 xs
		 es
		 e
		 (map (lambda (x) (positionp variable=? x xs0)) xs1)
		 (map (lambda (x) (memp variable=? x xs)) (free-variables e))
		 (map (lambda (x)
		       (if (memp variable=? x xs)
			   (positionp variable=? x xs)
			   (positionp variable=? x xs0)))
		      (free-variables e)))))
      (for-each (lambda (e)
		 (cond
		  ((eq? (lambda-expression-body-free-variable-indices1 e)
			'unfilled)
		   (set-lambda-expression-body-free-variable-indices1!
		    e
		    (map (lambda (x) (positionp variable=? x xs1))
			 (free-variables (lambda-expression-body e))))
		   (set-lambda-expression-body-free-variable-indices2!
		    e
		    (map (lambda (x) (positionp variable=? x xs))
			 (free-variables (lambda-expression-body e)))))
		  (else
		   (assert (and
			    (equal?
			     (lambda-expression-body-free-variable-indices1 e)
			     (map (lambda (x) (positionp variable=? x xs1))
				  (free-variables (lambda-expression-body e))))
			    (equal?
			     (lambda-expression-body-free-variable-indices2 e)
			     (map (lambda (x) (positionp variable=? x xs))
				  (free-variables
				   (lambda-expression-body e)))))))))
		es)
      (set! *expressions* (cons e0 *expressions*))
      e0)))

(define (new-cons-expression tags e1 e2)
 (assert (not *frozen?*))
 (let* ((xs (sort-variables
	     (union-variables (free-variables e1) (free-variables e2))))
	(e0 (make-cons-expression
	     '()
	     '()
	     #f
	     xs
	     tags
	     e1
	     e2
	     (map (lambda (x) (positionp variable=? x xs))
		  (free-variables e1))
	     (map (lambda (x) (positionp variable=? x xs))
		  (free-variables e2)))))
  (set! *expressions* (cons e0 *expressions*))
  e0))

;;; Generic expression accessors and mutators

(define (parents e)
 ((cond ((constant-expression? e) constant-expression-parents)
	((variable-access-expression? e) variable-access-expression-parents)
	((lambda-expression? e) lambda-expression-parents)
	((application? e) application-parents)
	((letrec-expression? e) letrec-expression-parents)
	((cons-expression? e) cons-expression-parents)
	(else (internal-error)))
  e))

(define (set-parents! e es)
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

(define (environment-bindings e)
 ((cond ((constant-expression? e) constant-expression-environment-bindings)
	((variable-access-expression? e)
	 variable-access-expression-environment-bindings)
	((lambda-expression? e) lambda-expression-environment-bindings)
	((application? e) application-environment-bindings)
	((letrec-expression? e) letrec-expression-environment-bindings)
	((cons-expression? e) cons-expression-environment-bindings)
	(else (internal-error)))
  e))

(define (set-environment-bindings! e es)
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

(define (enqueue? e)
 ((cond ((application? e) application-enqueue?)
	((letrec-expression? e) letrec-expression-enqueue?)
	((cons-expression? e) cons-expression-enqueue?)
	(else (internal-error)))
  e))

(define (set-enqueue?! e es)
 ((cond ((application? e) set-application-enqueue?!)
	((letrec-expression? e) set-letrec-expression-enqueue?!)
	((cons-expression? e) set-cons-expression-enqueue?!)
	(else (internal-error)))
  e
  es))

(define (free-variables e)
 (cond ((constant-expression? e) '())
       ((variable-access-expression? e)
	(list (variable-access-expression-variable e)))
       ((lambda-expression? e) (lambda-expression-free-variables e))
       ((application? e) (application-free-variables e))
       ((letrec-expression? e) (letrec-expression-free-variables e))
       ((cons-expression? e) (cons-expression-free-variables e))
       (else (internal-error))))

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

;;; Expression equivalence

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

;;; Empty lists

(define (vlad-empty-list) '())

;;; This used to (assert (not (union? u)))
(define (vlad-empty-list? u) (null? u))

;;; Booleans

(define (vlad-true) #t)

(define (vlad-false) #f)

;;; This used to (assert (not (union? u)))
(define (vlad-true? u) (eq? u #t))

;;; This used to (assert (not (union? u)))
(define (vlad-false? u) (eq? u #f))

(define (vlad-boolean? u) (or (vlad-true? u) (vlad-false? u)))

;;; Reals

;;; This can't be real since there would be an ambiguity between an abstract
;;; real and the primitive real when externalizing.
(define (abstract-real) 'abstract-real)

;;; This used to (assert (not (union? u)))
(define (abstract-real? u) (eq? u 'abstract-real))

;;; This used to (assert (not (union? u)))
(define (vlad-real? u) (or (real? u) (abstract-real? u)))

;;; Closures

(define (allocate-nonrecursive-closure vs e)
 (make-nonrecursive-closure
  vs
  e
  (lambda-expression-body-free-variable-indices e)
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  'unfilled
  #f
  #f
  'unfilled
  '()
  '()
  #f))

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
       (or (eq? *mode* 'abstract)
	   (every
	    (lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	    (free-variables e)
	    vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and (eq? *mode* 'abstract)
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (free-variables e)
	    vs)))
     (empty-abstract-value)
     (allocate-nonrecursive-closure vs e)))

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
       (or (eq? *mode* 'abstract)
	   (every
	    (lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	    (free-variables e)
	    vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and (eq? *mode* 'abstract)
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (free-variables e)
	    vs)))
     (empty-abstract-value)
     (if *interned?*
	 (or (find-if (lambda (v0)
		       ;; The first condition is an optimization.
		       (and (= (length vs)
			       (length (get-nonrecursive-closure-values v0)))
			    (dereferenced-expression-eqv?
			     e (nonrecursive-closure-lambda-expression v0))
			    (abstract-environment=?
			     vs (get-nonrecursive-closure-values v0))))
		      *nonrecursive-closures*)
	     (let ((v0 (allocate-nonrecursive-closure vs e)))
	      (assert (not *frozen?*))
	      (set! *nonrecursive-closures* (cons v0 *nonrecursive-closures*))
	      (set-nonrecursive-closure-canonize-cache! v0 v0)
	      (set-nonrecursive-closure-intern-cache! v0 v0)
	      v0))
	 (allocate-nonrecursive-closure vs e))))

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

(define (allocate-recursive-closure vs xs es i)
 (cond
  ((eq? (lambda-expression-body-free-variable-indices1 (vector-ref es i))
	'unfilled)
   (set-lambda-expression-body-free-variable-indices1!
    (vector-ref es i)
    (let ((xs (recursive-closure-free-variables
	       (vector->list xs) (vector->list es))))
     (map (lambda (x) (positionp variable=? x xs))
	  (free-variables (lambda-expression-body (vector-ref es i))))))
   (set-lambda-expression-body-free-variable-indices2!
    (vector-ref es i)
    (map (lambda (x) (positionp-vector variable=? x xs))
	 (free-variables (lambda-expression-body (vector-ref es i))))))
  (else
   (assert (and
	    (equal?
	     (lambda-expression-body-free-variable-indices1 (vector-ref es i))
	     (let ((xs (recursive-closure-free-variables
			(vector->list xs) (vector->list es))))
	      (map (lambda (x) (positionp variable=? x xs))
		   (free-variables
		    (lambda-expression-body (vector-ref es i))))))
	    (equal?
	     (lambda-expression-body-free-variable-indices2 (vector-ref es i))
	     (map (lambda (x) (positionp-vector variable=? x xs))
		  (free-variables
		   (lambda-expression-body (vector-ref es i)))))))))
 (make-recursive-closure
  vs
  xs
  es
  i
  (lambda-expression-body-free-variable-indices1 (vector-ref es i))
  (lambda-expression-body-free-variable-indices2 (vector-ref es i))
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  #f
  'unfilled
  #f
  #f
  'unfilled
  '()
  '()
  #f))

(define (create-recursive-closure vs xs es i)
 (assert
  (and
   (= (length vs)
      (length (recursive-closure-free-variables
	       (vector->list xs) (vector->list es))))
   ;; See the note in new-nonrecursive-closure. While that hasn't happened in
   ;; practise, and I don't know whether it can, I removed it in principle.
   (or (eq? *mode* 'abstract)
       (every
	(lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	(recursive-closure-free-variables (vector->list xs) (vector->list es))
	vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and (eq? *mode* 'abstract)
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (recursive-closure-free-variables
	     (vector->list xs) (vector->list es))
	    vs)))
     (empty-abstract-value)
     (allocate-recursive-closure vs xs es i)))

(define (new-recursive-closure vs xs es i)
 (assert
  (and
   (= (length vs)
      (length (recursive-closure-free-variables
	       (vector->list xs) (vector->list es))))
   ;; See the note in new-nonrecursive-closure. While that hasn't happened in
   ;; practise, and I don't know whether it can, I removed it in principle.
   (or (eq? *mode* 'abstract)
       (every
	(lambda (x v) (prefix-tags? (variable-tags x) (value-tags v)))
	(recursive-closure-free-variables (vector->list xs) (vector->list es))
	vs))))
 (if (or
      (some empty-abstract-value? vs)
      (and (eq? *mode* 'abstract)
	   (some
	    (lambda (x v)
	     (every-value-tags
	      (lambda (tags) (not (prefix-tags? (variable-tags x) tags))) v))
	    (recursive-closure-free-variables
	     (vector->list xs) (vector->list es))
	    vs)))
     (empty-abstract-value)
     (if *interned?*
	 (or (find-if
	      (lambda (v0)
	       (and
		(= i (recursive-closure-index v0))
		(= (vector-length xs)
		   (vector-length (recursive-closure-procedure-variables v0)))
		(= (vector-length es)
		   (vector-length (recursive-closure-lambda-expressions v0)))
		;; This is an optimization.
		(= (length vs) (length (get-recursive-closure-values v0)))
		(every-vector dereferenced-expression-eqv?
			      es
			      (recursive-closure-lambda-expressions v0))
		(abstract-environment=? vs (get-recursive-closure-values v0))))
	      *recursive-closures*)
	     (let ((v0 (allocate-recursive-closure vs xs es i)))
	      (assert (not *frozen?*))
	      (set! *recursive-closures* (cons v0 *recursive-closures*))
	      (set-recursive-closure-canonize-cache! v0 v0)
	      (set-recursive-closure-intern-cache! v0 v0)
	      v0))
	 (allocate-recursive-closure vs xs es i))))

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

;;; There used to be both dereferenced and nondereferenced versions of
;;; nonrecursive-closure-match? and recursive-closure-match?.

(define (nonrecursive-closure-match? u1 u2)
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
      (every-vector dereferenced-expression-eqv?
		    (recursive-closure-lambda-expressions u1)
		    (recursive-closure-lambda-expressions u2))))

;;; This used to (assert (not (union? u)))
(define (closure? u) (or (nonrecursive-closure? u) (recursive-closure? u)))

;;; This used to use a nondereferencing closure match.
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

(define (closure-values u)
 (cond ((nonrecursive-closure? u) (get-nonrecursive-closure-values u))
       ((recursive-closure? u) (get-recursive-closure-values u))
       (else (internal-error))))

(define (closure-ref v x)
 (list-ref (closure-values v) (positionp variable=? x (closure-variables v))))

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

(define (tagged-new-nonrecursive-closure tags vs e)
 (if (empty-tags? tags)
     (new-nonrecursive-closure vs e)
     (case (first tags)
      ((perturbation)
       (perturb (tagged-new-nonrecursive-closure
		 (remove-tag 'perturbation tags)
		 (map unperturb vs)
		 (perturbation-transform-inverse e))))
      ((forward)
       (bundle (vlad-cons (tagged-new-nonrecursive-closure
			   (remove-tag 'forward tags)
			   (map primal vs)
			   (forward-transform-inverse e))
			  (perturb (tagged-new-nonrecursive-closure
				    (remove-tag 'forward tags)
				    (map unperturb (map tangent vs))
				    (forward-transform-inverse e))))))
      ((sensitivity)
       (sensitize (tagged-new-nonrecursive-closure
		   (remove-tag 'sensitivity tags)
		   (map unsensitize vs)
		   (sensitivity-transform-inverse e))))
      ((reverse)
       (*j (tagged-new-nonrecursive-closure
	    (remove-tag 'reverse tags)
	    (map *j-inverse vs)
	    (reverse-transform-inverse e))))
      (else (internal-error)))))

(define (tagged-new-recursive-closure tags vs xs es i)
 (if (empty-tags? tags)
     (new-recursive-closure vs xs es i)
     (case (first tags)
      ((perturbation)
       (perturb (tagged-new-recursive-closure
		 (remove-tag 'perturbation tags)
		 (map unperturb vs)
		 (map-vector unperturbationify xs)
		 (map-vector perturbation-transform-inverse es)
		 i)))
      ((forward)
       (bundle (vlad-cons (tagged-new-recursive-closure
			   (remove-tag 'forward tags)
			   (map primal vs)
			   (map-vector unforwardify xs)
			   (map-vector forward-transform-inverse es)
			   i)
			  (perturb (tagged-new-recursive-closure
				    (remove-tag 'forward tags)
				    (map unperturb (map tangent vs))
				    (map-vector unforwardify xs)
				    (map-vector forward-transform-inverse es)
				    i)))))
      ((sensitivity)
       (sensitize (tagged-new-recursive-closure
		   (remove-tag 'sensitivity tags)
		   (map unsensitize vs)
		   (map-vector unsensitivityify xs)
		   (map-vector sensitivity-transform-inverse es)
		   i)))
      ((reverse)
       (*j (tagged-new-recursive-closure
	    (remove-tag 'reverse tags)
	    (map *j-inverse vs)
	    (map-vector unreverseify xs)
	    (map-vector reverse-transform-inverse es)
	    i)))
      (else (internal-error)))))

(define (tagged-closure-ref tags v x)
 (if (empty-tags? tags)
     (cond
      ((union? v)
       ;; foo: to generate wideners for this case
       ;; widening case M3
       (unionize
	(map (lambda (u)
	      (if (closure? u)
		  (closure-ref u x)
		  (compile-time-warning "Argument might not be a closure" u)))
	     (get-union-values v))))
      ((closure? v) (closure-ref v x))
      (else (ad-error "Argument ~a a closure" v)))
     (case (first tags)
      ((perturbation)
       (perturb (tagged-closure-ref (remove-tag 'perturbation tags)
				    (unperturb v)
				    (unperturbationify x))))
      ((forward)
       (bundle
	(vlad-cons (tagged-closure-ref (remove-tag 'forward tags)
				       (unperturb v)
				       (unforwardify x))
		   (perturb (tagged-closure-ref (remove-tag 'forward tags)
						(unperturb (tangent v))
						(unforwardify x))))))
      ((sensitivity)
       (sensitize (tagged-closure-ref (remove-tag 'sensitivity tags)
				      (unsensitize v)
				      (unsensitivityify x))))
      ((reverse)
       (*j (tagged-closure-ref (remove-tag 'reverse tags)
			       (*j-inverse v)
			       (unreverseify x))))
      (else (internal-error)))))

;;; Perturbation tagged values

(define (allocate-perturbation-tagged-value v)
 (make-perturbation-tagged-value v
				 #f
				 #f
				 #f
				 #f
				 #f
				 #f
				 #f
				 #f
				 #f
				 'unfilled
				 #f
				 #f
				 'unfilled
				 '()
				 #f))

(define (create-perturbation-tagged-value v)
 (if (empty-abstract-value? v) v (allocate-perturbation-tagged-value v)))

(define (new-perturbation-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *interned?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-perturbation-tagged-value-primal v0)))
	      *perturbation-tagged-values*)
	     (let ((v0 (allocate-perturbation-tagged-value v)))
	      (assert (not *frozen?*))
	      (set! *perturbation-tagged-values*
		    (cons v0 *perturbation-tagged-values*))
	      (set-perturbation-tagged-value-canonize-cache! v0 v0)
	      (set-perturbation-tagged-value-intern-cache! v0 v0)
	      v0))
	 (allocate-perturbation-tagged-value v))))

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
	   (some-cps
	    (lambda (u-perturbation cs k) (loop v u-perturbation cs k))
	    (union-members v-perturbation)
	    cs
	    k))
	  ((or (and (vlad-empty-list? v)
		    (perturbation-tagged-value? v-perturbation)
		    (some vlad-empty-list?
			  (union-members
			   (get-perturbation-tagged-value-primal
			    v-perturbation))))
	       (and (vlad-true? v)
		    (perturbation-tagged-value? v-perturbation)
		    (some vlad-true?
			  (union-members
			   (get-perturbation-tagged-value-primal
			    v-perturbation))))
	       (and (vlad-false? v)
		    (perturbation-tagged-value? v-perturbation)
		    (some vlad-false?
			  (union-members
			   (get-perturbation-tagged-value-primal
			    v-perturbation))))
	       (and (vlad-real? v)
		    (perturbation-tagged-value? v-perturbation)
		    (some vlad-real?
			  (union-members
			   (get-perturbation-tagged-value-primal
			    v-perturbation))))
	       (and (primitive-procedure? v)
		    (perturbation-tagged-value? v-perturbation)
		    (some (lambda (u) (and (primitive-procedure? u) (eq? v u)))
			  (union-members
			   (get-perturbation-tagged-value-primal
			    v-perturbation)))))
	   (k #t cs))
	  ((and (nonrecursive-closure? v)
		(nonrecursive-closure? v-perturbation)
		(perturbation-parameter?
		 (nonrecursive-closure-parameter v-perturbation))
		(nonrecursive-closure-match? v (unperturb v-perturbation)))
	   (every2-cps loop
		       (get-nonrecursive-closure-values v)
		       (get-nonrecursive-closure-values v-perturbation)
		       cs
		       k))
	  ((and (recursive-closure? v)
		(recursive-closure? v-perturbation)
		(perturbation-parameter?
		 (recursive-closure-parameter v-perturbation))
		(recursive-closure-match? v (unperturb v-perturbation)))
	   (every2-cps loop
		       (get-recursive-closure-values v)
		       (get-recursive-closure-values v-perturbation)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (some-cps
	    (lambda (u-perturbation cs k)
	     (if (perturbation-tagged-value? u-perturbation)
		 (loop (get-perturbation-tagged-value-primal v)
		       (perturb
			(get-perturbation-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (bundle? v) (perturbation-tagged-value? v-perturbation))
	   (some-cps
	    (lambda (u-perturbation cs k)
	     (if (bundle? u-perturbation)
		 (loop (get-bundle-primal v)
		       (perturb (get-bundle-primal u-perturbation))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (get-bundle-tangent v)
				  (perturb (get-bundle-tangent u-perturbation))
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
	   (some-cps
	    (lambda (u-perturbation cs k)
	     (if (sensitivity-tagged-value? u-perturbation)
		 (loop (get-sensitivity-tagged-value-primal v)
		       (perturb
			(get-sensitivity-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (reverse-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (some-cps
	    (lambda (u-perturbation cs k)
	     (if (reverse-tagged-value? u-perturbation)
		 (loop (get-reverse-tagged-value-primal v)
		       (perturb
			(get-reverse-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (vlad-pair? v) (perturbation-tagged-value? v-perturbation))
	   (some-cps
	    (lambda (u-perturbation cs k)
	     (if (vlad-pair? u-perturbation)
		 (loop (vlad-car v)
		       (perturb (vlad-car u-perturbation))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (vlad-cdr v)
				  (perturb (vlad-cdr u-perturbation))
				  cs
				  k)
			    (k #f cs))))
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
	  ((and (nonrecursive-closure? v)
		(nonrecursive-closure? v-perturbation)
		(perturbation-parameter?
		 (nonrecursive-closure-parameter v-perturbation))
		(nonrecursive-closure-match? v (unperturb v-perturbation)))
	   (every2-cps loop
		       (get-nonrecursive-closure-values v)
		       (get-nonrecursive-closure-values v-perturbation)
		       cs
		       k))
	  ((and (recursive-closure? v)
		(recursive-closure? v-perturbation)
		(perturbation-parameter?
		 (recursive-closure-parameter v-perturbation))
		(recursive-closure-match? v (unperturb v-perturbation)))
	   (every2-cps loop
		       (get-recursive-closure-values v)
		       (get-recursive-closure-values v-perturbation)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (every-cps
	    (lambda (u-perturbation cs k)
	     (if (perturbation-tagged-value? u-perturbation)
		 (loop (get-perturbation-tagged-value-primal v)
		       (perturb
			(get-perturbation-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (bundle? v) (perturbation-tagged-value? v-perturbation))
	   (every-cps
	    (lambda (u-perturbation cs k)
	     (if (bundle? u-perturbation)
		 (loop (get-bundle-primal v)
		       (perturb (get-bundle-primal u-perturbation))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (get-bundle-tangent v)
				  (perturb (get-bundle-tangent u-perturbation))
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
	   (every-cps
	    (lambda (u-perturbation cs k)
	     (if (sensitivity-tagged-value? u-perturbation)
		 (loop (get-sensitivity-tagged-value-primal v)
		       (perturb
			(get-sensitivity-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (reverse-tagged-value? v)
		(perturbation-tagged-value? v-perturbation))
	   (every-cps
	    (lambda (u-perturbation cs k)
	     (if (reverse-tagged-value? u-perturbation)
		 (loop (get-reverse-tagged-value-primal v)
		       (perturb
			(get-reverse-tagged-value-primal u-perturbation))
		       cs
		       k)
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  ((and (vlad-pair? v) (perturbation-tagged-value? v-perturbation))
	   (every-cps
	    (lambda (u-perturbation cs k)
	     (if (vlad-pair? u-perturbation)
		 (loop (vlad-car v)
		       (perturb (vlad-car u-perturbation))
		       cs
		       (lambda (r? cs)
			(if r?
			    (loop (vlad-cdr v)
				  (perturb (vlad-cdr u-perturbation))
				  cs
				  k)
			    (k #f cs))))
		 (k #f cs)))
	    (union-members
	     (get-perturbation-tagged-value-primal v-perturbation))
	    cs
	    k))
	  (else (k #f cs)))))))))

(define (allocate-bundle v v-perturbation)
 (make-bundle v
	      v-perturbation
	      #f
	      #f
	      #f
	      #f
	      #f
	      #f
	      #f
	      #f
	      #f
	      'unfilled
	      #f
	      #f
	      'unfilled
	      '()
	      #f))

(define (create-bundle v v-perturbation)
 (assert (or (eq? *mode* 'abstract) (some-bundlable? v v-perturbation)))
 (if (or (empty-abstract-value? v)
	 (empty-abstract-value? v-perturbation)
	 (and (eq? *mode* 'abstract) (not (some-bundlable? v v-perturbation))))
     (empty-abstract-value)
     (allocate-bundle v v-perturbation)))

(define (new-bundle v v-perturbation)
 (assert (or (eq? *mode* 'abstract) (some-bundlable? v v-perturbation)))
 (if (or (empty-abstract-value? v)
	 (empty-abstract-value? v-perturbation)
	 (and (eq? *mode* 'abstract) (not (some-bundlable? v v-perturbation))))
     (empty-abstract-value)
     (if *interned?*
	 (or (find-if
	      (lambda (v0)
	       (and (abstract-value=? v (get-bundle-primal v0))
		    (abstract-value=? v-perturbation (get-bundle-tangent v0))))
	      *bundles*)
	     (let ((v0 (allocate-bundle v v-perturbation)))
	      (assert (not *frozen?*))
	      (set! *bundles* (cons v0 *bundles*))
	      (set-bundle-canonize-cache! v0 v0)
	      (set-bundle-intern-cache! v0 v0)
	      v0))
	 (allocate-bundle v v-perturbation))))

(define (fill-bundle! u v v-perturbation)
 ;; We can't do the full checks of new-bundle at this point because there may
 ;; be residual unfilled slots so the checks are delayed until
 ;; canonize-abstract-value.
 (assert (and (eq? (bundle-primal u) 'unfilled)
	      (eq? (bundle-tangent u) 'unfilled)))
 (set-bundle-primal! u v)
 (set-bundle-tangent! u v-perturbation))

(define (get-bundle-primal v)
 (assert (not (eq? (bundle-primal v) 'unfilled)))
 (bundle-primal v))

(define (get-bundle-tangent v)
 (assert (not (eq? (bundle-tangent v) 'unfilled)))
 (bundle-tangent v))

;;; Sensitivity tagged values

(define (allocate-sensitivity-tagged-value v)
 (make-sensitivity-tagged-value v
				#f
				#f
				#f
				#f
				#f
				#f
				#f
				#f
				#f
				'unfilled
				#f
				#f
				'unfilled
				'()
				#f))

(define (create-sensitivity-tagged-value v)
 (if (empty-abstract-value? v) v (allocate-sensitivity-tagged-value v)))

(define (new-sensitivity-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *interned?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-sensitivity-tagged-value-primal v0)))
	      *sensitivity-tagged-values*)
	     (let ((v0 (allocate-sensitivity-tagged-value v)))
	      (assert (not *frozen?*))
	      (set! *sensitivity-tagged-values*
		    (cons v0 *sensitivity-tagged-values*))
	      (set-sensitivity-tagged-value-canonize-cache! v0 v0)
	      (set-sensitivity-tagged-value-intern-cache! v0 v0)
	      v0))
	 (allocate-sensitivity-tagged-value v))))

(define (fill-sensitivity-tagged-value-primal! u v)
 ;; We can't do the full checks of new-sensitivity-tagged-value at this point
 ;; because there may be residual unfilled slots so the checks are delayed
 ;; until canonize-abstract-value.
 (assert (eq? (sensitivity-tagged-value-primal u) 'unfilled))
 (set-sensitivity-tagged-value-primal! u v))

(define (get-sensitivity-tagged-value-primal v)
 (assert (not (eq? (sensitivity-tagged-value-primal v) 'unfilled)))
 (sensitivity-tagged-value-primal v))

;;; Reverse tagged values

(define (allocate-reverse-tagged-value v)
 (make-reverse-tagged-value v
			    #f
			    #f
			    #f
			    #f
			    #f
			    #f
			    #f
			    #f
			    #f
			    'unfilled
			    #f
			    #f
			    'unfilled
			    '()
			    #f))

(define (create-reverse-tagged-value v)
 (if (empty-abstract-value? v) v (allocate-reverse-tagged-value v)))

(define (new-reverse-tagged-value v)
 (if (empty-abstract-value? v)
     v
     (if *interned?*
	 (or (find-if
	      (lambda (v0)
	       (abstract-value=? v (get-reverse-tagged-value-primal v0)))
	      *reverse-tagged-values*)
	     (let ((v0 (allocate-reverse-tagged-value v)))
	      (assert (not *frozen?*))
	      (set! *reverse-tagged-values* (cons v0 *reverse-tagged-values*))
	      (set-reverse-tagged-value-canonize-cache! v0 v0)
	      (set-reverse-tagged-value-intern-cache! v0 v0)
	      v0))
	 (allocate-reverse-tagged-value v))))

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

(define (allocate-vlad-pair v1 v2)
 (make-vlad-pair v1
		 v2
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 #f
		 'unfilled
		 #f
		 #f
		 'unfilled
		 '()
		 #f))

(define (create-vlad-pair v1 v2)
 (if (or (empty-abstract-value? v1) (empty-abstract-value? v2))
     (empty-abstract-value)
     (allocate-vlad-pair v1 v2)))

(define (fill-vlad-pair! u v1 v2)
 ;; We can't do the full checks of vlad-cons at this point because there may
 ;; be residual unfilled slots so the checks are delayed until
 ;; canonize-abstract-value.
 (assert (and (eq? (vlad-pair-car u) 'unfilled)
	      (eq? (vlad-pair-cdr u) 'unfilled)))
 (set-vlad-pair-car! u v1)
 (set-vlad-pair-cdr! u v2))

(define (vlad-cons v1 v2)
 (if (or (empty-abstract-value? v1) (empty-abstract-value? v2))
     (empty-abstract-value)
     (if *interned?*
	 (or (find-if (lambda (v0)
		       (and (abstract-value=? v1 (vlad-car v0))
			    (abstract-value=? v2 (vlad-cdr v0))))
		      *vlad-pairs*)
	     (let ((v0 (allocate-vlad-pair v1 v2)))
	      (assert (not *frozen?*))
	      (set! *vlad-pairs* (cons v0 *vlad-pairs*))
	      (set-vlad-pair-canonize-cache! v0 v0)
	      (set-vlad-pair-intern-cache! v0 v0)
	      v0))
	 (allocate-vlad-pair v1 v2))))

(define (vlad-car u)
 (assert (and (vlad-pair? u) (not (eq? (vlad-pair-car u) 'unfilled))))
 (vlad-pair-car u))

(define (vlad-cdr u)
 (assert (and (vlad-pair? u) (not (eq? (vlad-pair-cdr u) 'unfilled))))
 (vlad-pair-cdr u))

(define (tagged-vlad-cons tags v1 v2)
 (if (empty-tags? tags)
     (vlad-cons v1 v2)
     (case (first tags)
      ((perturbation)
       (perturb
	(tagged-vlad-cons
	 (remove-tag 'perturbation tags) (unperturb v1) (unperturb v2))))
      ((forward)
       (bundle
	(vlad-cons (tagged-vlad-cons
		    (remove-tag 'forward tags) (primal v1) (primal v2))
		   (perturb (tagged-vlad-cons (remove-tag 'forward tags)
					      (unperturb (tangent v1))
					      (unperturb (tangent v2)))))))
      ((sensitivity)
       (sensitize
	(tagged-vlad-cons
	 (remove-tag 'sensitivity tags) (unsensitize v1) (unsensitize v2))))
      ((reverse)
       (*j (tagged-vlad-cons
	    (remove-tag 'reverse tags) (*j-inverse v1) (*j-inverse v2))))
      (else (internal-error)))))

(define (tagged-vlad-car tags u)
 (if (empty-tags? tags)
     (cond
      ((union? u)
       ;; widening case M1
       (unionize
	(map (lambda (u)
	      (if (vlad-pair? u)
		  (vlad-car u)
		  (compile-time-warning "Argument might not be a pair" u)))
	     (get-union-values u))))
      ((vlad-pair? u) (vlad-car u))
      (else (ad-error "Argument ~a a pair" u)))
     (case (first tags)
      ((perturbation)
       (perturb
	(tagged-vlad-car (remove-tag 'perturbation tags) (unperturb u))))
      ((forward)
       (bundle
	(vlad-cons (tagged-vlad-car (remove-tag 'forward tags) (primal u))
		   (perturb (tagged-vlad-car (remove-tag 'forward tags)
					     (unperturb (tangent u)))))))
      ((sensitivity)
       (sensitize
	(tagged-vlad-car (remove-tag 'sensitivity tags) (unsensitize u))))
      ((reverse)
       (*j (tagged-vlad-car (remove-tag 'reverse tags) (*j-inverse u))))
      (else (internal-error)))))

(define (tagged-vlad-cdr tags u)
 (if (empty-tags? tags)
     (cond
      ((union? u)
       ;; widening case M2
       (unionize
	(map (lambda (u)
	      (if (vlad-pair? u)
		  (vlad-cdr u)
		  (compile-time-warning "Argument might not be a pair" u)))
	     (get-union-values u))))
      ((vlad-pair? u) (vlad-cdr u))
      (else (ad-error "Argument ~a a pair" u)))
     (case (first tags)
      ((perturbation)
       (perturb
	(tagged-vlad-cdr (remove-tag 'perturbation tags) (unperturb u))))
      ((forward)
       (bundle
	(vlad-cons (tagged-vlad-cdr (remove-tag 'forward tags) (primal u))
		   (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
					     (unperturb (tangent u)))))))
      ((sensitivity)
       (sensitize
	(tagged-vlad-cdr (remove-tag 'sensitivity tags) (unsensitize u))))
      ((reverse)
       (*j (tagged-vlad-cdr (remove-tag 'reverse tags) (*j-inverse u))))
      (else (internal-error)))))

;;; Unions

(define (empty-abstract-value) *empty-abstract-value*)

(define (empty-abstract-value? v) (null? (union-members v)))

(define (abstract-boolean) *abstract-boolean*)

(define (union-members v)
 (if (union? v)
     (map-reduce append '() union-members (get-union-values v))
     (list v)))

(define (allocate-union vs)
 (make-union vs
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     #f
	     'unfilled
	     #f
	     #f
	     'unfilled
	     '()
	     #f))

;;; The only widening case uses of this are in abstract-value-union-internal.
(define (create-union vs) (allocate-union vs))

(define (new-union vs)
 (if *interned?*
     (or (find-if
	  (lambda (v0) (set-equalp? abstract-value=? vs (get-union-values v0)))
	  *unions*)
	 ;; This is not a widening case.
	 (let ((v0 (allocate-union vs)))
	  (assert (not *frozen?*))
	  (set! *unions* (cons v0 *unions*))
	  (set-union-canonize-cache! v0 v0)
	  (set-union-intern-cache! v0 v0)
	  v0))
     ;; This is not a widening case.
     (allocate-union vs)))

(define (fill-union-values! v vs)
 (assert (and (not (memq v vs)) (eq? (union-values v) 'unfilled)))
 (set-union-values! v vs))

(define (get-union-values v)
 (assert (not (eq? (union-values v) 'unfilled)))
 (union-values v))

(define (unionize vs) (reduce abstract-value-union vs (empty-abstract-value)))

(define (map-union f v) (unionize (map f (union-members v))))

(define (for-each-union f v) (for-each f (get-union-values v)))

(define (cross-union f v1 v2)
 (unionize (cross-product f (union-members v1) (union-members v2))))

;;; Environment bindings

(define (new-environment-binding vs v)
 ;; debugging
 (when #f
  (assert (and (every meets-syntactic-constraints? vs)
	       (meets-syntactic-constraints? v))))
 (make-environment-binding vs v))

;;; Instances

(define (lookup-function-instance v1 v2)
 (find-if
  (lambda (instance)
   (and (abstract-value=? (function-instance-v1 instance) v1)
	(abstract-value=? (function-instance-v2 instance) v2)))
  (cond
   ((nonrecursive-closure? v1) (nonrecursive-closure-function-instances v1))
   ((recursive-closure? v1) (recursive-closure-function-instances v1))
   (else (internal-error)))))

(define (new-function-instance v1 v2)
 (or (lookup-function-instance v1 v2)
     (let ((instance (make-function-instance v1 v2 #f 0 #t #f #f #f #f #f)))
      (set! *function-instances* (cons instance *function-instances*))
      (cond
       ((nonrecursive-closure? v1)
	(set-nonrecursive-closure-function-instances!
	 v1 (cons instance (nonrecursive-closure-function-instances v1))))
       ((recursive-closure? v1)
	(set-recursive-closure-function-instances!
	 v1 (cons instance (recursive-closure-function-instances v1))))
       (else (internal-error)))
      instance)))

(define (lookup-widener-instance v1 v2)
 (find-if
  (lambda (instance)
   (and (abstract-value=? (widener-instance-v1 instance) v1)
	(abstract-value=? (widener-instance-v2 instance) v2)))
  (cond
   ((nonrecursive-closure? v1) (nonrecursive-closure-widener-instances v1))
   ((recursive-closure? v1) (recursive-closure-widener-instances v1))
   ((perturbation-tagged-value? v1)
    (perturbation-tagged-value-widener-instances v1))
   ((bundle? v1) (bundle-widener-instances v1))
   ((sensitivity-tagged-value? v1)
    (sensitivity-tagged-value-widener-instances v1))
   ((reverse-tagged-value? v1) (reverse-tagged-value-widener-instances v1))
   ((vlad-pair? v1) (vlad-pair-widener-instances v1))
   ((union? v1) (union-widener-instances v1))
   (else *scalar-widener-instances*))))

(define (new-widener-instance v1 v2)
 (or (lookup-widener-instance v1 v2)
     (let ((instance (make-widener-instance v1 v2 #f 0 #t #f #f #f #f #f)))
      (set! *widener-instances* (cons instance *widener-instances*))
      (cond
       ((nonrecursive-closure? v1)
	(set-nonrecursive-closure-widener-instances!
	 v1 (cons instance (nonrecursive-closure-widener-instances v1))))
       ((recursive-closure? v1)
	(set-recursive-closure-widener-instances!
	 v1 (cons instance (recursive-closure-widener-instances v1))))
       ((perturbation-tagged-value? v1)
	(set-perturbation-tagged-value-widener-instances!
	 v1 (cons instance (perturbation-tagged-value-widener-instances v1))))
       ((bundle? v1)
	(set-bundle-widener-instances!
	 v1 (cons instance (bundle-widener-instances v1))))
       ((sensitivity-tagged-value? v1)
	(set-sensitivity-tagged-value-widener-instances!
	 v1 (cons instance (sensitivity-tagged-value-widener-instances v1))))
       ((reverse-tagged-value? v1)
	(set-reverse-tagged-value-widener-instances!
	 v1 (cons instance (reverse-tagged-value-widener-instances v1))))
       ((vlad-pair? v1)
	(set-vlad-pair-widener-instances!
	 v1 (cons instance (vlad-pair-widener-instances v1))))
       ((union? v1)
	(set-union-widener-instances!
	 v1 (cons instance (union-widener-instances v1))))
       (else (set! *scalar-widener-instances*
		   (cons instance *scalar-widener-instances*))))
      instance)))

(define (lookup-primitive-procedure s)
 (value-binding-value
  (find-if (lambda (b)
	    (eq? (primitive-procedure-symbol (value-binding-value b)) s))
	   *value-bindings*)))

(define (find-instance s v)
 (find-if (lambda (instance)
	   (abstract-value=? (primitive-procedure-instance-v instance) v))
	  (primitive-procedure-instances (lookup-primitive-procedure s))))

(define (lookup-instance s v)
 (let ((instance (find-instance s v))) (assert instance) instance))

(define (new-instance s v)
 (let ((primitive-procedure (lookup-primitive-procedure s)))
  (or (find-if (lambda (instance)
		(abstract-value=? (primitive-procedure-instance-v instance) v))
	       (primitive-procedure-instances primitive-procedure))
      (let ((instance
	     (make-primitive-procedure-instance s v 0 #t #f '() #f #f #f)))
       (set-primitive-procedure-instances!
	primitive-procedure
	(cons instance (primitive-procedure-instances primitive-procedure)))
       instance))))

(define (instance-number-of-call-sites instance)
 ((cond ((function-instance? instance) function-instance-number-of-call-sites)
	((widener-instance? instance) widener-instance-number-of-call-sites)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-number-of-call-sites)
	(else (internal-error)))
  instance))

(define (set-instance-number-of-call-sites! instance number-of-call-sites)
 ((cond
   ((function-instance? instance) set-function-instance-number-of-call-sites!)
   ((widener-instance? instance) set-widener-instance-number-of-call-sites!)
   ((primitive-procedure-instance? instance)
    set-primitive-procedure-instance-number-of-call-sites!)
   (else (internal-error)))
  instance
  number-of-call-sites))

(define (inline? instance)
 ((cond ((function-instance? instance) function-instance-inline?)
	((widener-instance? instance) widener-instance-inline?)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-inline?)
	(else (internal-error)))
  instance))

(define (set-inline?! instance p?)
 ((cond ((function-instance? instance) set-function-instance-inline?!)
	((widener-instance? instance) set-widener-instance-inline?!)
	((primitive-procedure-instance? instance)
	 set-primitive-procedure-instance-inline?!)
	(else (internal-error)))
  instance
  p?))

(define (input-alias instance)
 ((cond ((function-instance? instance) function-instance-input-alias)
	((widener-instance? instance) widener-instance-input-alias)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-input-alias)
	(else (internal-error)))
  instance))

(define (set-input-alias! instance a)
 ((cond ((function-instance? instance) set-function-instance-input-alias!)
	((widener-instance? instance) set-widener-instance-input-alias!)
	((primitive-procedure-instance? instance)
	 set-primitive-procedure-instance-input-alias!)
	(else (internal-error)))
  instance
  a))

(define (new-input-aliases instance)
 ((cond ((function-instance? instance) function-instance-new-input-aliases)
	((widener-instance? instance) widener-instance-new-input-aliases)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-new-input-aliases)
	(else (internal-error)))
  instance))

(define (set-new-input-aliases! instance as)
 ((cond
   ((function-instance? instance) set-function-instance-new-input-aliases!)
   ((widener-instance? instance) set-widener-instance-new-input-aliases!)
   ((primitive-procedure-instance? instance)
    set-primitive-procedure-instance-new-input-aliases!)
   (else (internal-error)))
  instance
  as))

(define (output-alias instance)
 ((cond ((function-instance? instance) function-instance-output-alias)
	((widener-instance? instance) widener-instance-output-alias)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-output-alias)
	(else (internal-error)))
  instance))

(define (set-output-alias! instance a)
 ((cond ((function-instance? instance) set-function-instance-output-alias!)
	((widener-instance? instance) set-widener-instance-output-alias!)
	((primitive-procedure-instance? instance)
	 set-primitive-procedure-instance-output-alias!)
	(else (internal-error)))
  instance
  a))

(define (instance-il instance)
 ((cond ((function-instance? instance) function-instance-il)
	((widener-instance? instance) widener-instance-il)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-il)
	(else (internal-error)))
  instance))

(define (set-instance-il! instance il)
 ((cond ((function-instance? instance) set-function-instance-il!)
	((widener-instance? instance) set-widener-instance-il!)
	((primitive-procedure-instance? instance)
	 set-primitive-procedure-instance-il!)
	(else (internal-error)))
  instance
  il))

(define (instance-argument-values instance)
 (cond
  ((string? instance)
   (cond ((string=? instance "read_real") '())
	 ((string=? instance "write_real") (list (abstract-real)))
	 ((string=? instance "sqrt") (list (abstract-real)))
	 ((string=? instance "exp") (list (abstract-real)))
	 ((string=? instance "log") (list (abstract-real)))
	 ((string=? instance "sin") (list (abstract-real)))
	 ((string=? instance "cos") (list (abstract-real)))
	 ((string=? instance "atan2") (list (abstract-real) (abstract-real)))
	 (else (internal-error))))
  ((function-instance? instance)
   (list (function-instance-v1 instance) (function-instance-v2 instance)))
  ((widener-instance? instance) (list (widener-instance-v1 instance)))
  ((primitive-procedure-instance? instance)
   (list (primitive-procedure-instance-v instance)))
  (else (internal-error))))

(define (instance-return-value instance)
 (cond ((string? instance)
	(cond ((string=? instance "read_real") (abstract-real))
	      ((string=? instance "write_real") (abstract-real))
	      ((string=? instance "sqrt") (abstract-real))
	      ((string=? instance "exp") (abstract-real))
	      ((string=? instance "log") (abstract-real))
	      ((string=? instance "sin") (abstract-real))
	      ((string=? instance "cos") (abstract-real))
	      ((string=? instance "atan2") (abstract-real))
	      (else (internal-error))))
       ((function-instance? instance)
	(abstract-apply (function-instance-v1 instance)
			(function-instance-v2 instance)))
       ((widener-instance? instance) (widener-instance-v2 instance))
       ((primitive-procedure-instance? instance)
	((primitive-procedure-abstract
	  (lookup-primitive-procedure
	   (primitive-procedure-instance-symbol instance)))
	 (primitive-procedure-instance-v instance)))
       (else (internal-error))))

(define (instance-flag? instance)
 ((cond ((function-instance? instance) function-instance-flag?)
	((widener-instance? instance) widener-instance-flag?)
	((primitive-procedure-instance? instance)
	 primitive-procedure-instance-flag?)
	(else (internal-error)))
  instance))

(define (set-instance-flag?! instance flag?)
 ((cond ((function-instance? instance) set-function-instance-flag?!)
	((widener-instance? instance) set-widener-instance-flag?!)
	((primitive-procedure-instance? instance)
	 set-primitive-procedure-instance-flag?!)
	(else (internal-error)))
  instance
  flag?))

;;; Generic

(define (perturb-cache v)
 ((cond
   ((nonrecursive-closure? v) nonrecursive-closure-perturb-cache)
   ((recursive-closure? v) recursive-closure-perturb-cache)
   ((perturbation-tagged-value? v) perturbation-tagged-value-perturb-cache)
   ((bundle? v) bundle-perturb-cache)
   ((sensitivity-tagged-value? v) sensitivity-tagged-value-perturb-cache)
   ((reverse-tagged-value? v) reverse-tagged-value-perturb-cache)
   ((vlad-pair? v) vlad-pair-perturb-cache)
   ((union? v) union-perturb-cache)
   (else (internal-error)))
  v))

(define (set-perturb-cache! v v-perturbation)
 ((cond
   ((nonrecursive-closure? v) set-nonrecursive-closure-perturb-cache!)
   ((recursive-closure? v) set-recursive-closure-perturb-cache!)
   ((perturbation-tagged-value? v)
    set-perturbation-tagged-value-perturb-cache!)
   ((bundle? v) set-bundle-perturb-cache!)
   ((sensitivity-tagged-value? v) set-sensitivity-tagged-value-perturb-cache!)
   ((reverse-tagged-value? v) set-reverse-tagged-value-perturb-cache!)
   ((vlad-pair? v) set-vlad-pair-perturb-cache!)
   ((union? v) set-union-perturb-cache!)
   (else (internal-error)))
  v
  v-perturbation))

(define (unperturb-cache v-perturbation)
 ((cond ((nonrecursive-closure? v-perturbation)
	 nonrecursive-closure-unperturb-cache)
	((recursive-closure? v-perturbation) recursive-closure-unperturb-cache)
	((union? v-perturbation) union-unperturb-cache)
	(else (internal-error)))
  v-perturbation))

(define (set-unperturb-cache! v-perturbation v)
 ((cond ((nonrecursive-closure? v-perturbation)
	 set-nonrecursive-closure-unperturb-cache!)
	((recursive-closure? v-perturbation)
	 set-recursive-closure-unperturb-cache!)
	((union? v-perturbation) set-union-unperturb-cache!)
	(else (internal-error)))
  v-perturbation
  v))

(define (primal-cache v-forward)
 ((cond ((nonrecursive-closure? v-forward) nonrecursive-closure-primal-cache)
	((recursive-closure? v-forward) recursive-closure-primal-cache)
	((union? v-forward) union-primal-cache)
	(else (internal-error)))
  v-forward))

(define (set-primal-cache! v-forward v)
 ((cond
   ((nonrecursive-closure? v-forward) set-nonrecursive-closure-primal-cache!)
   ((recursive-closure? v-forward) set-recursive-closure-primal-cache!)
   ((union? v-forward) set-union-primal-cache!)
   (else (internal-error)))
  v-forward
  v))

(define (tangent-cache v-forward)
 ((cond ((nonrecursive-closure? v-forward) nonrecursive-closure-tangent-cache)
	((recursive-closure? v-forward) recursive-closure-tangent-cache)
	((union? v-forward) union-tangent-cache)
	(else (internal-error)))
  v-forward))

(define (set-tangent-cache! v-forward v)
 ((cond
   ((nonrecursive-closure? v-forward) set-nonrecursive-closure-tangent-cache!)
   ((recursive-closure? v-forward) set-recursive-closure-tangent-cache!)
   ((union? v-forward) set-union-tangent-cache!)
   (else (internal-error)))
  v-forward
  v))

(define (sensitize-cache v)
 ((cond
   ((nonrecursive-closure? v) nonrecursive-closure-sensitize-cache)
   ((recursive-closure? v) recursive-closure-sensitize-cache)
   ((perturbation-tagged-value? v) perturbation-tagged-value-sensitize-cache)
   ((bundle? v) bundle-sensitize-cache)
   ((sensitivity-tagged-value? v) sensitivity-tagged-value-sensitize-cache)
   ((reverse-tagged-value? v) reverse-tagged-value-sensitize-cache)
   ((vlad-pair? v) vlad-pair-sensitize-cache)
   ((union? v) union-sensitize-cache)
   (else (internal-error)))
  v))

(define (set-sensitize-cache! v v-sensitivity)
 ((cond ((nonrecursive-closure? v) set-nonrecursive-closure-sensitize-cache!)
	((recursive-closure? v) set-recursive-closure-sensitize-cache!)
	((perturbation-tagged-value? v)
	 set-perturbation-tagged-value-sensitize-cache!)
	((bundle? v) set-bundle-sensitize-cache!)
	((sensitivity-tagged-value? v)
	 set-sensitivity-tagged-value-sensitize-cache!)
	((reverse-tagged-value? v) set-reverse-tagged-value-sensitize-cache!)
	((vlad-pair? v) set-vlad-pair-sensitize-cache!)
	((union? v) set-union-sensitize-cache!)
	(else (internal-error)))
  v
  v-sensitivity))

(define (unsensitize-cache v-sensitivity)
 ((cond ((nonrecursive-closure? v-sensitivity)
	 nonrecursive-closure-unsensitize-cache)
	((recursive-closure? v-sensitivity)
	 recursive-closure-unsensitize-cache)
	((union? v-sensitivity) union-unsensitize-cache)
	(else (internal-error)))
  v-sensitivity))

(define (set-unsensitize-cache! v-sensitivity v)
 ((cond ((nonrecursive-closure? v-sensitivity)
	 set-nonrecursive-closure-unsensitize-cache!)
	((recursive-closure? v-sensitivity)
	 set-recursive-closure-unsensitize-cache!)
	((union? v-sensitivity) set-union-unsensitize-cache!)
	(else (internal-error)))
  v-sensitivity
  v))

(define (*j-cache v)
 ((cond ((nonrecursive-closure? v) nonrecursive-closure-*j-cache)
	((recursive-closure? v) recursive-closure-*j-cache)
	((perturbation-tagged-value? v) perturbation-tagged-value-*j-cache)
	((bundle? v) bundle-*j-cache)
	((sensitivity-tagged-value? v) sensitivity-tagged-value-*j-cache)
	((reverse-tagged-value? v) reverse-tagged-value-*j-cache)
	((vlad-pair? v) vlad-pair-*j-cache)
	((union? v) union-*j-cache)
	(else (internal-error)))
  v))

(define (set-*j-cache! v v-reverse)
 ((cond
   ((nonrecursive-closure? v) set-nonrecursive-closure-*j-cache!)
   ((recursive-closure? v) set-recursive-closure-*j-cache!)
   ((perturbation-tagged-value? v) set-perturbation-tagged-value-*j-cache!)
   ((bundle? v) set-bundle-*j-cache!)
   ((sensitivity-tagged-value? v) set-sensitivity-tagged-value-*j-cache!)
   ((reverse-tagged-value? v) set-reverse-tagged-value-*j-cache!)
   ((vlad-pair? v) set-vlad-pair-*j-cache!)
   ((union? v) set-union-*j-cache!)
   (else (internal-error)))
  v
  v-reverse))

(define (*j-inverse-cache v-reverse)
 ((cond
   ((nonrecursive-closure? v-reverse) nonrecursive-closure-*j-inverse-cache)
   ((recursive-closure? v-reverse) recursive-closure-*j-inverse-cache)
   ((union? v-reverse) union-*j-inverse-cache)
   (else (internal-error)))
  v-reverse))

(define (set-*j-inverse-cache! v-reverse v)
 ((cond ((nonrecursive-closure? v-reverse)
	 set-nonrecursive-closure-*j-inverse-cache!)
	((recursive-closure? v-reverse)
	 set-recursive-closure-*j-inverse-cache!)
	((union? v-reverse) set-union-*j-inverse-cache!)
	(else (internal-error)))
  v-reverse
  v))

(define (perturbation-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (perturbation-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (perturbation-parameter? (recursive-closure-parameter u)))
     (perturbation-tagged-value? u)))

(define (forward-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (forward-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (forward-parameter? (recursive-closure-parameter u)))
     (bundle? u)))

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
     (sensitivity-tagged-value? u)))

(define (reverse-value? u)
 (assert (not (union? u)))
 (or (and (nonrecursive-closure? u)
	  (reverse-parameter? (nonrecursive-closure-parameter u)))
     (and (recursive-closure? u)
	  (reverse-parameter? (recursive-closure-parameter u)))
     (reverse-tagged-value? u)))

(define (scalar-value? u)
 (assert (not (union? u)))
 (or (vlad-boolean? u)
     (vlad-empty-list? u)
     (vlad-real? u)
     (primitive-procedure? u)))

(define (aggregate-value-values u)
 (cond ((nonrecursive-closure? u) (get-nonrecursive-closure-values u))
       ((recursive-closure? u) (get-recursive-closure-values u))
       ((perturbation-tagged-value? u)
	(list (get-perturbation-tagged-value-primal u)))
       ((bundle? u) (list (get-bundle-primal u) (get-bundle-tangent u)))
       ((sensitivity-tagged-value? u)
	(list (get-sensitivity-tagged-value-primal u)))
       ((reverse-tagged-value? u) (list (get-reverse-tagged-value-primal u)))
       ((vlad-pair? u) (list (vlad-car u) (vlad-cdr u)))
       (else (internal-error))))

(define (aggregate-value-alias-values u a)
 (assert (compatible-alias? u a))
 (cond ((nonrecursive-closure? u) (get-nonrecursive-closure-alias-values u a))
       ((recursive-closure? u) (get-recursive-closure-alias-values u a))
       ((perturbation-tagged-value? u)
	(list (get-perturbation-tagged-value-primal-alias u a)))
       ((bundle? u) (get-bundle-aliases u a))
       ((sensitivity-tagged-value? u)
	(list (get-sensitivity-tagged-value-primal-alias u a)))
       ((reverse-tagged-value? u)
	(list (get-reverse-tagged-value-primal-alias u a)))
       ((vlad-pair? u) (get-vlad-pair-aliases u a))
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
  ((vlad-pair? u)
   (assert (= (length vs) 2))
   (create-vlad-pair (first vs) (second vs)))
  (else (internal-error))))

(define (value-tags u)
 (assert (not (union? u)))
 (cond ((scalar-value? u) '())
       ((nonrecursive-closure? u) (nonrecursive-closure-tags u))
       ((recursive-closure? u) (recursive-closure-tags u))
       ((perturbation-tagged-value? u)
	(add-tag 'perturbation
		 (value-tags (get-perturbation-tagged-value-primal u))))
       ;; needs work: When we add unions one might be able to get a more
       ;;             precise answer by traversing both the primal and the
       ;;             tangent.
       ((bundle? u) (add-tag 'forward (value-tags (get-bundle-primal u))))
       ((sensitivity-tagged-value? u)
	(add-tag 'sensitivity
		 (value-tags (get-sensitivity-tagged-value-primal u))))
       ((reverse-tagged-value? u)
	(add-tag 'reverse (value-tags (get-reverse-tagged-value-primal u))))
       ((vlad-pair? u) '())
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
   ((vlad-pair? v) (p (reverse tags)))
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
   ((vlad-pair? v) (p (reverse tags)))
   (else (internal-error)))))

(define (c:index thing)
 (cond
  ((variable? thing) (variable-c:index thing))
  ((nonrecursive-closure? thing) (nonrecursive-closure-c:index thing))
  ((recursive-closure? thing) (recursive-closure-c:index thing))
  ((perturbation-tagged-value? thing)
   (perturbation-tagged-value-c:index thing))
  ((bundle? thing) (bundle-c:index thing))
  ((sensitivity-tagged-value? thing) (sensitivity-tagged-value-c:index thing))
  ((reverse-tagged-value? thing) (reverse-tagged-value-c:index thing))
  ((vlad-pair? thing) (vlad-pair-c:index thing))
  ((union? thing) (union-c:index thing))
  ((function-instance? thing) (function-instance-c:index thing))
  ((widener-instance? thing) (widener-instance-c:index thing))
  ((primitive-procedure-instance? thing)
   (c:index (primitive-procedure-instance-v thing)))
  (else (cdr (assp abstract-value=? thing *c:indices*)))))

(define (set-c:index! thing i)
 (cond
  ((variable? thing) (set-variable-c:index! thing i))
  ((nonrecursive-closure? thing) (set-nonrecursive-closure-c:index! thing i))
  ((recursive-closure? thing) (set-recursive-closure-c:index! thing i))
  ((perturbation-tagged-value? thing)
   (set-perturbation-tagged-value-c:index! thing i))
  ((bundle? thing) (set-bundle-c:index! thing i))
  ((sensitivity-tagged-value? thing)
   (set-sensitivity-tagged-value-c:index! thing i))
  ((reverse-tagged-value? thing) (set-reverse-tagged-value-c:index! thing i))
  ((vlad-pair? thing) (set-vlad-pair-c:index! thing i))
  ((union? thing) (set-union-c:index! thing i))
  ((function-instance? thing) (set-function-instance-c:index! thing i))
  ((widener-instance? thing) (set-widener-instance-c:index! thing i))
  ((primitive-procedure-instance? thing) (internal-error))
  (else (set! *c:indices* (cons (cons thing i) *c:indices*)))))

(define (boxed? v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-boxed? v))
       ((recursive-closure? v) (recursive-closure-boxed? v))
       ((perturbation-tagged-value? v) (perturbation-tagged-value-boxed? v))
       ((bundle? v) (bundle-boxed? v))
       ((sensitivity-tagged-value? v) (sensitivity-tagged-value-boxed? v))
       ((reverse-tagged-value? v) (reverse-tagged-value-boxed? v))
       ((vlad-pair? v) (vlad-pair-boxed? v))
       ((union? v) (union-boxed? v))
       (else #f)))

(define (set-boxed?! v p?)
 ((cond ((nonrecursive-closure? v) set-nonrecursive-closure-boxed?!)
	((recursive-closure? v) set-recursive-closure-boxed?!)
	((perturbation-tagged-value? v) set-perturbation-tagged-value-boxed?!)
	((bundle? v) set-bundle-boxed?!)
	((sensitivity-tagged-value? v) set-sensitivity-tagged-value-boxed?!)
	((reverse-tagged-value? v) set-reverse-tagged-value-boxed?!)
	((vlad-pair? v) set-vlad-pair-boxed?!)
	((union? v) set-union-boxed?!)
	(else (internal-error)))
  v
  p?))

(define (alias v)
 ((cond ((nonrecursive-closure? v) nonrecursive-closure-alias)
	((recursive-closure? v) recursive-closure-alias)
	((perturbation-tagged-value? v) perturbation-tagged-value-alias)
	((bundle? v) bundle-alias)
	((sensitivity-tagged-value? v) sensitivity-tagged-value-alias)
	((reverse-tagged-value? v) reverse-tagged-value-alias)
	((vlad-pair? v) vlad-pair-alias)
	((union? v) union-alias)
	(else (internal-error)))
  v))

(define (set-alias! v a)
 ((cond ((nonrecursive-closure? v) set-nonrecursive-closure-alias!)
	((recursive-closure? v) set-recursive-closure-alias!)
	((perturbation-tagged-value? v) set-perturbation-tagged-value-alias!)
	((bundle? v) set-bundle-alias!)
	((sensitivity-tagged-value? v) set-sensitivity-tagged-value-alias!)
	((reverse-tagged-value? v) set-reverse-tagged-value-alias!)
	((vlad-pair? v) set-vlad-pair-alias!)
	((union? v) set-union-alias!)
	(else (internal-error)))
  v
  a))

(define (new-aliases v)
 ((cond ((nonrecursive-closure? v) nonrecursive-closure-new-aliases)
	((recursive-closure? v) recursive-closure-new-aliases)
	((perturbation-tagged-value? v) perturbation-tagged-value-new-aliases)
	((bundle? v) bundle-new-aliases)
	((sensitivity-tagged-value? v) sensitivity-tagged-value-new-aliases)
	((reverse-tagged-value? v) reverse-tagged-value-new-aliases)
	((vlad-pair? v) vlad-pair-new-aliases)
	((union? v) union-new-aliases)
	(else (internal-error)))
  v))

(define (set-new-aliases! v as)
 ((cond
   ((nonrecursive-closure? v) set-nonrecursive-closure-new-aliases!)
   ((recursive-closure? v) set-recursive-closure-new-aliases!)
   ((perturbation-tagged-value? v) set-perturbation-tagged-value-new-aliases!)
   ((bundle? v) set-bundle-new-aliases!)
   ((sensitivity-tagged-value? v) set-sensitivity-tagged-value-new-aliases!)
   ((reverse-tagged-value? v) set-reverse-tagged-value-new-aliases!)
   ((vlad-pair? v) set-vlad-pair-new-aliases!)
   ((union? v) set-union-new-aliases!)
   (else (internal-error)))
  v
  as))

(define (abstract-value-flag? v)
 (cond ((nonrecursive-closure? v) (nonrecursive-closure-flag? v))
       ((recursive-closure? v) (recursive-closure-flag? v))
       ((perturbation-tagged-value? v) (perturbation-tagged-value-flag? v))
       ((bundle? v) (bundle-flag? v))
       ((sensitivity-tagged-value? v) (sensitivity-tagged-value-flag? v))
       ((reverse-tagged-value? v) (reverse-tagged-value-flag? v))
       ((vlad-pair? v) (vlad-pair-flag? v))
       ((union? v) (union-flag? v))
       (else (memp abstract-value=? v *flagged-abstract-values*))))

(define (set-abstract-value-flag?! v p?)
 (cond
  ((nonrecursive-closure? v) (set-nonrecursive-closure-flag?! v p?))
  ((recursive-closure? v) (set-recursive-closure-flag?! v p?))
  ((perturbation-tagged-value? v) (set-perturbation-tagged-value-flag?! v p?))
  ((bundle? v) (set-bundle-flag?! v p?))
  ((sensitivity-tagged-value? v) (set-sensitivity-tagged-value-flag?! v p?))
  ((reverse-tagged-value? v) (set-reverse-tagged-value-flag?! v p?))
  ((vlad-pair? v) (set-vlad-pair-flag?! v p?))
  ((union? v) (set-union-flag?! v p?))
  (p? (unless (memp abstract-value=? v *flagged-abstract-values*)
       (set! *flagged-abstract-values* (cons v *flagged-abstract-values*))))
  (else (set! *flagged-abstract-values*
	      (removep abstract-value=? v *flagged-abstract-values*)))))

;;; Abstract value subset, equivalence, nondisjointness, union, canonization,
;;; and internment

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
		;; This used to use a nondereferencing closure match.
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		;; This used to use a nondereferencing closure match.
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1)
		(perturbation-tagged-value? v2))
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
	  ((and (vlad-pair? v1) (vlad-pair? v2))
	   (loop (vlad-car v1)
		 (vlad-car v2)
		 cs
		 (lambda (r? cs)
		  (if r? (loop (vlad-cdr v1) (vlad-cdr v2) cs k) (k #f cs)))))
	  (else (k #f cs)))))))))

(define (deep-abstract-value=? v1 v2)
 (and (abstract-value-subset? v1 v2) (abstract-value-subset? v2 v1)))

(define (abstract-value=? v1 v2)
 (if *interned?*
     ;; This works because vlad-empty-list is (), vlad-true is #t, vlad-false
     ;; is #f, abstract-real is real, and all other non-concrete-real values
     ;; are structures. All of these are comparable with eq?.
     (or (eq? v1 v2) (and (real? v1) (real? v2) (equal? v1 v2)))
     (deep-abstract-value=? v1 v2)))

(define (filled-abstract-value-subset? v1 v2)
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
	(let* ((c (cons (cons v1 v2) #t))
	       (cs (cons c cs))
	       (k (lambda (r? cs)
		   (set-cdr! c r?)
		   (k r? cs))))
	 (cond
	  ;; This is an optimization.
	  ((eq? v1 v2) (k #t cs))
	  ((union? v1)
	   (if (eq? (union-values v1) 'unfilled)
	       (k #f cs)
	       (every-cps
		(lambda (u1 cs k) (loop u1 v2 cs k)) (union-members v1) cs k)))
	  ((union? v2)
	   (if (eq? (union-values v2) 'unfilled)
	       (k #f cs)
	       (some-cps
		(lambda (u2 cs k) (loop v1 u2 cs k)) (union-members v2) cs k)))
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
		(not (eq? (nonrecursive-closure-values v1) 'unfilled))
		(not (eq? (nonrecursive-closure-values v2) 'unfilled))
		;; This used to use a nondereferencing closure match.
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		(not (eq? (recursive-closure-values v1) 'unfilled))
		(not (eq? (recursive-closure-values v2) 'unfilled))
		;; This used to use a nondereferencing closure match.
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1)
		(perturbation-tagged-value? v2)
		(not (eq? (perturbation-tagged-value-primal v1) 'unfilled))
		(not (eq? (perturbation-tagged-value-primal v2) 'unfilled)))
	   (loop (get-perturbation-tagged-value-primal v1)
		 (get-perturbation-tagged-value-primal v2)
		 cs
		 k))
	  ((and (bundle? v1)
		(bundle? v2)
		(not (eq? (bundle-primal v1) 'unfilled))
		(not (eq? (bundle-tangent v1) 'unfilled))
		(not (eq? (bundle-primal v2) 'unfilled))
		(not (eq? (bundle-tangent v2) 'unfilled)))
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
	  ((and (sensitivity-tagged-value? v1)
		(sensitivity-tagged-value? v2)
		(not (eq? (sensitivity-tagged-value-primal v1) 'unfilled))
		(not (eq? (sensitivity-tagged-value-primal v2) 'unfilled)))
	   (loop (get-sensitivity-tagged-value-primal v1)
		 (get-sensitivity-tagged-value-primal v2)
		 cs
		 k))
	  ((and (reverse-tagged-value? v1)
		(reverse-tagged-value? v2)
		(not (eq? (reverse-tagged-value-primal v1) 'unfilled))
		(not (eq? (reverse-tagged-value-primal v2) 'unfilled)))
	   (loop (get-reverse-tagged-value-primal v1)
		 (get-reverse-tagged-value-primal v2)
		 cs
		 k))
	  ((and (vlad-pair? v1)
		(vlad-pair? v2)
		(not (eq? (vlad-pair-car v1) 'unfilled))
		(not (eq? (vlad-pair-cdr v1) 'unfilled))
		(not (eq? (vlad-pair-car v2) 'unfilled))
		(not (eq? (vlad-pair-cdr v2) 'unfilled)))
	   (loop (vlad-car v1)
		 (vlad-car v2)
		 cs
		 (lambda (r? cs)
		  (if r? (loop (vlad-cdr v1) (vlad-cdr v2) cs k) (k #f cs)))))
	  (else (k #f cs)))))))))

(define (filled-deep-abstract-value=? v1 v2)
 (and (filled-abstract-value-subset? v1 v2)
      (filled-abstract-value-subset? v2 v1)))

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
  4
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
		;; This used to use a nondereferencing closure match.
		(nonrecursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-nonrecursive-closure-values v1)
		       (get-nonrecursive-closure-values v2)
		       cs
		       k))
	  ((and (recursive-closure? v1)
		(recursive-closure? v2)
		;; This used to use a nondereferencing closure match.
		(recursive-closure-match? v1 v2))
	   ;; See the note in abstract-environment=?.
	   (every2-cps loop
		       (get-recursive-closure-values v1)
		       (get-recursive-closure-values v2)
		       cs
		       k))
	  ((and (perturbation-tagged-value? v1)
		(perturbation-tagged-value? v2))
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
	  ((and (vlad-pair? v1) (vlad-pair? v2))
	   (loop (vlad-car v1)
		 (vlad-car v2)
		 cs
		 (lambda (r? cs)
		  (if r? (loop (vlad-cdr v1) (vlad-cdr v2) cs k) (k #f cs)))))
	  (else (k #f cs)))))))))

(define (abstract-value-unionable? p? v1 v2)
 ;; When p? is true asks whether unionable without creating new top-level
 ;; union.
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  5
  (or (not *almost-union-free?*)
      (let loop ((p? p?) (v1 v1) (v2 v2) (cs '()) (k (lambda (r? cs) r?)))
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
	      ((or (union? v1) (union? v2))
	       (every-cps
		(lambda (u1 cs k)
		 (some-cps (lambda (u2 cs k) (loop #t u1 u2 cs k))
			   (union-members v2)
			   cs
			   k))
		(union-members v1)
		cs
		(lambda (r? cs)
		 (if r?
		     (k #t cs)
		     (every-cps
		      (lambda (u2 cs k)
		       (some-cps (lambda (u1 cs k) (loop #t u1 u2 cs k))
				 (union-members v1)
				 cs
				 k))
		      (union-members v2)
		      cs
		      k)))))
	      ((or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
		   (and (vlad-true? v1) (vlad-true? v2))
		   (and (vlad-false? v1) (vlad-false? v2))
		   (and (vlad-boolean? v1) (vlad-boolean? v2) (not p?))
		   (and (vlad-real? v1) (vlad-real? v2))
		   (and (primitive-procedure? v1)
			(primitive-procedure? v2)
			(eq? v1 v2))
		   (and (backpropagator? v1) (backpropagator? v2) (not p?))
		   ;; needs work: I use union-members instead of
		   ;;             get-union-values below since v1 and v2 might
		   ;;             not be canonical because unionable? is
		   ;;             called in union-internal which is called on
		   ;;             values that might not be canonical and also
		   ;;             by widen-lists on arguments that might not
		   ;;             be canonical because widen-lists calls and
		   ;;             processes the result of union-internal. This
		   ;;             whole mess needs to be cleaned up.
		   (and (not p?)
			(vlad-pair? v2)
			(vlad-empty-list? v1)
			(union? (vlad-cdr v2))
			(= (length (union-members (vlad-cdr v2))) 2)
			(some vlad-empty-list? (union-members (vlad-cdr v2)))
			(some (lambda (u2) (deep-abstract-value=? u2 v2))
			      (union-members (vlad-cdr v2))))
		   (and (not p?)
			(vlad-pair? v1)
			(vlad-empty-list? v2)
			(union? (vlad-cdr v1))
			(= (length (union-members (vlad-cdr v1))) 2)
			(some vlad-empty-list? (union-members (vlad-cdr v1)))
			(some (lambda (u1) (deep-abstract-value=? u1 v1))
			      (union-members (vlad-cdr v1)))))
	       (k #t cs))
	      ((and (nonrecursive-closure? v1)
		    (nonrecursive-closure? v2)
		    ;; This used to use a nondereferencing closure match.
		    (nonrecursive-closure-match? v1 v2))
	       ;; See the note in abstract-environment=?.
	       (every2-cps (lambda (u1 u2 cs k) (loop #f u1 u2 cs k))
			   (get-nonrecursive-closure-values v1)
			   (get-nonrecursive-closure-values v2)
			   cs
			   k))
	      ((and (recursive-closure? v1)
		    (recursive-closure? v2)
		    ;; This used to use a nondereferencing closure match.
		    (recursive-closure-match? v1 v2))
	       ;; See the note in abstract-environment=?.
	       (every2-cps (lambda (u1 u2 cs k) (loop #f u1 u2 cs k))
			   (get-recursive-closure-values v1)
			   (get-recursive-closure-values v2)
			   cs
			   k))
	      ((and (perturbation-tagged-value? v1)
		    (perturbation-tagged-value? v2))
	       (loop #f
		     (get-perturbation-tagged-value-primal v1)
		     (get-perturbation-tagged-value-primal v2)
		     cs
		     k))
	      ((and (bundle? v1) (bundle? v2))
	       (loop #f
		     (get-bundle-primal v1)
		     (get-bundle-primal v2)
		     cs
		     (lambda (r? cs)
		      (if r?
			  (loop #f
				(get-bundle-tangent v1)
				(get-bundle-tangent v2)
				cs
				k)
			  (k #f cs)))))
	      ((and (sensitivity-tagged-value? v1)
		    (sensitivity-tagged-value? v2))
	       (loop #f
		     (get-sensitivity-tagged-value-primal v1)
		     (get-sensitivity-tagged-value-primal v2)
		     cs
		     k))
	      ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	       (loop #f
		     (get-reverse-tagged-value-primal v1)
		     (get-reverse-tagged-value-primal v2)
		     cs
		     k))
	      ((and (vlad-pair? v1) (vlad-pair? v2))
	       (loop #f
		     (vlad-car v1)
		     (vlad-car v2)
		     cs
		     (lambda (r? cs)
		      (if r?
			  (loop #f (vlad-cdr v1) (vlad-cdr v2) cs k)
			  (k #f cs)))))
	      (else (k #f cs))))))))))

(define (abstract-value-union-internal v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 ;; The output can be wider than the strict union since unions of transformed
 ;; booleans are transformed into transformed unions of booleans, widening in
 ;; the process (for bundles).
 (time-it-bucket
  6
  (if *almost-union-free?*
      (let loop ((v1 v1) (v2 v2) (cs '()) (k (lambda (v cs) v)))
       (let ((found?
	      (find-if (lambda (c)
			(and (eq? (car (car c)) v1) (eq? (cdr (car c)) v2)))
		       cs)))
	(cond
	 (found? (k (cdr found?) cs))
	 ;; needs work: These two cases were added because of
	 ;;             examples/generator-tests/bug{1,2,3,4}. This bug happens
	 ;;             because loop has the invariant that while the result
	 ;;             can be unfilled, the argumets must be filled. But
	 ;;             reduce-cps violates this invariant. I don't know how to
	 ;;             properly fix this. The next two cases hide the bug but
	 ;;             I'm not sure that they solve it.
	 ((abstract-value-subset? v1 v2) (k v2 cs))
	 ((abstract-value-subset? v2 v1) (k v1 cs))
	 ;; needs work: I added the restriction to unionable?-#t to preclude
	 ;;             the error check in fill-union-values that happens
	 ;;             when unioning (union #t #f) with #f. But I fear that
	 ;;             this now precludes unions of more than two elements,
	 ;;             inter alia, more than two backpropagators.
	 ((or (union? v1) (union? v2))
	  (cond
	   ((every (lambda (u1)
		    (some (lambda (u2) (abstract-value-unionable? #t u1 u2))
			  (union-members v2)))
		   (union-members v1))
	    (let ((u12s
		   (map (lambda (u1)
			 (cons u1
			       (find-if (lambda (u2)
					 (abstract-value-unionable? #t u1 u2))
					(union-members v2))))
			(union-members v1)))
		  (v (allocate-union 'unfilled)))
	     (map-cps
	      (lambda (u2 cs k)
	       (reduce-cps
		loop
		(map car
		     (remove-if-not (lambda (u12) (eq? (cdr u12) u2)) u12s))
		u2
		cs
		k))
	      (union-members v2)
	      (cons (cons (cons v1 v2) v) cs)
	      (lambda (us cs)
	       (fill-union-values! v us)
	       (k v cs)))))
	   ((every (lambda (u2)
		    (some (lambda (u1) (abstract-value-unionable? #t u1 u2))
			  (union-members v1)))
		   (union-members v2))
	    (let ((u21s
		   (map (lambda (u2)
			 (cons u2
			       (find-if (lambda (u1)
					 (abstract-value-unionable? #t u1 u2))
					(union-members v1))))
			(union-members v2)))
		  (v (allocate-union 'unfilled)))
	     (map-cps
	      (lambda (u1 cs k)
	       (reduce-cps
		loop
		(map car
		     (remove-if-not (lambda (u21) (eq? (cdr u21) u1)) u21s))
		u1
		cs
		k))
	      (union-members v1)
	      (cons (cons (cons v1 v2) v) cs)
	      (lambda (us cs)
	       (fill-union-values! v us)
	       (k v cs)))))
	   ;; needs work: Sometimes anerror occures in externalize because
	   ;;             v1 and/or v2 might not be canonical since
	   ;;             abstract-value-union-internal is called inside
	   ;;             canonize-abstractvalue.
	   (else (compile-time-error "Program is not almost union free: ~s ~s"
				     (externalize v1)
				     (externalize v2)))))
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
	 ;; See note in abstract-value-unionable?.
	 ((and (vlad-pair? v2)
	       (vlad-empty-list? v1)
	       (union? (vlad-cdr v2))
	       (= (length (union-members (vlad-cdr v2))) 2)
	       (some vlad-empty-list? (union-members (vlad-cdr v2)))
	       (some (lambda (u2) (deep-abstract-value=? u2 v2))
		     (union-members (vlad-cdr v2))))
	  (let ((u (vlad-cdr v2))) (k u (cons (cons (cons v1 v2) u) cs))))
	 ((and (vlad-pair? v1)
	       (vlad-empty-list? v2)
	       (union? (vlad-cdr v1))
	       (= (length (union-members (vlad-cdr v1))) 2)
	       (some vlad-empty-list? (union-members (vlad-cdr v1)))
	       (some (lambda (u1) (deep-abstract-value=? u1 v1))
		     (union-members (vlad-cdr v1))))
	  (let ((u (vlad-cdr v1))) (k u (cons (cons (cons v1 v2) u) cs))))
	 ((and (nonrecursive-closure? v1)
	       (nonrecursive-closure? v2)
	       ;; This used to use a nondereferencing closure match.
	       (nonrecursive-closure-match? v1 v2)
	       (every (lambda (v1 v2) (abstract-value-unionable? #f v1 v2))
		      (get-nonrecursive-closure-values v1)
		      (get-nonrecursive-closure-values v2)))
	  ;; See the note in abstract-environment=?.
	  (let ((u (allocate-nonrecursive-closure
		    'unfilled (nonrecursive-closure-lambda-expression v1))))
	   (map2-cps loop
		     (get-nonrecursive-closure-values v1)
		     (get-nonrecursive-closure-values v2)
		     (cons (cons (cons v1 v2) u) cs)
		     (lambda (vs cs)
		      (fill-nonrecursive-closure-values! u vs)
		      (k u cs)))))
	 ((and (backpropagator? v1) (backpropagator? v2))
	  ;; I removed a check whether v1 and v2 where deep-abstract-value=?
	  ;; here since I believe that that check is subsumed by the above.
	  (let ((u (create-union (list v1 v2))))
	   (k u (cons (cons (cons v1 v2) u) cs))))
	 ((and (recursive-closure? v1)
	       (recursive-closure? v2)
	       ;; This used to use a nondereferencing closure match.
	       (recursive-closure-match? v1 v2))
	  ;; See the note in abstract-environment=?.
	  (let ((u (allocate-recursive-closure
		    'unfilled
		    (recursive-closure-procedure-variables v1)
		    (recursive-closure-lambda-expressions v1)
		    (recursive-closure-index v1))))
	   (map2-cps loop
		     (get-recursive-closure-values v1)
		     (get-recursive-closure-values v2)
		     (cons (cons (cons v1 v2) u) cs)
		     (lambda (vs cs)
		      (fill-recursive-closure-values! u vs)
		      (k u cs)))))
	 ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	  (let ((u (allocate-perturbation-tagged-value 'unfilled)))
	   (loop (get-perturbation-tagged-value-primal v1)
		 (get-perturbation-tagged-value-primal v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (v cs)
		  (fill-perturbation-tagged-value-primal! u v)
		  (k u cs)))))
	 ((and (bundle? v1) (bundle? v2))
	  (let ((u (allocate-bundle 'unfilled 'unfilled)))
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
	  (let ((u (allocate-sensitivity-tagged-value 'unfilled)))
	   (loop (get-sensitivity-tagged-value-primal v1)
		 (get-sensitivity-tagged-value-primal v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (v cs)
		  (fill-sensitivity-tagged-value-primal! u v)
		  (k u cs)))))
	 ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	  (let ((u (allocate-reverse-tagged-value 'unfilled)))
	   (loop (get-reverse-tagged-value-primal v1)
		 (get-reverse-tagged-value-primal v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (v cs)
		  (fill-reverse-tagged-value-primal! u v)
		  (k u cs)))))
	 ((and (vlad-pair? v1) (vlad-pair? v2))
	  (let ((u (allocate-vlad-pair 'unfilled 'unfilled)))
	   (loop (vlad-car v1)
		 (vlad-car v2)
		 (cons (cons (cons v1 v2) u) cs)
		 (lambda (v-car cs)
		  (loop (vlad-cdr v1)
			(vlad-cdr v2)
			cs
			(lambda (v-cdr cs)
			 (fill-vlad-pair! u v-car v-cdr)
			 (k u cs)))))))
	 ;; needs work: See note above.
	 (else (compile-time-error "Program is not almost union free: ~s ~s"
				   (externalize v1)
				   (externalize v2))))))
      (cond ((abstract-value-subset? v1 v2) v2)
	    ((abstract-value-subset? v2 v1) v1)
	    (else (create-union
		   (maximal-elements
		    abstract-value-subset?
		    (append (union-members v1) (union-members v2)))))))))

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
 ;; non-eq values which when merged yield a value that again has that path
 ;; causing an infinite loop.
 (time-it-bucket
  7
  (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
   (let ((found? (assp deep-abstract-value=? v cs)))
    (cond
     (found? (k (cdr found?) cs))
     ((union? v)
      (cond
       ((union-canonize-cache v) (k (union-canonize-cache v) cs))
       ((deep-empty-abstract-value? v)
	(let ((u-prime (empty-abstract-value)))
	 (k u-prime (cons (cons v u-prime) cs))))
       (else
	;; This is the whole reason we require that abstract values be
	;; copied. This performs the optimization that unionize performs but
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
	 ;; the error earlier, at the time of creation, but this just
	 ;; triggers the same error later, since we require that every
	 ;; abstract value be copied.
	 (cond ((null? us) (k (empty-abstract-value) cs))
	       ;; This used to add (cons v (first us)) to the cs cache but
	       ;; that caused a nested union bug in t22 without
	       ;; -imprecise-inexact when doing -all-limits 1
	       ;; -pair-depth-limit 3. I now believe that the
	       ;; following is correct.
	       ((null? (rest us)) (loop (first us) cs k))
	       (else (let ((v-prime (allocate-union 'unfilled)))
		      (set-union-canonize-cache! v v-prime)
		      (set-union-canonize-cache! v-prime v-prime)
		      (map-cps loop
			       us
			       (cons (cons v v-prime) cs)
			       (lambda (us-prime cs)
				(assert
				 (and (not (null? us-prime))
				      (not (null? (rest us-prime)))
				      (= (length us) (length us-prime))
				      (not (some union? us-prime))))
				(fill-union-values! v-prime us-prime)
				(k v-prime cs))))))))))
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
      (cond
       ((nonrecursive-closure-canonize-cache v)
	(k (nonrecursive-closure-canonize-cache v) cs))
       ((deep-empty-abstract-value? v)
	(let ((u-prime (empty-abstract-value)))
	 (k u-prime (cons (cons v u-prime) cs))))
       (else
	;; See the note in abstract-environment=?.
	(let ((u-prime (allocate-nonrecursive-closure
			'unfilled (nonrecursive-closure-lambda-expression v))))
	 (assert
	  (and (= (length (get-nonrecursive-closure-values v))
		  (length (free-variables
			   (nonrecursive-closure-lambda-expression u-prime))))
	       ;; See the note in new-nonrecursive-closure.
	       (or (eq? *mode* 'abstract)
		   (every (lambda (x v)
			   (prefix-tags? (variable-tags x) (value-tags v)))
			  (free-variables
			   (nonrecursive-closure-lambda-expression u-prime))
			  (get-nonrecursive-closure-values v)))
	       (not (some empty-abstract-value?
			  (get-nonrecursive-closure-values v)))
	       (or (eq? *mode* 'concrete)
		   (every (lambda (x v)
			   (some-value-tags
			    (lambda (tags)
			     (prefix-tags? (variable-tags x) tags)) v))
			  (free-variables
			   (nonrecursive-closure-lambda-expression u-prime))
			  (get-nonrecursive-closure-values v)))))
	 (set-nonrecursive-closure-canonize-cache! v u-prime)
	 (set-nonrecursive-closure-canonize-cache! u-prime u-prime)
	 (map-cps loop
		  (get-nonrecursive-closure-values v)
		  (cons (cons v u-prime) cs)
		  (lambda (vs-prime cs)
		   (fill-nonrecursive-closure-values! u-prime vs-prime)
		   (k u-prime cs)))))))
     ((recursive-closure? v)
      (cond ((recursive-closure-canonize-cache v)
	     (k (recursive-closure-canonize-cache v) cs))
	    ((deep-empty-abstract-value? v)
	     (let ((u-prime (empty-abstract-value)))
	      (k u-prime (cons (cons v u-prime) cs))))
	    (else
	     ;; See the note in abstract-environment=?.
	     (let ((u-prime (allocate-recursive-closure
			     'unfilled
			     (recursive-closure-procedure-variables v)
			     (recursive-closure-lambda-expressions v)
			     (recursive-closure-index v))))
	      (assert
	       (and
		(= (length (get-recursive-closure-values v))
		   (length (recursive-closure-variables u-prime)))
		;; See the note in new-nonrecursive-closure.
		(or (eq? *mode* 'abstract)
		    (every (lambda (x v)
			    (prefix-tags? (variable-tags x) (value-tags v)))
			   (recursive-closure-variables u-prime)
			   (get-recursive-closure-values v)))
		(not (some empty-abstract-value?
			   (get-recursive-closure-values v)))
		(or (eq? *mode* 'concrete)
		    (every (lambda (x v)
			    (some-value-tags
			     (lambda (tags)
			      (prefix-tags? (variable-tags x) tags)) v))
			   (recursive-closure-variables u-prime)
			   (get-recursive-closure-values v)))))
	      (set-recursive-closure-canonize-cache! v u-prime)
	      (set-recursive-closure-canonize-cache! u-prime u-prime)
	      (map-cps loop
		       (get-recursive-closure-values v)
		       (cons (cons v u-prime) cs)
		       (lambda (vs-prime cs)
			(fill-recursive-closure-values! u-prime vs-prime)
			(k u-prime cs)))))))
     ((perturbation-tagged-value? v)
      (cond ((perturbation-tagged-value-canonize-cache v)
	     (k (perturbation-tagged-value-canonize-cache v) cs))
	    ((deep-empty-abstract-value? v)
	     (let ((u-prime (empty-abstract-value)))
	      (k u-prime (cons (cons v u-prime) cs))))
	    (else
	     (let ((u-prime (allocate-perturbation-tagged-value 'unfilled)))
	      (assert (not (empty-abstract-value?
			    (get-perturbation-tagged-value-primal v))))
	      (set-perturbation-tagged-value-canonize-cache! v u-prime)
	      (set-perturbation-tagged-value-canonize-cache! u-prime u-prime)
	      (loop (get-perturbation-tagged-value-primal v)
		    (cons (cons v u-prime) cs)
		    (lambda (v-prime cs)
		     (fill-perturbation-tagged-value-primal! u-prime v-prime)
		     (k u-prime cs)))))))
     ((bundle? v)
      (cond
       ((bundle-canonize-cache v) (k (bundle-canonize-cache v) cs))
       ((deep-empty-abstract-value? v)
	(let ((u-prime (empty-abstract-value)))
	 (k u-prime (cons (cons v u-prime) cs))))
       (else
	(let ((u-prime (allocate-bundle 'unfilled 'unfilled)))
	 (assert
	  (and (some-bundlable? (get-bundle-primal v) (get-bundle-tangent v))
	       (not (empty-abstract-value? (get-bundle-primal v)))
	       (not (empty-abstract-value? (get-bundle-tangent v)))))
	 (set-bundle-canonize-cache! v u-prime)
	 (set-bundle-canonize-cache! u-prime u-prime)
	 (loop (get-bundle-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-primal-prime cs)
		(loop (get-bundle-tangent v)
		      cs
		      (lambda (v-tangent-prime cs)
		       (fill-bundle! u-prime v-primal-prime v-tangent-prime)
		       (k u-prime cs)))))))))
     ((sensitivity-tagged-value? v)
      (cond ((sensitivity-tagged-value-canonize-cache v)
	     (k (sensitivity-tagged-value-canonize-cache v) cs))
	    ((deep-empty-abstract-value? v)
	     (let ((u-prime (empty-abstract-value)))
	      (k u-prime (cons (cons v u-prime) cs))))
	    (else
	     (let ((u-prime (allocate-sensitivity-tagged-value 'unfilled)))
	      (assert (not (empty-abstract-value?
			    (get-sensitivity-tagged-value-primal v))))
	      (set-sensitivity-tagged-value-canonize-cache! v u-prime)
	      (set-sensitivity-tagged-value-canonize-cache! u-prime u-prime)
	      (loop (get-sensitivity-tagged-value-primal v)
		    (cons (cons v u-prime) cs)
		    (lambda (v-prime cs)
		     (fill-sensitivity-tagged-value-primal! u-prime v-prime)
		     (k u-prime cs)))))))
     ((reverse-tagged-value? v)
      (cond
       ((reverse-tagged-value-canonize-cache v)
	(k (reverse-tagged-value-canonize-cache v) cs))
       ((deep-empty-abstract-value? v)
	(let ((u-prime (empty-abstract-value)))
	 (k u-prime (cons (cons v u-prime) cs))))
       (else
	(let ((u-prime (allocate-reverse-tagged-value 'unfilled)))
	 (assert
	  (not (empty-abstract-value? (get-reverse-tagged-value-primal v))))
	 (set-reverse-tagged-value-canonize-cache! v u-prime)
	 (set-reverse-tagged-value-canonize-cache! u-prime u-prime)
	 (loop (get-reverse-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-reverse-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))))
     ((vlad-pair? v)
      (cond ((vlad-pair-canonize-cache v) (k (vlad-pair-canonize-cache v) cs))
	    ((deep-empty-abstract-value? v)
	     (let ((u-prime (empty-abstract-value)))
	      (k u-prime (cons (cons v u-prime) cs))))
	    (else
	     (let ((u-prime (allocate-vlad-pair 'unfilled 'unfilled)))
	      (assert (and (not (empty-abstract-value? (vlad-car v)))
			   (not (empty-abstract-value? (vlad-cdr v)))))
	      (set-vlad-pair-canonize-cache! v u-prime)
	      (set-vlad-pair-canonize-cache! u-prime u-prime)
	      (loop (vlad-car v)
		    (cons (cons v u-prime) cs)
		    (lambda (v-car-prime cs)
		     (loop (vlad-cdr v)
			   cs
			   (lambda (v-cdr-prime cs)
			    (fill-vlad-pair! u-prime v-car-prime v-cdr-prime)
			    (k u-prime cs)))))))))
     (else (internal-error)))))))

(define (intern-abstract-value v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  8
  (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
   (cond
    ((union? v)
     (if (union-intern-cache v)
	 (k (union-intern-cache v) cs)
	 (let ((v-prime (find-if (lambda (v-prime)
				  (filled-deep-abstract-value=? v-prime v))
				 *unions*)))
	  (if v-prime
	      (k v-prime (cons (cons v v-prime) cs))
	      (let ((v-prime (allocate-union 'unfilled)))
	       (assert (not *frozen?*))
	       (set-union-canonize-cache! v-prime v-prime)
	       (set-union-intern-cache! v v-prime)
	       (set-union-intern-cache! v-prime v-prime)
	       (map-cps
		loop
		(get-union-values v)
		(cons (cons v v-prime) cs)
		(lambda (us-prime cs)
		 (assert
		  (and (not (null? us-prime)) (not (null? (rest us-prime)))))
		 (set! *unions* (cons v-prime *unions*))
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
     (if (nonrecursive-closure-intern-cache v)
	 (k (nonrecursive-closure-intern-cache v) cs)
	 ;; See the notes in new-nonrecursive-closure.
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *nonrecursive-closures*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      ;; See the note in abstract-environment=?.
	      (let ((u-prime
		     (allocate-nonrecursive-closure
		      'unfilled (nonrecursive-closure-lambda-expression v))))
	       (assert
		(and
		 (= (length (get-nonrecursive-closure-values v))
		    (length
		     (free-variables
		      (nonrecursive-closure-lambda-expression u-prime))))
		 ;; See the note in new-nonrecursive-closure.
		 (or (eq? *mode* 'abstract)
		     (every (lambda (x v)
			     (prefix-tags? (variable-tags x) (value-tags v)))
			    (free-variables
			     (nonrecursive-closure-lambda-expression u-prime))
			    (get-nonrecursive-closure-values v)))
		 (not (some empty-abstract-value?
			    (get-nonrecursive-closure-values v)))
		 (or (eq? *mode* 'concrete)
		     (every (lambda (x v)
			     (some-value-tags
			      (lambda (tags)
			       (prefix-tags? (variable-tags x) tags)) v))
			    (free-variables
			     (nonrecursive-closure-lambda-expression u-prime))
			    (get-nonrecursive-closure-values v)))
		 (not *frozen?*)))
	       (set-nonrecursive-closure-canonize-cache! u-prime u-prime)
	       (set-nonrecursive-closure-intern-cache! v u-prime)
	       (set-nonrecursive-closure-intern-cache! u-prime u-prime)
	       (map-cps
		loop
		(get-nonrecursive-closure-values v)
		(cons (cons v u-prime) cs)
		(lambda (vs-prime cs)
		 (set! *nonrecursive-closures*
		       (cons u-prime *nonrecursive-closures*))
		 (fill-nonrecursive-closure-values! u-prime vs-prime)
		 (k u-prime cs))))))))
    ((recursive-closure? v)
     (if (recursive-closure-intern-cache v)
	 (k (recursive-closure-intern-cache v) cs)
	 ;; See the notes in new-recursive-closure.
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *recursive-closures*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      ;; See the note in abstract-environment=?.
	      (let ((u-prime (allocate-recursive-closure
			      'unfilled
			      (recursive-closure-procedure-variables v)
			      (recursive-closure-lambda-expressions v)
			      (recursive-closure-index v))))
	       (assert
		(and
		 (= (length (get-recursive-closure-values v))
		    (length (recursive-closure-variables u-prime)))
		 ;; See the note in new-nonrecursive-closure.
		 (or (eq? *mode* 'abstract)
		     (every (lambda (x v)
			     (prefix-tags? (variable-tags x) (value-tags v)))
			    (recursive-closure-variables u-prime)
			    (get-recursive-closure-values v)))
		 (not (some empty-abstract-value?
			    (get-recursive-closure-values v)))
		 (or (eq? *mode* 'concrete)
		     (every (lambda (x v)
			     (some-value-tags
			      (lambda (tags)
			       (prefix-tags? (variable-tags x) tags)) v))
			    (recursive-closure-variables u-prime)
			    (get-recursive-closure-values v)))
		 (not *frozen?*)))
	       (set-recursive-closure-canonize-cache! u-prime u-prime)
	       (set-recursive-closure-intern-cache! v u-prime)
	       (set-recursive-closure-intern-cache! u-prime u-prime)
	       (map-cps
		loop
		(get-recursive-closure-values v)
		(cons (cons v u-prime) cs)
		(lambda (vs-prime cs)
		 (set! *recursive-closures*
		       (cons u-prime *recursive-closures*))
		 (fill-recursive-closure-values! u-prime vs-prime)
		 (k u-prime cs))))))))
    ((perturbation-tagged-value? v)
     (if (perturbation-tagged-value-intern-cache v)
	 (k (perturbation-tagged-value-intern-cache v) cs)
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *perturbation-tagged-values*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      (let ((u-prime (allocate-perturbation-tagged-value 'unfilled)))
	       (assert (and (not (empty-abstract-value?
				  (get-perturbation-tagged-value-primal v)))
			    (not *frozen?*)))
	       (set-perturbation-tagged-value-canonize-cache! u-prime u-prime)
	       (set-perturbation-tagged-value-intern-cache! v u-prime)
	       (set-perturbation-tagged-value-intern-cache! u-prime u-prime)
	       (loop (get-perturbation-tagged-value-primal v)
		     (cons (cons v u-prime) cs)
		     (lambda (v-prime cs)
		      (set! *perturbation-tagged-values*
			    (cons u-prime *perturbation-tagged-values*))
		      (fill-perturbation-tagged-value-primal! u-prime v-prime)
		      (k u-prime cs))))))))
    ((bundle? v)
     (if (bundle-intern-cache v)
	 (k (bundle-intern-cache v) cs)
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *bundles*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      (let ((u-prime (allocate-bundle 'unfilled 'unfilled)))
	       (assert
		(and
		 (some-bundlable? (get-bundle-primal v) (get-bundle-tangent v))
		 (not (empty-abstract-value? (get-bundle-primal v)))
		 (not (empty-abstract-value? (get-bundle-tangent v)))
		 (not *frozen?*)))
	       (set-bundle-canonize-cache! u-prime u-prime)
	       (set-bundle-intern-cache! v u-prime)
	       (set-bundle-intern-cache! u-prime u-prime)
	       (loop
		(get-bundle-primal v)
		(cons (cons v u-prime) cs)
		(lambda (v-primal-prime cs)
		 (loop (get-bundle-tangent v)
		       cs
		       (lambda (v-tangent-prime cs)
			(set! *bundles* (cons u-prime *bundles*))
			(fill-bundle! u-prime v-primal-prime v-tangent-prime)
			(k u-prime cs))))))))))
    ((sensitivity-tagged-value? v)
     (if (sensitivity-tagged-value-intern-cache v)
	 (k (sensitivity-tagged-value-intern-cache v) cs)
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *sensitivity-tagged-values*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      (let ((u-prime (allocate-sensitivity-tagged-value 'unfilled)))
	       (assert (and (not (empty-abstract-value?
				  (get-sensitivity-tagged-value-primal v)))
			    (not *frozen?*)))
	       (set-sensitivity-tagged-value-canonize-cache! u-prime u-prime)
	       (set-sensitivity-tagged-value-intern-cache! v u-prime)
	       (set-sensitivity-tagged-value-intern-cache! u-prime u-prime)
	       (loop (get-sensitivity-tagged-value-primal v)
		     (cons (cons v u-prime) cs)
		     (lambda (v-prime cs)
		      (set! *sensitivity-tagged-values*
			    (cons u-prime *sensitivity-tagged-values*))
		      (fill-sensitivity-tagged-value-primal! u-prime v-prime)
		      (k u-prime cs))))))))
    ((reverse-tagged-value? v)
     (if (reverse-tagged-value-intern-cache v)
	 (k (reverse-tagged-value-intern-cache v) cs)
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *reverse-tagged-values*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      (let ((u-prime (allocate-reverse-tagged-value 'unfilled)))
	       (assert
		(and
		 (not
		  (empty-abstract-value? (get-reverse-tagged-value-primal v)))
		 (not *frozen?*)))
	       (set-reverse-tagged-value-canonize-cache! u-prime u-prime)
	       (set-reverse-tagged-value-intern-cache! v u-prime)
	       (set-reverse-tagged-value-intern-cache! u-prime u-prime)
	       (loop (get-reverse-tagged-value-primal v)
		     (cons (cons v u-prime) cs)
		     (lambda (v-prime cs)
		      (set! *reverse-tagged-values*
			    (cons u-prime *reverse-tagged-values*))
		      (fill-reverse-tagged-value-primal! u-prime v-prime)
		      (k u-prime cs))))))))
    ((vlad-pair? v)
     (if (vlad-pair-intern-cache v)
	 (k (vlad-pair-intern-cache v) cs)
	 (let ((u-prime (find-if (lambda (u-prime)
				  (filled-deep-abstract-value=? u-prime v))
				 *vlad-pairs*)))
	  (if u-prime
	      (k u-prime (cons (cons v u-prime) cs))
	      (let ((u-prime (allocate-vlad-pair 'unfilled 'unfilled)))
	       (assert (and (not (empty-abstract-value? (vlad-car v)))
			    (not (empty-abstract-value? (vlad-cdr v)))
			    (not *frozen?*)))
	       (set-vlad-pair-canonize-cache! u-prime u-prime)
	       (set-vlad-pair-intern-cache! v u-prime)
	       (set-vlad-pair-intern-cache! u-prime u-prime)
	       (loop
		(vlad-car v)
		(cons (cons v u-prime) cs)
		(lambda (v-car-prime cs)
		 (loop (vlad-cdr v)
		       cs
		       (lambda (v-cdr-prime cs)
			(set! *vlad-pairs* (cons u-prime *vlad-pairs*))
			(fill-vlad-pair! u-prime v-car-prime v-cdr-prime)
			(k u-prime cs))))))))))
    (else (internal-error))))))

(define (canonize-and-maybe-intern-abstract-value v)
 ;; Flow analysis needs both canonized and interned representations. The
 ;; interpreter does not. I'm not sure whether interned representations must
 ;; be canonized. For now, they need not be.
 (let ((v (if *canonized?* (canonize-abstract-value v) v)))
  (if *interned?* (intern-abstract-value v) v)))

;;; Abstract environment equivalence

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
    (let loop ((es '()) (ignore? #f))
     (let ((e (read input-port)))
      (cond
       ((eof-object? e) (reverse es))
       (ignore? (loop es #f))
       ((eq? '===> e) (loop es #t))
       ((and (list? e)
	     (= (length e) 2)
	     (eq? (first e) 'include)
	     (string? (second e)))
	(loop
	 (append (reverse (read-source (search-include-path (second e)))) es) #f))
       (else (loop (cons e es) #f)))))))))

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
 ;; This is now only one of two places where the nondereferenced
 ;; expression-eqv? is used. Here it is only used in an assertion.
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

;;; Concrete->abstract

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
      ((let) (cond ((and (= (length e) 3)
			 (list? (second e))
			 (every (lambda (b) (and (list? b) (= (length b) 2)))
				(second e)))
		    `((lambda ,(map first (second e)) ,(third e))
		      ,@(map second (second e))))
		   ((and (= (length e) 4)
			 (list? (third e))
			 (every (lambda (b) (and (list? b) (= (length b) 2)))
				(third e)))
		    `(letrec ((,(second e)
			       (lambda ,(map first (third e)) ,(fourth e))))
		      (,(second e) ,@(map second (third e)))))
		   (else (compile-time-error "Invalid expression: ~s" e))))
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
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  9
  (let loop ((v v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v)
     (if (union-zero-cache v)
	 (k (union-zero-cache v))
	 ;; widening case H1
	 (let ((v0 (allocate-union 'unfilled)))
	  (set-union-zero-cache! v v0)
	  (set-union-zero-cache! v0 v0)
	  (map-cps-non-cs loop
			  (union-members v)
			  (lambda (us0)
			   (fill-union-values! v0 us0)
			   (k v0))))))
    ((vlad-empty-list? v) (k v))
    ((vlad-true? v) (k v))
    ((vlad-false? v) (k v))
    ;; debugging
    ((vlad-real? v) (if #t (k 0) (k (abstract-real))))
    ((primitive-procedure? v) (k v))
    ((nonrecursive-closure? v)
     (if (nonrecursive-closure-zero-cache v)
	 (k (nonrecursive-closure-zero-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u0 (allocate-nonrecursive-closure
		    'unfilled (nonrecursive-closure-lambda-expression v))))
	  (set-nonrecursive-closure-zero-cache! v u0)
	  (set-nonrecursive-closure-zero-cache! u0 u0)
	  (map-cps-non-cs loop
			  (get-nonrecursive-closure-values v)
			  (lambda (vs0)
			   (fill-nonrecursive-closure-values! u0 vs0)
			   (k u0))))))
    ((recursive-closure? v)
     (if (recursive-closure-zero-cache v)
	 (k (recursive-closure-zero-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u0 (allocate-recursive-closure
		    'unfilled
		    (recursive-closure-procedure-variables v)
		    (recursive-closure-lambda-expressions v)
		    (recursive-closure-index v))))
	  (set-recursive-closure-zero-cache! v u0)
	  (set-recursive-closure-zero-cache! u0 u0)
	  (map-cps-non-cs loop
			  (get-recursive-closure-values v)
			  (lambda (vs0)
			   (fill-recursive-closure-values! u0 vs0)
			   (k u0))))))
    ((perturbation-tagged-value? v)
     (if (perturbation-tagged-value-zero-cache v)
	 (k (perturbation-tagged-value-zero-cache v))
	 (let ((u0 (allocate-perturbation-tagged-value 'unfilled)))
	  (set-perturbation-tagged-value-zero-cache! v u0)
	  (set-perturbation-tagged-value-zero-cache! u0 u0)
	  (loop (get-perturbation-tagged-value-primal v)
		(lambda (v0)
		 (fill-perturbation-tagged-value-primal! u0 v0)
		 (k u0))))))
    ((bundle? v)
     (if (bundle-zero-cache v)
	 (k (bundle-zero-cache v))
	 (let ((u0 (allocate-bundle 'unfilled 'unfilled)))
	  (set-bundle-zero-cache! v u0)
	  (set-bundle-zero-cache! u0 u0)
	  (loop (get-bundle-primal v)
		(lambda (v0-primal)
		 (loop (get-bundle-tangent v)
		       (lambda (v0-tangent)
			(fill-bundle! u0 v0-primal v0-tangent)
			(k u0))))))))
    ((sensitivity-tagged-value? v)
     (if (sensitivity-tagged-value-zero-cache v)
	 (k (sensitivity-tagged-value-zero-cache v))
	 (let ((u0 (allocate-sensitivity-tagged-value 'unfilled)))
	  (set-sensitivity-tagged-value-zero-cache! v u0)
	  (set-sensitivity-tagged-value-zero-cache! u0 u0)
	  (loop (get-sensitivity-tagged-value-primal v)
		(lambda (v0)
		 (fill-sensitivity-tagged-value-primal! u0 v0)
		 (k u0))))))
    ((reverse-tagged-value? v)
     (if (reverse-tagged-value-zero-cache v)
	 (k (reverse-tagged-value-zero-cache v))
	 (let ((u0 (allocate-reverse-tagged-value 'unfilled)))
	  (set-reverse-tagged-value-zero-cache! v u0)
	  (set-reverse-tagged-value-zero-cache! u0 u0)
	  (loop (get-reverse-tagged-value-primal v)
		(lambda (v0)
		 (fill-reverse-tagged-value-primal! u0 v0)
		 (k u0))))))
    ((vlad-pair? v)
     (if (vlad-pair-zero-cache v)
	 (k (vlad-pair-zero-cache v))
	 (let ((u0 (allocate-vlad-pair 'unfilled 'unfilled)))
	  (set-vlad-pair-zero-cache! v u0)
	  (set-vlad-pair-zero-cache! u0 u0)
	  (loop (vlad-car v)
		(lambda (v0-car)
		 (loop (vlad-cdr v)
		       (lambda (v0-cdr)
			(fill-vlad-pair! u0 v0-car v0-cdr)
			(k u0))))))))
    (else (internal-error))))))

;;; Forward mode

(define (perturbation-transform e)
 (define (loop e)
  (cond ((constant-expression? e)
	 (with-concrete
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
    (with-concrete
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
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 (time-it-bucket
  10
  (let loop ((v v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v)
     (if (perturb-cache v)
	 (k (perturb-cache v))
	 ;; widening case H2
	 (let ((v-perturbation (allocate-union 'unfilled)))
	  (set-unperturb-cache! v-perturbation v)
	  (set-perturb-cache! v v-perturbation)
	  (map-cps-non-cs loop
			  (union-members v)
			  (lambda (us-perturbation)
			   (fill-union-values! v-perturbation us-perturbation)
			   (k v-perturbation))))))
    ((or (vlad-empty-list? v)
	 (vlad-true? v)
	 (vlad-false? v)
	 (vlad-real? v)
	 (primitive-procedure? v))
     (k (new-perturbation-tagged-value v)))
    ((nonrecursive-closure? v)
     (if (perturb-cache v)
	 (k (perturb-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-perturbation
		(allocate-nonrecursive-closure
		 'unfilled
		 (perturbation-transform
		  (nonrecursive-closure-lambda-expression v)))))
	  (set-unperturb-cache! u-perturbation v)
	  (set-perturb-cache! v u-perturbation)
	  (map-cps-non-cs
	   loop
	   (get-nonrecursive-closure-values v)
	   (lambda (vs-perturbation)
	    (fill-nonrecursive-closure-values! u-perturbation vs-perturbation)
	    (k u-perturbation))))))
    ((recursive-closure? v)
     (if (perturb-cache v)
	 (k (perturb-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-perturbation
		(allocate-recursive-closure
		 'unfilled
		 (map-vector perturbationify
			     (recursive-closure-procedure-variables v))
		 (map-vector perturbation-transform
			     (recursive-closure-lambda-expressions v))
		 (recursive-closure-index v))))
	  (set-unperturb-cache! u-perturbation v)
	  (set-perturb-cache! v u-perturbation)
	  (map-cps-non-cs
	   loop
	   (get-recursive-closure-values v)
	   (lambda (vs-perturbation)
	    (fill-recursive-closure-values! u-perturbation vs-perturbation)
	    (k u-perturbation))))))
    ((or (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v)
	 (vlad-pair? v))
     (if (perturb-cache v)
	 (k (perturb-cache v))
	 (let ((u-perturbation (create-perturbation-tagged-value v)))
	  (set-perturb-cache! v u-perturbation)
	  (k u-perturbation))))
    (else (internal-error))))))

(define (unperturb v-perturbation)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v-perturbation)
  (check-intern-cache! v-perturbation)
  (check-interned! v-perturbation))
 (time-it-bucket
  11
  (let loop ((v-perturbation v-perturbation)
	     (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v-perturbation)
     (if (unperturb-cache v-perturbation)
	 (k (unperturb-cache v-perturbation))
	 ;; widening case H3
	 (let ((v (allocate-union 'unfilled)))
	  (set-perturb-cache! v v-perturbation)
	  (set-unperturb-cache! v-perturbation v)
	  (map-cps-non-cs loop
			  (union-members v-perturbation)
			  (lambda (us)
			   (fill-union-values! v us)
			   (k v))))))
    ((or (vlad-empty-list? v-perturbation)
	 (vlad-true? v-perturbation)
	 (vlad-false? v-perturbation)
	 (vlad-real? v-perturbation)
	 (primitive-procedure? v-perturbation)
	 (bundle? v-perturbation)
	 (sensitivity-tagged-value? v-perturbation)
	 (reverse-tagged-value? v-perturbation)
	 (vlad-pair? v-perturbation))
     (k (ad-error "Argument to unperturb ~a a perturbation value"
		  v-perturbation)))
    ((nonrecursive-closure? v-perturbation)
     (cond
      ((unperturb-cache v-perturbation) (k (unperturb-cache v-perturbation)))
      ((tagged? 'perturbation (nonrecursive-closure-tags v-perturbation))
       ;; See the note in abstract-environment=?.
       (let ((u (allocate-nonrecursive-closure
		 'unfilled
		 (perturbation-transform-inverse
		  (nonrecursive-closure-lambda-expression v-perturbation)))))
	(set-perturb-cache! u v-perturbation)
	(set-unperturb-cache! v-perturbation u)
	(map-cps-non-cs loop
			(get-nonrecursive-closure-values v-perturbation)
			(lambda (vs)
			 (fill-nonrecursive-closure-values! u vs)
			 (k u)))))
      (else (k (ad-error "Argument to unperturb ~a a perturbation value"
			 v-perturbation)))))
    ((recursive-closure? v-perturbation)
     (cond
      ((unperturb-cache v-perturbation) (k (unperturb-cache v-perturbation)))
      ((tagged? 'perturbation (recursive-closure-tags v-perturbation))
       ;; See the note in abstract-environment=?.
       (let ((u (allocate-recursive-closure
		 'unfilled
		 (map-vector
		  unperturbationify
		  (recursive-closure-procedure-variables v-perturbation))
		 (map-vector
		  perturbation-transform-inverse
		  (recursive-closure-lambda-expressions v-perturbation))
		 (recursive-closure-index v-perturbation))))
	(set-perturb-cache! u v-perturbation)
	(set-unperturb-cache! v-perturbation u)
	(map-cps-non-cs loop
			(get-recursive-closure-values v-perturbation)
			(lambda (vs)
			 (fill-recursive-closure-values! u vs)
			 (k u)))))
      (else (k (ad-error "Argument to unperturb ~a a perturbation value"
			 v-perturbation)))))
    ((perturbation-tagged-value? v-perturbation)
     (k (get-perturbation-tagged-value-primal v-perturbation)))
    (else (internal-error))))))

(define (primal v-forward)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v-forward)
  (check-intern-cache! v-forward)
  (check-interned! v-forward))
 (time-it-bucket
  12
  (let loop ((v-forward v-forward)
	     (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v-forward)
     (if (primal-cache v-forward)
	 (k (primal-cache v-forward))
	 ;; widening case H4
	 (let ((v (allocate-union 'unfilled)))
	  (set-primal-cache! v-forward v)
	  (map-cps-non-cs loop
			  (union-members v-forward)
			  (lambda (us)
			   (fill-union-values! v us)
			   (k v))))))
    ((or (vlad-empty-list? v-forward)
	 (vlad-true? v-forward)
	 (vlad-false? v-forward)
	 (vlad-real? v-forward)
	 (primitive-procedure? v-forward)
	 (perturbation-tagged-value? v-forward)
	 (sensitivity-tagged-value? v-forward)
	 (reverse-tagged-value? v-forward)
	 (vlad-pair? v-forward))
     (k (ad-error "Argument to primal ~a a forward value" v-forward)))
    ((nonrecursive-closure? v-forward)
     (if (primal-cache v-forward)
	 (k (primal-cache v-forward))
	 (let ((b (find-if
		   (lambda (b)
		    (deep-abstract-value=?
		     v-forward
		     (primitive-procedure-forward (value-binding-value b))))
		   *value-bindings*)))
	  (cond
	   (b (let ((u (value-binding-value b)))
	       (set-primal-cache! v-forward u)
	       (k u)))
	   ((tagged? 'forward (nonrecursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-nonrecursive-closure
		      'unfilled
		      (forward-transform-inverse
		       (nonrecursive-closure-lambda-expression v-forward)))))
	     (set-primal-cache! v-forward u)
	     (map-cps-non-cs loop
			     (get-nonrecursive-closure-values v-forward)
			     (lambda (vs)
			      (fill-nonrecursive-closure-values! u vs)
			      (k u)))))
	   (else (k (ad-error "Argument to primal ~a a forward value"
			      v-forward)))))))
    ((recursive-closure? v-forward)
     (cond ((primal-cache v-forward) (k (primal-cache v-forward)))
	   ((tagged? 'forward (recursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-recursive-closure
		      'unfilled
		      (map-vector
		       unforwardify
		       (recursive-closure-procedure-variables v-forward))
		      (map-vector
		       forward-transform-inverse
		       (recursive-closure-lambda-expressions v-forward))
		      (recursive-closure-index v-forward))))
	     (set-primal-cache! v-forward u)
	     (map-cps-non-cs loop
			     (get-recursive-closure-values v-forward)
			     (lambda (vs)
			      (fill-recursive-closure-values! u vs)
			      (k u)))))
	   (else (k (ad-error "Argument to primal ~a a forward value"
			      v-forward)))))
    ((bundle? v-forward) (k (get-bundle-primal v-forward)))
    (else (internal-error))))))

(define (tangent v-forward)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v-forward)
  (check-intern-cache! v-forward)
  (check-interned! v-forward))
 (time-it-bucket
  13
  (let loop ((v-forward v-forward)
	     (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v-forward)
     (if (tangent-cache v-forward)
	 (k (tangent-cache v-forward))
	 ;; widening case H5
	 (let ((v-perturbation (allocate-union 'unfilled)))
	  (set-tangent-cache! v-forward v-perturbation)
	  (map-cps-non-cs loop
			  (union-members v-forward)
			  (lambda (us-perturbation)
			   (fill-union-values! v-perturbation us-perturbation)
			   (k v-perturbation))))))
    ((or (vlad-empty-list? v-forward)
	 (vlad-true? v-forward)
	 (vlad-false? v-forward)
	 (vlad-real? v-forward)
	 (primitive-procedure? v-forward)
	 (perturbation-tagged-value? v-forward)
	 (sensitivity-tagged-value? v-forward)
	 (reverse-tagged-value? v-forward)
	 (vlad-pair? v-forward))
     (k (ad-error "Argument to tangent ~a a forward value" v-forward)))
    ((nonrecursive-closure? v-forward)
     (if (tangent-cache v-forward)
	 (k (tangent-cache v-forward))
	 (let ((b (find-if
		   (lambda (b)
		    (deep-abstract-value=?
		     v-forward
		     (primitive-procedure-forward (value-binding-value b))))
		   *value-bindings*)))
	  (cond
	   (b (let ((u-perturbation (perturb (value-binding-value b))))
	       (set-tangent-cache! v-forward u-perturbation)
	       (k u-perturbation)))
	   ((tagged? 'forward (nonrecursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (let ((u-perturbation
		   (allocate-nonrecursive-closure
		    'unfilled
		    (perturbation-transform
		     (forward-transform-inverse
		      (nonrecursive-closure-lambda-expression v-forward))))))
	     (set-tangent-cache! v-forward u-perturbation)
	     (map-cps-non-cs loop
			     (get-nonrecursive-closure-values v-forward)
			     (lambda (vs-perturbation)
			      (fill-nonrecursive-closure-values!
			       u-perturbation vs-perturbation)
			      (k u-perturbation)))))
	   (else (k (ad-error "Argument to tangent ~a a forward value"
			      v-forward)))))))
    ((recursive-closure? v-forward)
     (cond ((tangent-cache v-forward) (k (tangent-cache v-forward)))
	   ((tagged? 'forward (recursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (let ((u-perturbation
		   (allocate-recursive-closure
		    'unfilled
		    (map-vector
		     (lambda (x) (perturbationify (unforwardify x)))
		     (recursive-closure-procedure-variables v-forward))
		    (map-vector
		     (lambda (e)
		      (perturbation-transform (forward-transform-inverse e)))
		     (recursive-closure-lambda-expressions v-forward))
		    (recursive-closure-index v-forward))))
	     (set-tangent-cache! v-forward u-perturbation)
	     (map-cps-non-cs loop
			     (get-recursive-closure-values v-forward)
			     (lambda (vs-perturbation)
			      (fill-recursive-closure-values!
			       u-perturbation vs-perturbation)
			      (k u-perturbation)))))
	   (else (k (ad-error "Argument to tangent ~a a forward value"
			      v-forward)))))
    ((bundle? v-forward) (k (get-bundle-tangent v-forward)))
    (else (internal-error))))))

(define (bundle v)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 ;; needs work: Throughout the following can mutually narrow v and
 ;;             v-perturbation when creating a bundle to those elements that
 ;;             mututally bundlable with the corresponding elements of the
 ;;             other.
 (time-it-bucket
  14
  ;; needs work: v0 naming convention
  (let loop ((v0 v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v0)
     (if (union-bundle-cache v0)
	 (k (union-bundle-cache v0))
	 ;; widening case H6
	 (let ((v-forward (allocate-union 'unfilled)))
	  (set-union-bundle-cache! v0 v-forward)
	  (map-cps-non-cs loop
			  (union-members v0)
			  (lambda (us-forward)
			   (fill-union-values! v-forward us-forward)
			   (k v-forward))))))
    ((vlad-pair? v0)
     (if (vlad-pair-bundle-cache v0)
	 (k (vlad-pair-bundle-cache v0))
	 (let ((v (vlad-car v0)) (v-perturbation (vlad-cdr v0)))
	  (cond
	   ((union? v)
	    ;; widening case H7
	    (let ((v-forward (allocate-union 'unfilled)))
	     (set-vlad-pair-bundle-cache! v0 v-forward)
	     (map-cps-non-cs
	      (lambda (u k) (loop (vlad-cons u v-perturbation) k))
	      (union-members v)
	      (lambda (us-forward)
	       (fill-union-values! v-forward us-forward)
	       (k v-forward)))))
	   ((union? v-perturbation)
	    ;; widening case H8
	    (let ((v-forward (allocate-union 'unfilled)))
	     (set-vlad-pair-bundle-cache! v0 v-forward)
	     (map-cps-non-cs (lambda (u-perturbation k)
			      (loop (vlad-cons v u-perturbation) k))
			     (union-members v-perturbation)
			     (lambda (us-forward)
			      (fill-union-values! v-forward us-forward)
			      (k v-forward)))))
	   ((and (or (vlad-empty-list? v)
		     (vlad-true? v)
		     (vlad-false? v)
		     (vlad-real? v)
		     (perturbation-tagged-value? v)
		     (bundle? v)
		     (sensitivity-tagged-value? v)
		     (reverse-tagged-value? v)
		     (vlad-pair? v))
		 (some-bundlable? v v-perturbation))
	    (unless (every-bundlable? v v-perturbation)
	     (ad-warning
	      "Arguments to bundle might not conform" v v-perturbation))
	    (let ((u-forward (new-bundle v v-perturbation)))
	     (set-vlad-pair-bundle-cache! v0 u-forward)
	     (k u-forward)))
	   ((and (primitive-procedure? v) (some-bundlable? v v-perturbation))
	    (unless (every-bundlable? v v-perturbation)
	     (ad-warning
	      "Arguments to bundle might not conform" v v-perturbation))
	    (let ((u-forward (primitive-procedure-forward v)))
	     (set-vlad-pair-bundle-cache! v0 u-forward)
	     (k u-forward)))
	   ((and (nonrecursive-closure? v)
		 (nonrecursive-closure? v-perturbation)
		 (perturbation-parameter?
		  (nonrecursive-closure-parameter v-perturbation))
		 (nonrecursive-closure-match? v (unperturb v-perturbation)))
	    ;; See the note in abstract-environment=?.
	    (let ((u-forward (allocate-nonrecursive-closure
			      'unfilled
			      (forward-transform
			       (nonrecursive-closure-lambda-expression v)))))
	     (set-primal-cache! u-forward v)
	     (set-tangent-cache! u-forward v-perturbation)
	     (set-vlad-pair-bundle-cache! v0 u-forward)
	     (map2-cps-non-cs
	      (lambda (v v-perturbation k)
	       (loop (vlad-cons v v-perturbation) k))
	      (get-nonrecursive-closure-values v)
	      (get-nonrecursive-closure-values v-perturbation)
	      (lambda (vs-forward)
	       (fill-nonrecursive-closure-values! u-forward vs-forward)
	       (k u-forward)))))
	   ((and (recursive-closure? v)
		 (recursive-closure? v-perturbation)
		 (perturbation-parameter?
		  (recursive-closure-parameter v-perturbation))
		 (recursive-closure-match? v (unperturb v-perturbation)))
	    ;; See the note in abstract-environment=?.
	    (let ((u-forward
		   (allocate-recursive-closure
		    'unfilled
		    (map-vector forwardify
				(recursive-closure-procedure-variables v))
		    (map-vector forward-transform
				(recursive-closure-lambda-expressions v))
		    (recursive-closure-index v))))
	     (set-primal-cache! u-forward v)
	     (set-tangent-cache! u-forward v-perturbation)
	     (set-vlad-pair-bundle-cache! v0 u-forward)
	     (map2-cps-non-cs
	      (lambda (v v-perturbation k)
	       (loop (vlad-cons v v-perturbation) k))
	      (get-recursive-closure-values v)
	      (get-recursive-closure-values v-perturbation)
	      (lambda (vs-forward)
	       (fill-recursive-closure-values! u-forward vs-forward)
	       (k u-forward)))))
	   (else (case *mode*
		  ((concrete)
		   (run-time-error "Arguments to bundle do not conform"
				   v
				   v-perturbation))
		  ((abstract)
		   (let ((u-forward (compile-time-warning
				     "Arguments to bundle might not conform"
				     v
				     v-perturbation)))
		    (set-vlad-pair-bundle-cache! v0 u-forward)
		    (k u-forward)))
		  (else (internal-error))))))))
    (else (k (ad-error "Argument to bundle ~a valid" v0)))))))

(define (j* v) (bundle (vlad-cons v (zero (perturb v)))))

;;; Reverse mode

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
   (with-concrete
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
		 (with-concrete
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
		      (with-concrete
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
			  (make-zero
			   (make-sensitize
			    (make-*j-inverse (reverse-access x))))))
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
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 (time-it-bucket
  15
  (let loop ((v v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v)
     (if (union-sensitize-cache v)
	 (k (union-sensitize-cache v))
	 ;; widening case H10
	 (let ((v-sensitivity (allocate-union 'unfilled)))
	  (set-union-unsensitize-cache! v-sensitivity v)
	  (set-union-sensitize-cache! v v-sensitivity)
	  (map-cps-non-cs loop
			  (union-members v)
			  (lambda (us-sensitivity)
			   (fill-union-values! v-sensitivity us-sensitivity)
			   (k v-sensitivity))))))
    ((or (vlad-empty-list? v)
	 (vlad-true? v)
	 (vlad-false? v)
	 (vlad-real? v)
	 (primitive-procedure? v))
     (k (new-sensitivity-tagged-value v)))
    ((nonrecursive-closure? v)
     (if (nonrecursive-closure-sensitize-cache v)
	 (k (nonrecursive-closure-sensitize-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-sensitivity (allocate-nonrecursive-closure
			       'unfilled
			       (sensitivity-transform
				(nonrecursive-closure-lambda-expression v)))))
	  (set-nonrecursive-closure-unsensitize-cache! u-sensitivity v)
	  (set-nonrecursive-closure-sensitize-cache! v u-sensitivity)
	  (map-cps-non-cs
	   loop
	   (get-nonrecursive-closure-values v)
	   (lambda (vs-sensitivity)
	    (fill-nonrecursive-closure-values! u-sensitivity vs-sensitivity)
	    (k u-sensitivity))))))
    ((recursive-closure? v)
     (if (recursive-closure-sensitize-cache v)
	 (k (recursive-closure-sensitize-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-sensitivity
		(allocate-recursive-closure
		 'unfilled
		 (map-vector sensitivityify
			     (recursive-closure-procedure-variables v))
		 (map-vector sensitivity-transform
			     (recursive-closure-lambda-expressions v))
		 (recursive-closure-index v))))
	  (set-recursive-closure-unsensitize-cache! u-sensitivity v)
	  (set-recursive-closure-sensitize-cache! v u-sensitivity)
	  (map-cps-non-cs
	   loop
	   (get-recursive-closure-values v)
	   (lambda (vs-sensitivity)
	    (fill-recursive-closure-values! u-sensitivity vs-sensitivity)
	    (k u-sensitivity))))))
    ((or (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v)
	 (vlad-pair? v))
     (if (sensitize-cache v)
	 (k (sensitize-cache v))
	 (let ((u-sensitivity (create-sensitivity-tagged-value v)))
	  (set-sensitize-cache! v u-sensitivity)
	  (k u-sensitivity))))
    (else (internal-error))))))

(define (unsensitize? v-sensitivity)
 ;; This is written in CPS so as not to break structure sharing.
 ;; Unlike the other AD primitives, v-sensitivity might not be canonized or
 ;; interned because canonize-abstract-values calls
 ;; abstract-value-union-internal which calls backpropagator? which calls
 ;; unsensitize?.
 (time-it-bucket
  16
  (let loop ((v-sensitivity v-sensitivity) (cs '()) (k (lambda (r? cs) r?)))
   (let ((found? (memq v-sensitivity cs)))
    (cond
     (found? (k #t cs))
     ((union? v-sensitivity)
      (if (union-unsensitize-cache v-sensitivity)
	  (k #t cs)
	  (every-cps
	   loop (union-members v-sensitivity) (cons v-sensitivity cs) k)))
     ((or (vlad-empty-list? v-sensitivity)
	  (vlad-true? v-sensitivity)
	  (vlad-false? v-sensitivity)
	  (vlad-real? v-sensitivity)
	  (primitive-procedure? v-sensitivity)
	  (perturbation-tagged-value? v-sensitivity)
	  (bundle? v-sensitivity)
	  (reverse-tagged-value? v-sensitivity)
	  (vlad-pair? v-sensitivity))
      (k #f cs))
     ((nonrecursive-closure? v-sensitivity)
      (cond
       ((nonrecursive-closure-unsensitize-cache v-sensitivity) (k #t cs))
       ((and (tagged? 'sensitivity (nonrecursive-closure-tags v-sensitivity))
	     (sensitivity-transform-inverse?
	      (nonrecursive-closure-lambda-expression v-sensitivity)))
	;; See the note in abstract-environment=?.
	(every-cps loop
		   (get-nonrecursive-closure-values v-sensitivity)
		   (cons v-sensitivity cs)
		   k))
       (else (k #f cs))))
     ((recursive-closure? v-sensitivity)
      (cond
       ((recursive-closure-unsensitize-cache v-sensitivity) (k #t cs))
       ((and
	 (tagged? 'sensitivity (recursive-closure-tags v-sensitivity))
	 (every-vector unsensitivityify?
		       (recursive-closure-procedure-variables v-sensitivity))
	 (every-vector sensitivity-transform-inverse?
		       (recursive-closure-lambda-expressions v-sensitivity)))
	;; See the note in abstract-environment=?.
	(every-cps loop
		   (get-recursive-closure-values v-sensitivity)
		   (cons v-sensitivity cs)
		   k))
       (else (k #f cs))))
     ((sensitivity-tagged-value? v-sensitivity) (k #t (cons v-sensitivity cs)))
     (else (internal-error)))))))

(define (unsensitize v-sensitivity)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v-sensitivity)
  (check-intern-cache! v-sensitivity)
  (check-interned! v-sensitivity))
 (time-it-bucket
  17
  (let loop ((v-sensitivity v-sensitivity)
	     (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v-sensitivity)
     (if (union-unsensitize-cache v-sensitivity)
	 (k (union-unsensitize-cache v-sensitivity))
	 ;; widening case H11
	 (let ((v (allocate-union 'unfilled)))
	  (set-union-sensitize-cache! v v-sensitivity)
	  (set-union-unsensitize-cache! v-sensitivity v)
	  (map-cps-non-cs loop
			  (union-members v-sensitivity)
			  (lambda (us)
			   (fill-union-values! v us)
			   (k v))))))
    ((or (vlad-empty-list? v-sensitivity)
	 (vlad-true? v-sensitivity)
	 (vlad-false? v-sensitivity)
	 (vlad-real? v-sensitivity)
	 (primitive-procedure? v-sensitivity)
	 (perturbation-tagged-value? v-sensitivity)
	 (bundle? v-sensitivity)
	 (reverse-tagged-value? v-sensitivity)
	 (vlad-pair? v-sensitivity))
     (k (ad-error "Argument to unsensitize ~a a sensitivity value"
		  v-sensitivity)))
    ((nonrecursive-closure? v-sensitivity)
     (cond
      ((nonrecursive-closure-unsensitize-cache v-sensitivity)
       (k (nonrecursive-closure-unsensitize-cache v-sensitivity)))
      ((and (tagged? 'sensitivity (nonrecursive-closure-tags v-sensitivity))
	    (sensitivity-transform-inverse?
	     (nonrecursive-closure-lambda-expression v-sensitivity)))
       ;; See the note in abstract-environment=?.
       (let ((u (allocate-nonrecursive-closure
		 'unfilled
		 (sensitivity-transform-inverse
		  (nonrecursive-closure-lambda-expression v-sensitivity)))))
	(set-nonrecursive-closure-sensitize-cache! u v-sensitivity)
	(set-nonrecursive-closure-unsensitize-cache! v-sensitivity u)
	(map-cps-non-cs loop
			(get-nonrecursive-closure-values v-sensitivity)
			(lambda (vs)
			 (fill-nonrecursive-closure-values! u vs)
			 (k u)))))
      (else (k (ad-error "Argument to unsensitize ~a a sensitivity value"
			 v-sensitivity)))))
    ((recursive-closure? v-sensitivity)
     (cond
      ((recursive-closure-unsensitize-cache v-sensitivity)
       (k (recursive-closure-unsensitize-cache v-sensitivity)))
      ((and
	(tagged? 'sensitivity (recursive-closure-tags v-sensitivity))
	(every-vector unsensitivityify?
		      (recursive-closure-procedure-variables v-sensitivity))
	(every-vector sensitivity-transform-inverse?
		      (recursive-closure-lambda-expressions v-sensitivity)))
       ;; See the note in abstract-environment=?.
       (let ((u (allocate-recursive-closure
		 'unfilled
		 (map-vector
		  unsensitivityify
		  (recursive-closure-procedure-variables v-sensitivity))
		 (map-vector
		  sensitivity-transform-inverse
		  (recursive-closure-lambda-expressions v-sensitivity))
		 (recursive-closure-index v-sensitivity))))
	(set-recursive-closure-sensitize-cache! u v-sensitivity)
	(set-recursive-closure-unsensitize-cache! v-sensitivity u)
	(map-cps-non-cs loop
			(get-recursive-closure-values v-sensitivity)
			(lambda (vs)
			 (fill-recursive-closure-values! u vs)
			 (k u)))))
      (else (k (ad-error "Argument to unsensitize ~a a sensitivity value"
			 v-sensitivity)))))
    ((sensitivity-tagged-value? v-sensitivity)
     (k (get-sensitivity-tagged-value-primal v-sensitivity)))
    (else (internal-error))))))

(define (is-zero? v)
 ;; A false return value doesn't mean that v is nonzero, it just means that it
 ;; wasn't produced by the zero procedure. It might just happen to be a zero.
 (and
  ;; debugging
  #f
  (or
   (and (union? v) (eq? (union-zero-cache v) v))
   (vlad-empty-list? v)
   (vlad-true? v)
   (vlad-false? v)
   (and (real? v) (zero? v))
   (primitive-procedure? v)
   (and (nonrecursive-closure? v) (eq? (nonrecursive-closure-zero-cache v) v))
   (and (recursive-closure? v) (eq? (recursive-closure-zero-cache v) v))
   (and (perturbation-tagged-value? v)
	(eq? (perturbation-tagged-value-zero-cache v) v))
   (and (bundle? v) (eq? (bundle-zero-cache v) v))
   (and (sensitivity-tagged-value? v)
	(eq? (sensitivity-tagged-value-zero-cache v) v))
   (and (reverse-tagged-value? v) (eq? (reverse-tagged-value-zero-cache v) v))
   (and (vlad-pair? v) (eq? (vlad-pair-zero-cache v) v)))))

(define (plus v)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 (time-it-bucket
  18
  ;; needs work: v0 naming convention
  (let loop ((v0 v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v0)
     (if (union-plus-cache v0)
	 (k (union-plus-cache v0))
	 ;; widening case H12
	 (let ((v (allocate-union 'unfilled)))
	  (set-union-plus-cache! v0 v)
	  (map-cps-non-cs loop
			  (union-members v0)
			  (lambda (us)
			   (fill-union-values! v us)
			   (k v))))))
    ((vlad-pair? v0)
     (if (vlad-pair-plus-cache v0)
	 (k (vlad-pair-plus-cache v0))
	 (let ((v1 (vlad-car v0)) (v2 (vlad-cdr v0)))
	  (cond
	   ;; needs work: The following two don't check conformance.
	   ((is-zero? v1)
	    (set-vlad-pair-plus-cache! v0 v2)
	    (k v2))
	   ((is-zero? v2)
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ;; widening case H13
	   ((union? v1)
	    (let ((v (allocate-union 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 v)
	     (map-cps-non-cs (lambda (u1 k) (loop (vlad-cons u1 v2) k))
			     (union-members v1)
			     (lambda (us)
			      (fill-union-values! v us)
			      (k v)))))
	   ;; widening case H14
	   ;; There is no widening case H15
	   ((union? v2)
	    (let ((v (allocate-union 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 v)
	     (map-cps-non-cs (lambda (u2 k) (loop (vlad-cons v1 u2) k))
			     (union-members v2)
			     (lambda (us)
			      (fill-union-values! v us)
			      (k v)))))
	   ((and (vlad-empty-list? v1) (vlad-empty-list? v2))
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ((and (vlad-true? v1) (vlad-true? v2))
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ((and (vlad-false? v1) (vlad-false? v2))
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ((and (abstract-real? v1) (vlad-real? v2))
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ((and (vlad-real? v1) (abstract-real? v2))
	    (set-vlad-pair-plus-cache! v0 v2)
	    (k v2))
	   ((and (real? v1) (real? v2))
	    (let ((u (+ v1 v2)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (k u)))
	   ((and
	     (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
	    (set-vlad-pair-plus-cache! v0 v1)
	    (k v1))
	   ((and (nonrecursive-closure? v1)
		 (nonrecursive-closure? v2)
		 (nonrecursive-closure-match? v1 v2))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-nonrecursive-closure
		      'unfilled (nonrecursive-closure-lambda-expression v1))))
	     (set-vlad-pair-plus-cache! v0 u)
	     (map2-cps-non-cs (lambda (v1 v2 k) (loop (vlad-cons v1 v2) k))
			      (get-nonrecursive-closure-values v1)
			      (get-nonrecursive-closure-values v2)
			      (lambda (vs)
			       (fill-nonrecursive-closure-values! u vs)
			       (k u)))))
	   ((and (recursive-closure? v1)
		 (recursive-closure? v2)
		 (recursive-closure-match? v1 v2))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-recursive-closure
		      'unfilled
		      (recursive-closure-procedure-variables v1)
		      (recursive-closure-lambda-expressions v1)
		      (recursive-closure-index v1))))
	     (set-vlad-pair-plus-cache! v0 u)
	     (map2-cps-non-cs (lambda (v1 v2 k) (loop (vlad-cons v1 v2) k))
			      (get-recursive-closure-values v1)
			      (get-recursive-closure-values v2)
			      (lambda (vs)
			       (fill-recursive-closure-values! u vs)
			       (k u)))))
	   ((and
	     (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	    (let ((u (allocate-perturbation-tagged-value 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (loop (vlad-cons (get-perturbation-tagged-value-primal v1)
			      (get-perturbation-tagged-value-primal v2))
		   (lambda (v)
		    (fill-perturbation-tagged-value-primal! u v)
		    (k u)))))
	   ((and (bundle? v1) (bundle? v2))
	    (let ((u (allocate-bundle 'unfilled 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (loop (vlad-cons (get-bundle-primal v1)
			      (get-bundle-primal v2))
		   (lambda (v-primal)
		    (loop (vlad-cons (get-bundle-tangent v1)
				     (get-bundle-tangent v2))
			  (lambda (v-tangent)
			   (fill-bundle! u v-primal v-tangent)
			   (k u)))))))
	   ((and (sensitivity-tagged-value? v1)
		 (sensitivity-tagged-value? v2))
	    (let ((u (allocate-sensitivity-tagged-value 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (loop (vlad-cons (get-sensitivity-tagged-value-primal v1)
			      (get-sensitivity-tagged-value-primal v2))
		   (lambda (v)
		    (fill-sensitivity-tagged-value-primal! u v)
		    (k u)))))
	   ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	    (let ((u (allocate-reverse-tagged-value 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (loop (vlad-cons (get-reverse-tagged-value-primal v1)
			      (get-reverse-tagged-value-primal v2))
		   (lambda (v)
		    (fill-reverse-tagged-value-primal! u v)
		    (k u)))))
	   ((and (vlad-pair? v1) (vlad-pair? v2))
	    (let ((u (allocate-vlad-pair 'unfilled 'unfilled)))
	     (set-vlad-pair-plus-cache! v0 u)
	     (loop (vlad-cons (vlad-car v1) (vlad-car v2))
		   (lambda (v-car)
		    (loop (vlad-cons (vlad-cdr v1) (vlad-cdr v2))
			  (lambda (v-cdr)
			   (fill-vlad-pair! u v-car v-cdr)
			   (k u)))))))
	   (else (case *mode*
		  ((concrete)
		   (run-time-error "Arguments to plus do not conform" v1 v2))
		  ((abstract)
		   (let ((u (compile-time-warning
			     "Arguments to plus might not conform" v1 v2)))
		    (set-vlad-pair-plus-cache! v0 u)
		    (k u)))
		  (else (internal-error))))))))
    (else (k (ad-error "Argument to plus ~a valid" v0)))))))

(define (*j v)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v)
  (check-intern-cache! v)
  (check-interned! v))
 (time-it-bucket
  19
  (let loop ((v v) (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v)
     (if (*j-cache v)
	 (k (*j-cache v))
	 ;; widening case H16
	 (let ((v-reverse (allocate-union 'unfilled)))
	  (set-union-*j-inverse-cache! v-reverse v)
	  (set-*j-cache! v v-reverse)
	  (map-cps-non-cs loop
			  (union-members v)
			  (lambda (us-reverse)
			   (fill-union-values! v-reverse us-reverse)
			   (k v-reverse))))))
    ((or (vlad-empty-list? v)
	 (vlad-true? v)
	 (vlad-false? v)
	 (vlad-real? v))
     (k (new-reverse-tagged-value v)))
    ((primitive-procedure? v) (k (primitive-procedure-reverse v)))
    ((nonrecursive-closure? v)
     (if (*j-cache v)
	 (k (*j-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-reverse
		(allocate-nonrecursive-closure
		 'unfilled
		 (reverse-transform
		  (nonrecursive-closure-lambda-expression v)))))
	  (set-nonrecursive-closure-*j-inverse-cache! u-reverse v)
	  (set-*j-cache! v u-reverse)
	  (map-cps-non-cs
	   loop
	   (get-nonrecursive-closure-values v)
	   (lambda (vs-reverse)
	    (fill-nonrecursive-closure-values! u-reverse vs-reverse)
	    (k u-reverse))))))
    ((recursive-closure? v)
     (if (*j-cache v)
	 (k (*j-cache v))
	 ;; See the note in abstract-environment=?.
	 (let ((u-reverse
		(allocate-recursive-closure
		 'unfilled
		 (map-vector
		  reverseify (recursive-closure-procedure-variables v))
		 (map-n-vector
		  (lambda (i)
		   (reverse-transform-internal
		    (vector-ref (recursive-closure-lambda-expressions v) i)
		    (vector->list (recursive-closure-procedure-variables v))
		    (vector->list (recursive-closure-lambda-expressions v))
		    i))
		  (vector-length (recursive-closure-lambda-expressions v)))
		 (recursive-closure-index v))))
	  (set-recursive-closure-*j-inverse-cache! u-reverse v)
	  (set-*j-cache! v u-reverse)
	  (map-cps-non-cs
	   loop
	   (get-recursive-closure-values v)
	   (lambda (vs-reverse)
	    (fill-recursive-closure-values! u-reverse vs-reverse)
	    (k u-reverse))))))
    ((or (perturbation-tagged-value? v)
	 (bundle? v)
	 (sensitivity-tagged-value? v)
	 (reverse-tagged-value? v)
	 (vlad-pair? v))
     (if (*j-cache v)
	 (k (*j-cache v))
	 (let ((u-reverse (create-reverse-tagged-value v)))
	  (set-*j-cache! v u-reverse)
	  (k u-reverse))))
    (else (internal-error))))))

(define (*j-inverse v-reverse)
 ;; This is written in CPS so as not to break structure sharing.
 (when (and *expensive-checks?* *interned?*)
  (check-canonize-cache! v-reverse)
  (check-intern-cache! v-reverse)
  (check-interned! v-reverse))
 (time-it-bucket
  20
  (let loop ((v-reverse v-reverse)
	     (k canonize-and-maybe-intern-abstract-value))
   (cond
    ((union? v-reverse)
     (if (union-*j-inverse-cache v-reverse)
	 (k (union-*j-inverse-cache v-reverse))
	 ;; widening case H17
	 (let ((v (allocate-union 'unfilled)))
	  (set-*j-cache! v v-reverse)
	  (set-union-*j-inverse-cache! v-reverse v)
	  (map-cps-non-cs loop
			  (union-members v-reverse)
			  (lambda (us)
			   (fill-union-values! v us)
			   (k v))))))
    ((or (vlad-empty-list? v-reverse)
	 (vlad-true? v-reverse)
	 (vlad-false? v-reverse)
	 (vlad-real? v-reverse)
	 (primitive-procedure? v-reverse)
	 (perturbation-tagged-value? v-reverse)
	 (bundle? v-reverse)
	 (sensitivity-tagged-value? v-reverse)
	 (vlad-pair? v-reverse))
     (k (ad-error "Argument to *j-inverse ~a a reverse value" v-reverse)))
    ((nonrecursive-closure? v-reverse)
     (if (nonrecursive-closure-*j-inverse-cache v-reverse)
	 (k (nonrecursive-closure-*j-inverse-cache v-reverse))
	 (let ((b (find-if
		   (lambda (b)
		    (deep-abstract-value=?
		     v-reverse
		     (primitive-procedure-reverse (value-binding-value b))))
		   *value-bindings*)))
	  (cond
	   (b (let ((u (value-binding-value b)))
	       (set-nonrecursive-closure-*j-inverse-cache! v-reverse u)
	       (k u)))
	   ((tagged? 'reverse (nonrecursive-closure-tags v-reverse))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-nonrecursive-closure
		      'unfilled
		      (reverse-transform-inverse
		       (nonrecursive-closure-lambda-expression v-reverse)))))
	     (set-*j-cache! u v-reverse)
	     (set-nonrecursive-closure-*j-inverse-cache! v-reverse u)
	     (map-cps-non-cs loop
			     (get-nonrecursive-closure-values v-reverse)
			     (lambda (vs)
			      (fill-nonrecursive-closure-values! u vs)
			      (k u)))))
	   (else (k (ad-error "Argument to *j-inverse ~a a reverse value"
			      v-reverse)))))))
    ((recursive-closure? v-reverse)
     (cond ((recursive-closure-*j-inverse-cache v-reverse)
	    (k (recursive-closure-*j-inverse-cache v-reverse)))
	   ((tagged? 'reverse (recursive-closure-tags v-reverse))
	    ;; See the note in abstract-environment=?.
	    (let ((u (allocate-recursive-closure
		      'unfilled
		      (map-vector
		       unreverseify
		       (recursive-closure-procedure-variables v-reverse))
		      (map-vector
		       reverse-transform-inverse
		       (recursive-closure-lambda-expressions v-reverse))
		      (recursive-closure-index v-reverse))))
	     (set-*j-cache! u v-reverse)
	     (set-recursive-closure-*j-inverse-cache! v-reverse u)
	     (map-cps-non-cs loop
			     (get-recursive-closure-values v-reverse)
			     (lambda (vs)
			      (fill-recursive-closure-values! u vs)
			      (k u)))))
	   (else (k (ad-error "Argument to *j-inverse ~a a reverse value"
			      v-reverse)))))
    ((reverse-tagged-value? v-reverse)
     (k (get-reverse-tagged-value-primal v-reverse)))
    (else (internal-error))))))

;;; Pretty printer

;;; *unabbreviate-executably?* assumes that:
;;;  1. you don't shadow *-primitive
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
  (cond
   ((memq v vs) `(up ,(positionq v vs)))
   ((union? v)
    (if (eq? (union-values v) 'unfilled)
	'(union unfilled)
	`(union
	  ,@(map (lambda (u) (loop u (cons v vs))) (union-members v)))))
   ((vlad-empty-list? v) '())
   ((vlad-true? v) #t)
   ((vlad-false? v) #f)
   ((real? v) v)
   ((abstract-real? v) v)
   ((primitive-procedure? v) (primitive-procedure-symbol v))
   ((nonrecursive-closure? v)
    (if (eq? (nonrecursive-closure-values v) 'unfilled)
	'(nonrecursive-closure unfilled)
	`(nonrecursive-closure
	  ,@(map (lambda (x v) `(,(variable-name x) ,(loop v vs)))
		 (nonrecursive-closure-variables v)
		 (get-nonrecursive-closure-values v)))))
   ((recursive-closure? v)
    (if (eq? (recursive-closure-values v) 'unfilled)
	`(recursive-closure
	  unfilled
	  ,(variable-name
	    (vector-ref (recursive-closure-procedure-variables v)
			(recursive-closure-index v))))
	`(recursive-closure
	  ,@(map (lambda (x v) `(,(variable-name x) ,(loop v vs)))
		 (recursive-closure-variables v)
		 (get-recursive-closure-values v))
	  ,(variable-name
	    (vector-ref (recursive-closure-procedure-variables v)
			(recursive-closure-index v))))))
   ((perturbation-tagged-value? v)
    (if (eq? (perturbation-tagged-value-primal v) 'unfilled)
	'(perturbation unfilled)
	`(perturbation ,(loop (get-perturbation-tagged-value-primal v) vs))))
   ((bundle? v)
    `(bundle ,(if (eq? (bundle-primal v) 'unfilled)
		  'unfilled
		  (loop (get-bundle-primal v) vs))
	     ,(if (eq? (bundle-tangent v) 'unfilled)
		  'unfilled
		  (loop (get-bundle-tangent v) vs))))
   ((sensitivity-tagged-value? v)
    (if (eq? (sensitivity-tagged-value-primal v) 'unfilled)
	'(sensitivity unfilled)
	`(sensitivity ,(loop (get-sensitivity-tagged-value-primal v) vs))))
   ((reverse-tagged-value? v)
    (if (eq? (reverse-tagged-value-primal v) 'unfilled)
	'(reverse unfilled)
	`(reverse ,(loop (get-reverse-tagged-value-primal v) vs))))
   ((vlad-pair? v) `(pair ,(if (eq? (vlad-pair-car v) 'unfilled)
			       'unfilled
			       (loop (vlad-car v) vs))
			  ,(if (eq? (vlad-pair-cdr v) 'unfilled)
			       'unfilled
			       (loop (vlad-cdr v) vs))))
   ((tag? v) `(tag ,(loop (tag-abstract-value v) vs)))
   (else (internal-error)))))

(define (safe-externalize v)
 (with-safe-externalize (lambda () (externalize v))))

(define (externalize v)
 ;; breaks structure sharing
 (let ((v
	(let loop ((v v) (quote? #f) (vs '()))
	 (cond
	  ((memq v vs)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably" v))
	   `(up ,(positionq v vs)))
	  ((and (union? v)
		(= (length (get-union-values v)) 2)
		(some vlad-empty-list? (get-union-values v))
		(some (lambda (u)
		       (and (vlad-pair? u)
			    (deep-abstract-value=? (vlad-cdr u) v)))
		      (get-union-values v)))
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably" v))
	   `(list*
	     ,(loop (vlad-car
		     (find-if (lambda (u)
			       (and (vlad-pair? u)
				    (deep-abstract-value=? (vlad-cdr u) v)))
			      (get-union-values v)))
		    quote?
		    vs)))
	  ((union? v)
	   (when *unabbreviate-executably?*
	    (run-time-error "Cannot unabbreviate executably" v))
	   (cond ((empty-abstract-value? v) 'bottom)
		 ((null? (rest (union-members v))) (internal-error))
		 (else `(union ,@(map (lambda (u) (loop u quote? (cons v vs)))
				      (union-members v))))))
	  ((and (not *unabbreviate-transformed?*) (perturbation-value? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(perturb ,(loop (unperturb v) quote? vs)))
		 (else `(perturbation ,(loop (unperturb v) quote? vs)))))
	  ((and (not *unabbreviate-transformed?*) (forward-value? v))
	   (cond (*unabbreviate-executably?*
		  (assert (not quote?))
		  `(bundle ,(loop (primal v) quote? vs)
			   ,(loop (tangent v) quote? vs)))
		 (else `(forward ,(loop (primal v) quote? vs)
				 ,(loop (tangent v) quote? vs)))))
	  ((and (not *unabbreviate-transformed?*)
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
	  ((and (not *unabbreviate-transformed?*) (reverse-value? v))
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
	    (run-time-error "Cannot unabbreviate executably" v))
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
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     (string->symbol
	      (string-append (symbol->string (primitive-procedure-symbol v))
			     (symbol->string '-primitive))))
	    (else (primitive-procedure-symbol v))))
	  ((nonrecursive-closure? v)
	   (cond
	    (*unabbreviate-executably?*
	     (assert (not quote?))
	     (case (length (nonrecursive-closure-variables v))
	      ((0) (externalize-expression
		    (nonrecursive-closure-lambda-expression v)))
	      ((1) `(let ,(map (lambda (x v)
				`(,(variable-name x) ,(loop v quote? vs)))
			       (nonrecursive-closure-variables v)
			       (get-nonrecursive-closure-values v))
		     ,(externalize-expression
		       (nonrecursive-closure-lambda-expression v))))
	      (else `(let ,(map (lambda (x v)
				 `(,(variable-name x) ,(loop v quote? vs)))
				(nonrecursive-closure-variables v)
				(get-nonrecursive-closure-values v))
		      ,(externalize-expression
			(nonrecursive-closure-lambda-expression v))))))
	    (*unabbreviate-nonrecursive-closures?*
	     `(nonrecursive-closure
	       ,(map (lambda (x v) `(,(variable-name x) ,(loop v quote? vs)))
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
			       (lambda (x e)
				`(,(variable-name x)
				  ,(externalize-expression e)))
			       (recursive-closure-procedure-variables v)
			       (recursive-closure-lambda-expressions v)))
		     ,(variable-name
		       (vector-ref (recursive-closure-procedure-variables v)
				   (recursive-closure-index v)))))
	      ((1) `(let ,(map (lambda (x v)
				`(,(variable-name x) ,(loop v quote? vs)))
			       (recursive-closure-variables v)
			       (get-recursive-closure-values v))
		     (letrec ,(vector->list
			       (map-vector
				(lambda (x e)
				 `(,(variable-name x)
				   ,(externalize-expression e)))
				(recursive-closure-procedure-variables v)
				(recursive-closure-lambda-expressions v)))
		      ,(variable-name
			(vector-ref (recursive-closure-procedure-variables v)
				    (recursive-closure-index v))))))
	      (else
	       `(let ,(map (lambda (x v)
			    `(,(variable-name x) ,(loop v quote? vs)))
			   (recursive-closure-variables v)
			   (get-recursive-closure-values v))
		 (letrec ,(vector->list
			   (map-vector
			    (lambda (x e)
			     `(,(variable-name x) ,(externalize-expression e)))
			    (recursive-closure-procedure-variables v)
			    (recursive-closure-lambda-expressions v)))
		  ,(variable-name
		    (vector-ref (recursive-closure-procedure-variables v)
				(recursive-closure-index v))))))))
	    (*unabbreviate-recursive-closures?*
	     `(recursive-closure
	       ,(map (lambda (x v) `(,(variable-name x) ,(loop v quote? vs)))
		     (recursive-closure-variables v)
		     (get-recursive-closure-values v))
	       ,(vector->list
		 (map-vector
		  (lambda (x e)
		   `(,(variable-name x) ,(externalize-expression e)))
		  (recursive-closure-procedure-variables v)
		  (recursive-closure-lambda-expressions v)))
	       ,(variable-name
		 (vector-ref (recursive-closure-procedure-variables v)
			     (recursive-closure-index v)))))
	    (else (variable-name
		   (vector-ref (recursive-closure-procedure-variables v)
			       (recursive-closure-index v))))))
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
	    (else `(reverse
		    ,(loop (get-reverse-tagged-value-primal v) quote? vs)))))
	  (else (internal-error))))))
  (if *unabbreviate-executably?*
      `(let* ,(map (lambda (b)
		    (let ((x (variable-name (value-binding-variable b))))
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
	      (free-variables e) (environment-bindings e))))
      (remove-if (lambda (e) (null? (environment-bindings e))) *expressions*)))

;;; Concrete evaluator

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

;;; Environment restriction/construction

(define (restrict-environment vs is)
 (let ((vs (list->vector vs))) (map (lambda (i) (vector-ref vs i)) is)))

(define (letrec-nested-environment vs e)
 (let ((xs (list->vector (letrec-expression-procedure-variables e)))
       (es (list->vector (letrec-expression-lambda-expressions e)))
       (vs0 (list->vector vs)))
  (map (lambda (p? i)
	(if p?
	    ;; This may create an abstract value that violates the syntactic
	    ;; constraints.
	    ;; foo
	    (new-recursive-closure
	     (restrict-environment vs (letrec-expression-indices e)) xs es i)
	    (vector-ref vs0 i)))
       (letrec-expression-body-free-variable-procedure-variable? e)
       (letrec-expression-body-free-variable-indices e))))

(define (concrete-destructure p v)
 (cond
  ((constant-expression? p)
   (unless (abstract-value=? (constant-expression-value p) v)
    (run-time-error (format #f "Argument is not an equivalent value for ~s"
			    (externalize-expression p))
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
   (append
    (concrete-destructure
     (cons-expression-car p) (tagged-vlad-car (cons-expression-tags p) v))
    (concrete-destructure
     (cons-expression-cdr p) (tagged-vlad-cdr (cons-expression-tags p) v))))
  (else (internal-error))))

(define (construct-environment-for-let e vs v-alist)
 (let ((vs (list->vector vs)))
  (map
   (lambda (i x)
    ;; needs work: To make application-let-free-variable-indices such that
    ;;             this can be made more efficient.
    (cond ((assp variable=? x v-alist) => cdr) (else (vector-ref vs i))))
   (application-let-free-variable-indices e)
   (free-variables (lambda-expression-body (application-callee e))))))

(define (construct-environment u1 v-alist)
 (cond
  ((nonrecursive-closure? u1)
   (let ((vs (list->vector (closure-values u1))))
    (map
     (lambda (i x)
      ;; needs work: To make nonrecursive-closure-body-free-variable-indices
      ;;             such that this can be made more efficient.
      (cond ((assp variable=? x v-alist) => cdr) (else (vector-ref vs i))))
     (nonrecursive-closure-body-free-variable-indices u1)
     (free-variables
      (lambda-expression-body (nonrecursive-closure-lambda-expression u1))))))
  ((recursive-closure? u1)
   (let ((vs (list->vector (closure-values u1))))
    (map (lambda (i i1 x)
	  ;; needs work:
	  ;; To make recursive-closure-body-free-variable-indices and
	  ;; recursive-closure-body-free-variable-procedure-variable-indices
	  ;; such that this can be made more efficient.
	  (cond
	   ((assp variable=? x v-alist) => cdr)
	   (i1
	    ;; This may create an abstract value that violates the syntactic
	    ;; constraints.
	    ;; foo
	    (new-recursive-closure (get-recursive-closure-values u1)
				   (recursive-closure-procedure-variables u1)
				   (recursive-closure-lambda-expressions u1)
				   i1))
	   (else (vector-ref vs i))))
	 (recursive-closure-body-free-variable-indices u1)
	 (recursive-closure-body-free-variable-procedure-variable-indices u1)
	 (free-variables (lambda-expression-body
			  (vector-ref (recursive-closure-lambda-expressions u1)
				      (recursive-closure-index u1)))))))
  ((perturbation-tagged-value? u1)
   (map perturb
	(construct-environment
	 (unperturb u1)
	 (map (lambda (x-v)
	       (cons (unperturbationify (car x-v)) (unperturb (cdr x-v))))
	      v-alist))))
  ((bundle? u1)
   (map (lambda (v1 v2) (bundle (vlad-cons v1 v2)))
	(construct-environment
	 (primal u1)
	 (map (lambda (x-v) (cons (unforwardify (car x-v)) (primal (cdr x-v))))
	      v-alist))
	(construct-environment
	 (tangent u1)
	 (map (lambda (x-v)
	       (cons (perturbationify (unforwardify (car x-v)))
		     (tangent (cdr x-v))))
	      v-alist))))
  ((sensitivity-tagged-value? u1)
   (map sensitize
	(construct-environment
	 (unsensitize u1)
	 (map (lambda (x-v)
	       (cons (unsensitivityify (car x-v)) (unsensitize (cdr x-v))))
	      v-alist))))
  ((reverse-tagged-value? u1)
   (map *j
	(construct-environment
	 (*j-inverse u1)
	 (map (lambda (x-v)
	       (cons (unreverseify (car x-v)) (*j-inverse (cdr x-v))))
	      v-alist))))
  (else (internal-error))))

;;; needs work: This evaluator is not tail recursive.

(define (concrete-apply v1 v2)
 (unless (vlad-procedure? v1) (run-time-error "Target is not a procedure" v1))
 (unless (prefix-tags? (value-tags v1) (value-tags v2))
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
	 ((primitive-procedure? v1) ((primitive-procedure-concrete v1) v2))
	 ((closure? v1)
	  (concrete-eval
	   (closure-body v1)
	   (construct-environment
	    v1 (concrete-destructure (closure-parameter v1) v2))))
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
  ;; foo
  ((lambda-expression? e) (new-nonrecursive-closure vs e))
  ((application? e)
   (if (lambda-expression? (application-callee e))
       ;; This handling of LET is an optimization. It affects the stack trace
       ;; on error, tracing, and the tag-check error message.
       (let* ((e1 (application-callee e))
	      (v (concrete-eval
		  (application-argument e)
		  (restrict-environment vs (application-argument-indices e)))))
	(unless (prefix-tags? (lambda-expression-tags e1) (value-tags v))
	 (run-time-error "Value has wrong type for let binder" v))
	(concrete-eval
	 (lambda-expression-body e1)
	 (construct-environment-for-let
	  e vs (concrete-destructure (lambda-expression-parameter e1) v))))
       ;; This LET* is to specify the evaluation order.
       (let* ((v1 (concrete-eval
		   (application-callee e)
		   (restrict-environment vs (application-callee-indices e))))
	      (v2 (concrete-eval
		   (application-argument e)
		   (restrict-environment
		    vs (application-argument-indices e)))))
	(concrete-apply v1 v2))))
  ((letrec-expression? e)
   (concrete-eval (letrec-expression-body e) (letrec-nested-environment vs e)))
  ((cons-expression? e)
   ;; This LET* is to specify the evaluation order.
   (let* ((v1 (concrete-eval
	       (cons-expression-car e)
	       (restrict-environment vs (cons-expression-car-indices e))))
	  (v2 (concrete-eval
	       (cons-expression-cdr e)
	       (restrict-environment vs (cons-expression-cdr-indices e)))))
    (tagged-vlad-cons (cons-expression-tags e) v1 v2)))
  (else (internal-error))))

;;; Flow analysis

;;; Abstract values

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
  ((vlad-pair? v)
   (vlad-cons (concrete-value->abstract-value (vlad-car v))
	      (concrete-value->abstract-value (vlad-cdr v))))
  (else (internal-error))))

;;; Widen

;;; Width

(define (reduce-real-width limit v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  21
  (canonize-and-maybe-intern-abstract-value
   (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
    (let ((found? (assq v cs)))
     (cond
      (found? (k (cdr found?) cs))
      ((union? v)
       ;; This widening case is part of widen-abstract-value.
       (let ((v-prime (allocate-union 'unfilled)))
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
       (let ((u-prime (allocate-nonrecursive-closure
		       'unfilled (nonrecursive-closure-lambda-expression v))))
	(map-cps loop
		 (get-nonrecursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-nonrecursive-closure-values! u-prime vs-prime)
		  (k u-prime cs)))))
      ((recursive-closure? v)
       ;; See the note in abstract-environment=?.
       (let ((u-prime (allocate-recursive-closure
		       'unfilled
		       (recursive-closure-procedure-variables v)
		       (recursive-closure-lambda-expressions v)
		       (recursive-closure-index v))))
	(map-cps loop
		 (get-recursive-closure-values v)
		 (cons (cons v u-prime) cs)
		 (lambda (vs-prime cs)
		  (fill-recursive-closure-values! u-prime vs-prime)
		  (k u-prime cs)))))
      ((perturbation-tagged-value? v)
       (let ((u-prime (allocate-perturbation-tagged-value 'unfilled)))
	(loop (get-perturbation-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-perturbation-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((bundle? v)
       (let ((u-prime (allocate-bundle 'unfilled 'unfilled)))
	(loop (get-bundle-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-primal-prime cs)
	       (loop (get-bundle-tangent v)
		     cs
		     (lambda (v-tangent-prime cs)
		      (fill-bundle! u-prime v-primal-prime v-tangent-prime)
		      (k u-prime cs)))))))
      ((sensitivity-tagged-value? v)
       (let ((u-prime (allocate-sensitivity-tagged-value 'unfilled)))
	(loop (get-sensitivity-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-sensitivity-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((reverse-tagged-value? v)
       (let ((u-prime (allocate-reverse-tagged-value 'unfilled)))
	(loop (get-reverse-tagged-value-primal v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-prime cs)
	       (fill-reverse-tagged-value-primal! u-prime v-prime)
	       (k u-prime cs)))))
      ((vlad-pair? v)
       (let ((u-prime (allocate-vlad-pair 'unfilled 'unfilled)))
	(loop (vlad-car v)
	      (cons (cons v u-prime) cs)
	      (lambda (v-car-prime cs)
	       (loop (vlad-cdr v)
		     cs
		     (lambda (v-cdr-prime cs)
		      (fill-vlad-pair! u-prime v-car-prime v-cdr-prime)
		      (k u-prime cs)))))))
      (else (internal-error))))))))

(define (limit-real-width v)
 (if (eq? *real-width-limit* #f) v (reduce-real-width *real-width-limit* v)))

(define (pick-values-to-coalesce-for-width-limit limit match? type? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  22
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
    (else
     (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
      (if (null? vs1)
	  (k vs)
	  (outer (first vs1) vs (lambda (vs) (inner (rest vs1) vs))))))))))

(define (merge-subabstract-values v u1 u2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  23
  (canonize-and-maybe-intern-abstract-value
   (let ((u12 (create-aggregate-value-with-new-values
	       u1
	       (map abstract-value-union
		    ;; needs work: To check conformance.
		    (aggregate-value-values u1)
		    (aggregate-value-values u2)))))
    (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
     (let ((found? (assq v cs)))
      (cond
       (found? (k (cdr found?) cs))
       ;; needs work: Do we need to update cs here?
       ((or (eq? v u1) (eq? v u2)) (loop u12 cs k))
       ((union? v)
	;; This widening case is part of widen-abstract-value.
	(let ((v-prime (allocate-union 'unfilled)))
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
	(let ((u-prime (allocate-nonrecursive-closure
			'unfilled (nonrecursive-closure-lambda-expression v))))
	 (map-cps loop
		  (get-nonrecursive-closure-values v)
		  (cons (cons v u-prime) cs)
		  (lambda (vs-prime cs)
		   (fill-nonrecursive-closure-values! u-prime vs-prime)
		   (k u-prime cs)))))
       ((recursive-closure? v)
	;; See the note in abstract-environment=?.
	(let ((u-prime (allocate-recursive-closure
			'unfilled
			(recursive-closure-procedure-variables v)
			(recursive-closure-lambda-expressions v)
			(recursive-closure-index v))))
	 (map-cps loop
		  (get-recursive-closure-values v)
		  (cons (cons v u-prime) cs)
		  (lambda (vs-prime cs)
		   (fill-recursive-closure-values! u-prime vs-prime)
		   (k u-prime cs)))))
       ((perturbation-tagged-value? v)
	(let ((u-prime (allocate-perturbation-tagged-value 'unfilled)))
	 (loop (get-perturbation-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-perturbation-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((bundle? v)
	(let ((u-prime (allocate-bundle 'unfilled 'unfilled)))
	 (loop (get-bundle-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-primal-prime cs)
		(loop (get-bundle-tangent v)
		      cs
		      (lambda (v-tangent-prime cs)
		       (fill-bundle! u-prime v-primal-prime v-tangent-prime)
		       (k u-prime cs)))))))
       ((sensitivity-tagged-value? v)
	(let ((u-prime (allocate-sensitivity-tagged-value 'unfilled)))
	 (loop (get-sensitivity-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-sensitivity-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((reverse-tagged-value? v)
	(let ((u-prime (allocate-reverse-tagged-value 'unfilled)))
	 (loop (get-reverse-tagged-value-primal v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-prime cs)
		(fill-reverse-tagged-value-primal! u-prime v-prime)
		(k u-prime cs)))))
       ((vlad-pair? v)
	(let ((u-prime (allocate-vlad-pair 'unfilled 'unfilled)))
	 (loop (vlad-car v)
	       (cons (cons v u-prime) cs)
	       (lambda (v-car-prime cs)
		(loop (vlad-cdr v)
		      cs
		      (lambda (v-cdr-prime cs)
		       (fill-vlad-pair! u-prime v-car-prime v-cdr-prime)
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
	    ;; See note in limit-depth.
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
  24
  (let outer ((v v)
	      (cs '())
	      (path '())
	      (depth-of-path 0)
	      (longest-path #f)
	      (depth-of-longest-path #f)
	      (k
	       (lambda (longest-path depth-of-longest-path cs) longest-path)))
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
		 (map (lambda (c)
		       (if (eq? (car c) v) (cons v depth-of-path) c))
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
	      (inner
	       (rest vs) cs longest-path depth-of-longest-path))))))))))))

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
	    ;; -all-limits 1 on {cannon,backprop}-{F,R} trigger this. I believe
	    ;; this is because of the conservative nature of
	    ;; abstract-value-subset? but I haven't fully checked that.
	    ;; (assert (abstract-value-subset? v v-prime))
	    (loop v-prime)))))))

;;; List widening

(define (widen-lists v)
 ;; This is written in CPS so as not to break structure sharing.
 (if *widen-lists?*
     (time-it-bucket
      25
      (canonize-and-maybe-intern-abstract-value
       (let loop ((v v) (cs '()) (k (lambda (v-prime cs) v-prime)))
	(let ((found? (assq v cs)))
	 (cond
	  (found? (k (cdr found?) cs))
	  ((union? v)
	   ;; This widening case is part of widen-abstract-value.
	   (let ((v-prime (allocate-union 'unfilled)))
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
	   (let ((u-prime (allocate-nonrecursive-closure
			   'unfilled
			   (nonrecursive-closure-lambda-expression v))))
	    (map-cps loop
		     (get-nonrecursive-closure-values v)
		     (cons (cons v u-prime) cs)
		     (lambda (vs-prime cs)
		      (fill-nonrecursive-closure-values! u-prime vs-prime)
		      (k u-prime cs)))))
	  ((recursive-closure? v)
	   ;; See the note in abstract-environment=?.
	   (let ((u-prime (allocate-recursive-closure
			   'unfilled
			   (recursive-closure-procedure-variables v)
			   (recursive-closure-lambda-expressions v)
			   (recursive-closure-index v))))
	    (map-cps loop
		     (get-recursive-closure-values v)
		     (cons (cons v u-prime) cs)
		     (lambda (vs-prime cs)
		      (fill-recursive-closure-values! u-prime vs-prime)
		      (k u-prime cs)))))
	  ((perturbation-tagged-value? v)
	   (let ((u-prime (allocate-perturbation-tagged-value 'unfilled)))
	    (loop (get-perturbation-tagged-value-primal v)
		  (cons (cons v u-prime) cs)
		  (lambda (v-prime cs)
		   (fill-perturbation-tagged-value-primal! u-prime v-prime)
		   (k u-prime cs)))))
	  ((bundle? v)
	   (let ((u-prime (allocate-bundle 'unfilled 'unfilled)))
	    (loop (get-bundle-primal v)
		  (cons (cons v u-prime) cs)
		  (lambda (v-primal-prime cs)
		   (loop (get-bundle-tangent v)
			 cs
			 (lambda (v-tangent-prime cs)
			  (fill-bundle! u-prime v-primal-prime v-tangent-prime)
			  (k u-prime cs)))))))
	  ((sensitivity-tagged-value? v)
	   (let ((u-prime (allocate-sensitivity-tagged-value 'unfilled)))
	    (loop (get-sensitivity-tagged-value-primal v)
		  (cons (cons v u-prime) cs)
		  (lambda (v-prime cs)
		   (fill-sensitivity-tagged-value-primal! u-prime v-prime)
		   (k u-prime cs)))))
	  ((reverse-tagged-value? v)
	   (let ((u-prime (allocate-reverse-tagged-value 'unfilled)))
	    (loop (get-reverse-tagged-value-primal v)
		  (cons (cons v u-prime) cs)
		  (lambda (v-prime cs)
		   (fill-reverse-tagged-value-primal! u-prime v-prime)
		   (k u-prime cs)))))
	  ((vlad-pair? v)
	   (cond
	    ;; See note in abstract-value-unionable?.
	    ((vlad-empty-list? (vlad-cdr v))
	     (let* ((u-prime (allocate-vlad-pair 'unfilled 'unfilled))
		    ;; This widening case is part of widen-abstract-value.
		    (v-prime (allocate-union (list u-prime (vlad-cdr v)))))
	      (loop (vlad-car v)
		    cs
		    (lambda (v-car-prime cs)
		     (fill-vlad-pair! u-prime v-car-prime v-prime)
		     (k v-prime cs)))))
	    ((and
	      (union? (vlad-cdr v))
	      (= (length (union-members (vlad-cdr v))) 2)
	      (some vlad-empty-list? (union-members (vlad-cdr v)))
	      (some (lambda (u)
		     (and (vlad-pair? u)
			  (deep-abstract-value=? (vlad-cdr u) (vlad-cdr v))))
		    (union-members (vlad-cdr v)))
	      (abstract-value-unionable?
	       #t
	       (vlad-car v)
	       (vlad-car
		(find-if
		 (lambda (u)
		  (and (vlad-pair? u)
		       (deep-abstract-value=? (vlad-cdr u) (vlad-cdr v))))
		 (union-members (vlad-cdr v))))))
	     (let* ((u-prime (allocate-vlad-pair 'unfilled 'unfilled))
		    ;; This widening case is part of widen-abstract-value.
		    (v-prime (allocate-union
			      (list u-prime
				    (find-if vlad-empty-list?
					     (union-members (vlad-cdr v)))))))
	      (loop
	       (abstract-value-union-internal
		(vlad-car v)
		(vlad-car
		 (find-if
		  (lambda (u)
		   (and (vlad-pair? u)
			(deep-abstract-value=? (vlad-cdr u) (vlad-cdr v))))
		  (union-members (vlad-cdr v)))))
	       cs
	       (lambda (v-car-prime cs)
		(fill-vlad-pair! u-prime v-car-prime v-prime)
		(k v-prime cs)))))
	    (else
	     (let ((u-prime (allocate-vlad-pair 'unfilled 'unfilled)))
	      (loop (vlad-car v)
		    (cons (cons v u-prime) cs)
		    (lambda (v-car-prime cs)
		     (loop (vlad-cdr v)
			   cs
			   (lambda (v-cdr-prime cs)
			    (fill-vlad-pair! u-prime v-car-prime v-cdr-prime)
			    (k u-prime cs)))))))))
	  (else (internal-error)))))))
     v))

;;; Syntactic constraints

(define (limit-closure-width v)
 ;; This used to use a nondereferencing closure match.
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

(define (limit-pair-width v)
 (limit-width *pair-width-limit* (lambda (u1 u2) #t) vlad-pair? v))

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
  ;; This used to use a nondereferencing closure match.
  (nonrecursive-closure-match? u1 u2)
  (every (lambda (v1 v2) (abstract-value-unionable? #f v1 v2))
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
 ;; This used to use a nondereferencing closure match.
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

(define (limit-pair-depth v)
 (limit-depth *pair-depth-limit* (lambda (u1 u2) #t) vlad-pair? v))

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
   ((and (vlad-pair? v) (vlad-pair-widen v)) (vlad-pair-widen v))
   ((and (union? v) (union-widen v)) (union-widen v))
   (else
    (let ((v-prime
	   (let loop ((v v))
	    (let ((v-prime (widen-lists
			    (limit-pair-depth
			     (limit-reverse-tagged-value-depth
			      (limit-sensitivity-tagged-value-depth
			       (limit-bundle-depth
				(limit-perturbation-tagged-value-depth
				 (limit-backpropagator-depth
				  (limit-closure-depth
				   (limit-pair-width
				    (limit-reverse-tagged-value-width
				     (limit-sensitivity-tagged-value-width
				      (limit-bundle-width
				       (limit-perturbation-tagged-value-width
					(limit-closure-width v))))))))))))))))
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
      ((vlad-pair? v) (set-vlad-pair-widen! v v-prime))
      ((union? v) (set-union-widen! v v-prime)))
     v-prime)))))

(define (meets-syntactic-constraints? v)
 ;; This is not a widening case.
 (abstract-value=? v (widen-abstract-value v)))

;;; Abstract evaluator

(define (abstract-eval1 e vs)
 (assert (<= (count-if
	      (lambda (b)
	       (abstract-environment=? vs (environment-binding-values b)))
	      (environment-bindings e))
	     1))
 (let ((b (find-if
	   (lambda (b)
	    (abstract-environment=? vs (environment-binding-values b)))
	   (environment-bindings e))))
  (if b (environment-binding-value b) (empty-abstract-value))))

(define (abstract-destructure f i p v k)
 ;; The assumption is that v doesn't violate the syntactic constraints.
 (let outer ((p p) (v v) (v-alist '()) (k k))
  (cond
   ;; This case comes first to avoid the dispatch.
   ((variable-access-expression? p)
    (k (cons (cons (variable-access-expression-variable p) v) v-alist)))
   ;; widening case J
   ((union? v) (f (lambda (u) (outer p u v-alist k)) v))
   ((constant-expression? p)
    ;; This can widen when the constant expression value violates the
    ;; syntactic constraints (presumably pair depth limit).
    ;; widening case A
    (let ((v-prime
	   (widen-abstract-value
	    (concrete-value->abstract-value (constant-expression-value p)))))
     (cond
      ((abstract-value=? v-prime v) (k v-alist))
      ((abstract-value-nondisjoint? v-prime v)
       (compile-time-warning
	(format #f "Argument might not be an equivalent value for ~s"
		(constant-expression-value p))
	v)
       (k v-alist))
      (else (compile-time-warning
	     (format #f "Argument might not be an equivalent value for ~s"
		     (constant-expression-value p))
	     v)
	    i))))
   ((lambda-expression? p)
    (cond ((and (nonrecursive-closure? v)
		(dereferenced-expression-eqv?
		 p (nonrecursive-closure-lambda-expression v)))
	   (let inner ((xs1 (parameter-variables p))
		       (xs2 (nonrecursive-closure-variables v))
		       (vs (get-nonrecursive-closure-values v))
		       (v-alist v-alist)
		       (k k))
	    (if (null? xs1)
		(k v-alist)
		(outer (allocate-variable-access-expression (first xs1))
		       (first vs)
		       v-alist
		       (lambda (v-alist)
			(inner (rest xs1) (rest xs2) (rest vs) v-alist k))))))
	  (else
	   (compile-time-warning
	    (format
	     #f
	     "Argument might not be a matching nonrecursive closure for ~s"
	     (externalize-expression p))
	    v)
	   i)))
   ((letrec-expression? p)
    (assert (and (variable-access-expression? (letrec-expression-body p))
		 (memp variable=?
		       (variable-access-expression-variable
			(letrec-expression-body p))
		       (letrec-expression-procedure-variables p))))
    (cond ((and (recursive-closure? v)
		(= (recursive-closure-index v)
		   (positionp variable=?
			      (variable-access-expression-variable
			       (letrec-expression-body p))
			      (letrec-expression-procedure-variables p)))
		(= (vector-length (recursive-closure-procedure-variables v))
		   (length (letrec-expression-procedure-variables p)))
		(= (vector-length (recursive-closure-lambda-expressions v))
		   (length (letrec-expression-lambda-expressions p)))
		(every dereferenced-expression-eqv?
		       (vector->list (recursive-closure-lambda-expressions v))
		       (letrec-expression-lambda-expressions p)))
	   (let inner ((xs1 (parameter-variables p))
		       (xs2 (recursive-closure-variables v))
		       (vs (get-recursive-closure-values v))
		       (v-alist v-alist)
		       (k k))
	    (if (null? xs1)
		(k v-alist)
		(outer (allocate-variable-access-expression (first xs1))
		       (first vs)
		       v-alist
		       (lambda (v-alist)
			(inner (rest xs1) (rest xs2) (rest vs) v-alist k))))))
	  (else
	   (compile-time-warning
	    (format
	     #f
	     "Argument might not be a matching recursive closure for ~s"
	     (externalize-expression p))
	    v)
	   i)))
   ((cons-expression? p)
    (outer (cons-expression-car p)
	   (tagged-vlad-car (cons-expression-tags p) v)
	   v-alist
	   (lambda (v-alist)
	    (outer (cons-expression-cdr p)
		   (tagged-vlad-cdr (cons-expression-tags p) v)
		   v-alist
		   k))))
   (else (internal-error)))))

(define (abstract-apply v1 v2)
 (cond ((empty-abstract-value? v2) (empty-abstract-value))
       ;; widening case I
       ((union? v1) (map-union (lambda (u1) (abstract-apply u1 v2)) v1))
       ((primitive-procedure? v1) ((primitive-procedure-abstract v1) v2))
       ((closure? v1)
	(unless (every-value-tags
		 (lambda (tags2) (prefix-tags? (value-tags v1) tags2)) v2)
	 (compile-time-warning
	  "Argument might have wrong type for target" v1 v2))
	(if (some-value-tags
	     (lambda (tags2) (prefix-tags? (value-tags v1) tags2)) v2)
	    (abstract-destructure
	     ;; widening case J
	     map-union
	     (empty-abstract-value)
	     (closure-parameter v1)
	     v2
	     (lambda (v-alist)
	      ;; bar
	      (abstract-eval1
	       (closure-body v1) (construct-environment v1 v-alist))))
	    (empty-abstract-value)))
       (else (compile-time-warning "Target might not be a procedure" v1))))

(define (enqueue! e)
 (unless (enqueue? e)
  (set-enqueue?! e #t)
  (set! *queue* (cons e *queue*))))

(define (abstract-eval! e)
 (cond
  ((application? e)
   (cond
    ((lambda-expression? (application-callee e))
     ;; This handling of LET is an optimization. See the note in concrete-eval.
     (let ((e1 (lambda-expression-body (application-callee e)))
	   (p (lambda-expression-parameter (application-callee e)))
	   (tags1 (lambda-expression-tags (application-callee e))))
      (for-each
       (lambda (b)
	(let* ((vs (environment-binding-values b))
	       (v (abstract-eval1 (application-argument e)
				  (restrict-environment
				   vs (application-argument-indices e)))))
	 ;; needs work: what if v is empty-abstract-value
	 (unless (empty-abstract-value? v)
	  (unless (every-value-tags
		   (lambda (tags) (prefix-tags? tags1 tags)) v)
	   (compile-time-warning
	    "Value might have wrong type for let binder" v))
	  (when (some-value-tags (lambda (tags) (prefix-tags? tags1 tags)) v)
	   (abstract-destructure
	    ;; widening case J
	    for-each-union
	    #f
	    p
	    v
	    (lambda (v-alist)
	     ;; See the note in abstract-eval-prime!
	     ;; here I am: Can hoist this since it doesn't depend on v-alist
	     ;;            or b. It only depends on v-alist being nonempty and
	     ;;            v not being an empty abstract value.
	     ;; We now use expression-eqv? in only two places. Here is the
	     ;; second (which includes all similar additions to parents).
	     (unless (memp expression-eqv? e (parents e1))
	      (set-parents! e1 (cons e (parents e1)))
	      (enqueue! e))
	     ;; bar
	     (abstract-eval-prime!
	      e1 (construct-environment-for-let e vs v-alist))))))))
       (environment-bindings e))
      (for-each
       (lambda (b)
	(let* ((vs (environment-binding-values b))
	       (v (abstract-eval1 (application-argument e)
				  (restrict-environment
				   vs (application-argument-indices e))))
	       ;; widening case B-prime
	       (v (widen-abstract-value
		   ;; Need to refresh my memory as to why this union is needed.
		   (abstract-value-union
		    (environment-binding-value b)
		    (begin
		     ;; needs work: what if v is empty-abstract-value
		     (unless (every-value-tags
			      (lambda (tags) (prefix-tags? tags1 tags)) v)
		      (compile-time-warning
		       "Value might have wrong type for let binder" v))
		     (if (some-value-tags
			  (lambda (tags) (prefix-tags? tags1 tags)) v)
			 (abstract-destructure
			  ;; widening case J
			  map-union
			  (empty-abstract-value)
			  p
			  v
			  (lambda (v-alist)
			   ;; bar
			   (abstract-eval1
			    e1 (construct-environment-for-let e vs v-alist))))
			 (empty-abstract-value)))))))
	 ;; With the above union the old value will always be a subset of the
	 ;; new value by a precise calculation but might not be given that the
	 ;; subset calculation is imprecise. Need to document example where
	 ;; this occurs.
	 (unless (abstract-value-subset? v (environment-binding-value b))
	  (set-environment-binding-value! b v)
	  (for-each enqueue! (parents e)))))
       (environment-bindings e))))
    (else
     (for-each (lambda (b)
		(abstract-apply-prime!
		 e
		 (abstract-eval1
		  (application-callee e)
		  (restrict-environment (environment-binding-values b)
					(application-callee-indices e)))
		 (abstract-eval1
		  (application-argument e)
		  (restrict-environment (environment-binding-values b)
					(application-argument-indices e)))))
	       (environment-bindings e))
     (for-each
      (lambda (b)
       ;; widening case B
       (let ((v (widen-abstract-value
		 ;; Need to refresh my memory as to why this union is needed.
		 (abstract-value-union
		  (environment-binding-value b)
		  (abstract-apply
		   (abstract-eval1 (application-callee e)
				   (restrict-environment
				    (environment-binding-values b)
				    (application-callee-indices e)))
		   (abstract-eval1 (application-argument e)
				   (restrict-environment
				    (environment-binding-values b)
				    (application-argument-indices e))))))))
	;; With the above union the old value will always be a subset of the
	;; new value by a precise calculation but might not be given that the
	;; subset calculation is imprecise. Need to document example where this
	;; occurs.
	(unless (abstract-value-subset? v (environment-binding-value b))
	 (set-environment-binding-value! b v)
	 (for-each enqueue! (parents e)))))
      (environment-bindings e)))))
  ((letrec-expression? e)
   (for-each
    (lambda (b)
     ;; widening case C
     (let ((v (widen-abstract-value
	       ;; See the above note.
	       (abstract-value-union
		(environment-binding-value b)
		;; bar
		(abstract-eval1 (letrec-expression-body e)
				(letrec-nested-environment
				 (environment-binding-values b) e))))))
      ;; See the above note.
      (unless (abstract-value-subset? v (environment-binding-value b))
       (set-environment-binding-value! b v)
       (for-each enqueue! (parents e)))))
    (environment-bindings e)))
  ((cons-expression? e)
   (for-each
    (lambda (b)
     ;; widening case D
     (let ((v (widen-abstract-value
	       ;; See the above note.
	       (abstract-value-union
		(environment-binding-value b)
		(tagged-vlad-cons
		 (cons-expression-tags e)
		 (abstract-eval1
		  (cons-expression-car e)
		  (restrict-environment (environment-binding-values b)
					(cons-expression-car-indices e)))
		 (abstract-eval1
		  (cons-expression-cdr e)
		  (restrict-environment (environment-binding-values b)
					(cons-expression-cdr-indices e))))))))
      ;; See the above note.
      (unless (abstract-value-subset? v (environment-binding-value b))
       (set-environment-binding-value! b v)
       (for-each enqueue! (parents e)))))
    (environment-bindings e)))
  (else (internal-error))))

(define (abstract-apply-closure! e u1 v2)
 (assert (not (union? u1)))
 (abstract-destructure
  ;; widening case J
  for-each-union
  #f
  (closure-parameter u1)
  v2
  (lambda (v-alist)
   (let ((e1 (closure-body u1)))
    ;; See the note in abstract-eval-prime!
    (unless (memp expression-eqv? e (parents e1))
     (set-parents! e1 (cons e (parents e1)))
     (enqueue! e))
    ;; bar
    (abstract-eval-prime! e1 (construct-environment u1 v-alist))))))

(define (abstract-apply-prime! e v1 v2)
 (unless (empty-abstract-value? v2)
  (for-each
   (lambda (u1)
    (cond
     ((primitive-procedure? u1)
      ;; needs work: Should put this into slots of the primitive procedures.
      (when (eq? (primitive-procedure-symbol u1) 'if-procedure)
       (for-each
	(lambda (u)
	 (if (vlad-pair? u)
	     (for-each
	      (lambda (u1)
	       (for-each
		(lambda (u23)
		 (if (vlad-pair? u23)
		     (for-each
		      (lambda (u2)
		       (for-each
			(lambda (u3)
			 ;; When v3 and/or v2 is not a procedure the warning is
			 ;; issued by abstract-apply. If it is a primitive
			 ;; procedure we don't have to do anything here. In
			 ;; practise, it will always be a nonrecursive closure
			 ;; unless the user calls if-procedure outside the
			 ;; context of the if macro.
			 (if (vlad-false? u1)
			     (when (closure? u3)
			      (abstract-apply-closure! e u3 (vlad-empty-list)))
			     (when (closure? u2)
			      (abstract-apply-closure!
			       e u2 (vlad-empty-list)))))
			(union-members (vlad-cdr u23))))
		      (union-members (vlad-car u23)))
		     (compile-time-warning
		      "Argument to if-procedure might be invalid" u)))
		(union-members (vlad-cdr u))))
	      (union-members (vlad-car u)))
	     (compile-time-warning
	      "Argument to if-procedure might be invalid" u)))
	(union-members v2))))
     ((closure? u1)
      (unless (every-value-tags
	       (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
       (compile-time-warning
	"Argument might have wrong type for target" u1 v2))
      (when (some-value-tags
	     (lambda (tags2) (prefix-tags? (value-tags u1) tags2)) v2)
       (abstract-apply-closure! e u1 v2)))
     (else (compile-time-warning "Target might not be a procedure" u1))))
   (union-members v1))))

(define (abstract-eval-prime! e vs)
 ;; Can't give an error if entry already exists since we call this
 ;; indiscriminantly in abstract-apply-prime!.
 (let loop ((e e) (vs vs))
  ;; debugging
  (when #f (assert (every meets-syntactic-constraints? vs)))
  (unless (some (lambda (b)
		 (abstract-environment=? vs (environment-binding-values b)))
		(environment-bindings e))
   (cond
    ((constant-expression? e)
     (set-environment-bindings!
      e
      (cons (new-environment-binding
	     vs
	     ;; widening case E
	     (widen-abstract-value
	      (concrete-value->abstract-value (constant-expression-value e))))
	    (environment-bindings e)))
     (for-each enqueue! (parents e)))
    ;; There is no widening case F.
    ((variable-access-expression? e)
     (set-environment-bindings!
      e
      (cons (new-environment-binding vs (first vs)) (environment-bindings e)))
     (for-each enqueue! (parents e)))
    ((lambda-expression? e)
     (set-environment-bindings!
      e
      (cons (new-environment-binding
	     vs
	     ;; Note that we don't widen vs before creating the closure.
	     ;; widening case G
	     ;; foo
	     (widen-abstract-value (new-nonrecursive-closure vs e)))
	    (environment-bindings e)))
     (for-each enqueue! (parents e)))
    ((application? e)
     (cond
      ((lambda-expression? (application-callee e))
       ;; This handling of LET is an optimization.
       (set-environment-bindings!
	e
	(cons (new-environment-binding vs (empty-abstract-value))
	      (environment-bindings e)))
       ;; Can't give an error if parent already in list since could have done
       ;; this for a different context.
       (unless (memp expression-eqv? e (parents (application-argument e)))
	(set-parents! (application-argument e)
		      (cons e (parents (application-argument e)))))
       (loop (application-argument e)
	     (restrict-environment vs (application-argument-indices e)))
       (enqueue! e))
      (else
       (set-environment-bindings!
	e
	(cons (new-environment-binding vs (empty-abstract-value))
	      (environment-bindings e)))
       ;; Can't give an error if parent already in list since could have done
       ;; this for a different context.
       (unless (memp expression-eqv? e (parents (application-callee e)))
	(set-parents! (application-callee e)
		      (cons e (parents (application-callee e)))))
       (unless (memp expression-eqv? e (parents (application-argument e)))
	(set-parents! (application-argument e)
		      (cons e (parents (application-argument e)))))
       (loop (application-callee e)
	     (restrict-environment vs (application-callee-indices e)))
       (loop (application-argument e)
	     (restrict-environment vs (application-argument-indices e)))
       (enqueue! e))))
    ((letrec-expression? e)
     (set-environment-bindings!
      e
      (cons (new-environment-binding vs (empty-abstract-value))
	    (environment-bindings e)))
     ;; Ditto.
     (unless (memp expression-eqv? e (parents (letrec-expression-body e)))
      (set-parents! (letrec-expression-body e)
		    (cons e (parents (letrec-expression-body e)))))
     ;; bar
     (loop (letrec-expression-body e) (letrec-nested-environment vs e))
     (enqueue! e))
    ((cons-expression? e)
     (set-environment-bindings!
      e
      (cons (new-environment-binding vs (empty-abstract-value))
	    (environment-bindings e)))
     ;; Ditto.
     (unless (memp expression-eqv? e (parents (cons-expression-car e)))
      (set-parents! (cons-expression-car e)
		    (cons e (parents (cons-expression-car e)))))
     (unless (memp expression-eqv? e (parents (cons-expression-cdr e)))
      (set-parents! (cons-expression-cdr e)
		    (cons e (parents (cons-expression-cdr e)))))
     (loop (cons-expression-car e)
	   (restrict-environment vs (cons-expression-car-indices e)))
     (loop (cons-expression-cdr e)
	   (restrict-environment vs (cons-expression-cdr-indices e)))
     (enqueue! e))
    (else (internal-error))))))

(define (deep-empty-abstract-value? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  26
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

(define (value-contains-unfilled? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  27
  (let outer ((v v) (vs '()) (k (lambda (r? vs) r?)))
   (cond ((real? v) (k #f vs))
	 ((memq v vs) (k #f vs))
	 ((union? v)
	  (if (eq? (union-values v) 'unfilled)
	      (k #t vs)
	      (let inner ((us (union-members v)) (vs (cons v vs)))
	       (if (null? us)
		   (k #f vs)
		   (outer (first us)
			  vs
			  (lambda (r? vs)
			   (if r? (k #t vs) (inner (rest us) vs))))))))
	 ((scalar-value? v) (k #f vs))
	 (else
	  (if (or (and (nonrecursive-closure? v)
		       (eq? (nonrecursive-closure-values v) 'unfilled))
		  (and (recursive-closure? v)
		       (eq? (recursive-closure-values v) 'unfilled))
		  (and (perturbation-tagged-value? v)
		       (eq? (perturbation-tagged-value-primal v) 'unfilled))
		  (and (bundle? v)
		       (or (eq? (bundle-primal v) 'unfilled)
			   (eq? (bundle-tangent v) 'unfilled)))
		  (and (sensitivity-tagged-value? v)
		       (eq? (sensitivity-tagged-value-primal v) 'unfilled))
		  (and (reverse-tagged-value? v)
		       (eq? (reverse-tagged-value-primal v) 'unfilled))
		  (and (vlad-pair? v)
		       (or (eq? (vlad-pair-car v) 'unfilled)
			   (eq? (vlad-pair-cdr v) 'unfilled))))
	      (k #t vs)
	      (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
	       (if (null? vs1)
		   (k #f vs)
		   (outer (first vs1)
			  vs
			  (lambda (r? vs)
			   (if r? (k #t vs) (inner (rest vs1) vs))))))))))))

(define (value-contains-union? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  28
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
  29
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
  30
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
  31
  (let outer ((v v) (vs '()) (n '()) (k (lambda (n vs) n)))
   (cond
    ((real? v) (k (if (memv v n) n (cons v n)) vs))
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
    (else (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)) (n n))
	   (if (null? vs1)
	       (k n vs)
	       (outer (first vs1)
		      vs
		      n
		      (lambda (n vs) (inner (rest vs1) vs n))))))))))

(define (value-size v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  32
  (let outer ((v v) (vs '()) (n 0) (k (lambda (n vs) n)))
   (cond
    ((memq v vs) (k n vs))
    ;; We intentionally omit the special case for real here but not elsewhere.
    ((union? v)
     (let inner ((us (union-members v)) (vs (cons v vs)) (n (+ n 1)))
      (if (null? us)
	  (k n vs)
	  (outer (first us) vs n (lambda (n vs) (inner (rest us) vs n))))))
    ;; We intentionally cons here but not elsewhere.
    ((scalar-value? v) (k (+ n 1) (cons v vs)))
    (else (let inner ((vs1 (aggregate-value-values v))
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
  33
  (let outer ((v v) (vs '()) (n 0) (k (lambda (n vs) n)))
   (cond
    ((real? v) (k (max n 1) vs))
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
 (map-reduce + 0 (lambda (e) (length (environment-bindings e))) *expressions*))

(define (max-flow-size)
 (map-reduce max
	     minus-infinity
	     (lambda (e) (length (environment-bindings e)))
	     *expressions*))

(define (analysis-contains-union?)
 (some (lambda (e)
	(some (lambda (b)
	       (or (some value-contains-union?
			 (environment-binding-values b))
		   (value-contains-union? (environment-binding-value b))))
	      (environment-bindings e)))
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
    (environment-bindings e)))
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
    (environment-bindings e)))
  *expressions*))

(define (bottoms-in-analysis)
 (map-reduce
  +
  0
  (lambda (e)
   (count-if (lambda (b) (empty-abstract-value? (environment-binding-value b)))
	     (environment-bindings e)))
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
    (environment-bindings e)))
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
    (environment-bindings e)))
  *expressions*))

(define (check-canonize-cache! v)
 (cond ((union? v) (assert (eq? (union-canonize-cache v) v)))
       ((scalar-value? v) #f)
       ((nonrecursive-closure? v)
	(assert (eq? (nonrecursive-closure-canonize-cache v) v)))
       ((recursive-closure? v)
	(assert (eq? (recursive-closure-canonize-cache v) v)))
       ((perturbation-tagged-value? v)
	(assert (eq? (perturbation-tagged-value-canonize-cache v) v)))
       ((bundle? v) (assert (eq? (bundle-canonize-cache v) v)))
       ((sensitivity-tagged-value? v)
	(assert (eq? (sensitivity-tagged-value-canonize-cache v) v)))
       ((reverse-tagged-value? v)
	(assert (eq? (reverse-tagged-value-canonize-cache v) v)))
       ((vlad-pair? v) (assert (eq? (vlad-pair-canonize-cache v) v)))
       (else (internal-error))))

(define (check-intern-cache! v)
 (cond ((union? v) (assert (eq? (union-intern-cache v) v)))
       ((scalar-value? v) #f)
       ((nonrecursive-closure? v)
	(assert (eq? (nonrecursive-closure-intern-cache v) v)))
       ((recursive-closure? v)
	(assert (eq? (recursive-closure-intern-cache v) v)))
       ((perturbation-tagged-value? v)
	(assert (eq? (perturbation-tagged-value-intern-cache v) v)))
       ((bundle? v) (assert (eq? (bundle-intern-cache v) v)))
       ((sensitivity-tagged-value? v)
	(assert (eq? (sensitivity-tagged-value-intern-cache v) v)))
       ((reverse-tagged-value? v)
	(assert (eq? (reverse-tagged-value-intern-cache v) v)))
       ((vlad-pair? v) (assert (eq? (vlad-pair-intern-cache v) v)))
       (else (internal-error))))

(define (check-filled! v)
 (cond ((union? v) (assert (not (eq? (union-values v) 'unfilled))))
       ((scalar-value? v) #f)
       ((nonrecursive-closure? v)
	(assert (not (eq? (nonrecursive-closure-values v) 'unfilled))))
       ((recursive-closure? v)
	(assert (not (eq? (recursive-closure-values v) 'unfilled))))
       ((perturbation-tagged-value? v)
	(assert (not (eq? (perturbation-tagged-value-primal v) 'unfilled))))
       ((bundle? v)
	(assert (and (not (eq? (bundle-primal v) 'unfilled))
		     (not (eq? (bundle-tangent v) 'unfilled)))))
       ((sensitivity-tagged-value? v)
	(assert (not (eq? (sensitivity-tagged-value-primal v) 'unfilled))))
       ((reverse-tagged-value? v)
	(assert (not (eq? (reverse-tagged-value-primal v) 'unfilled))))
       ((vlad-pair? v)
	(assert (and (not (eq? (vlad-pair-car v) 'unfilled))
		     (not (eq? (vlad-pair-cdr v) 'unfilled)))))
       (else (internal-error))))

(define (check-interned! v)
 (cond ((union? v) (assert (memq v *unions*)))
       ((scalar-value? v) #f)
       ((nonrecursive-closure? v) (assert (memq v *nonrecursive-closures*)))
       ((recursive-closure? v) (assert (memq v *recursive-closures*)))
       ((perturbation-tagged-value? v)
	(assert (memq v *perturbation-tagged-values*)))
       ((bundle? v) (assert (memq v *bundles*)))
       ((sensitivity-tagged-value? v)
	(assert (memq v *sensitivity-tagged-values*)))
       ((reverse-tagged-value? v) (assert (memq v *reverse-tagged-values*)))
       ((vlad-pair? v) (assert (memq v *vlad-pairs*)))
       (else (internal-error))))

(define (check-no-nested-or-singleton-unions! v)
 (when (union? v)
  (assert (and (not (some union? (get-union-values v)))
	       (not (= (length (get-union-values v)) 1))))))

(define (check-no-empty-slots! v)
 (unless (or (union? v) (scalar-value? v))
  (for-each (lambda (v) (assert (not (empty-abstract-value? v))))
	    (aggregate-value-values v))))

(define (check-slots-interned! v)
 (cond ((union? v) (for-each check-interned! (get-union-values v)))
       ((scalar-value? v) #f)
       (else (for-each check-interned! (aggregate-value-values v)))))

(define (check-no-subsumptions! v)
 (when (union? v)
  (for-each-indexed
   (lambda (u1 i1)
    (for-each-indexed
     (lambda (u2 i2)
      (assert (or (= i1 i2) (not (abstract-value-subset? u1 u2)))))
     (union-members v)))
   (union-members v))))

(define (check-abstract-value! v)
 (check-canonize-cache! v)
 (check-intern-cache! v)
 (check-filled! v)
 (check-no-nested-or-singleton-unions! v)
 (check-no-empty-slots! v)
 (check-slots-interned! v)
 (check-no-subsumptions! v))

(define (for-each-interned-abstract-value! f)
 (for-each f *unions*)
 (for-each f *nonrecursive-closures*)
 (for-each f *recursive-closures*)
 (for-each f *perturbation-tagged-values*)
 (for-each f *bundles*)
 (for-each f *sensitivity-tagged-values*)
 (for-each f *reverse-tagged-values*)
 (for-each f *vlad-pairs*))

(define (check-no-duplicate-interned-abstract-values!)
 (define (check-no-duplicate-interned-abstract-values! vs)
  (for-each-indexed
   (lambda (v1 i1)
    (for-each-indexed
     (lambda (v2 i2)
      (assert (or (= i1 i2) (not (deep-abstract-value=? v1 v2)))))
     vs))
   vs))
 (check-no-duplicate-interned-abstract-values! *unions*)
 (check-no-duplicate-interned-abstract-values! *nonrecursive-closures*)
 (check-no-duplicate-interned-abstract-values! *recursive-closures*)
 (check-no-duplicate-interned-abstract-values! *perturbation-tagged-values*)
 (check-no-duplicate-interned-abstract-values! *bundles*)
 (check-no-duplicate-interned-abstract-values! *sensitivity-tagged-values*)
 (check-no-duplicate-interned-abstract-values! *reverse-tagged-values*)
 (check-no-duplicate-interned-abstract-values! *vlad-pairs*))

(define (walk-abstract-value! f v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  34
  (let outer ((v v) (vs '()) (k (lambda (vs) #f)))
   (f v)
   (cond ((real? v) (k vs))
	 ((memq v vs) (k vs))
	 ((union? v)
	  (let inner ((us (union-members v)) (vs (cons v vs)))
	   (if (null? us)
	       (k vs)
	       (outer (first us) vs (lambda (vs) (inner (rest us) vs))))))
	 ((scalar-value? v) (k vs))
	 (else (let inner ((vs1 (aggregate-value-values v)) (vs (cons v vs)))
		(if (null? vs1)
		    (k vs)
		    (outer (first vs1)
			   vs
			   (lambda (vs) (inner (rest vs1) vs))))))))))

(define (check-analysis!)
 (for-each
  (lambda (e)
   (for-each (lambda (b)
	      (for-each check-interned! (environment-binding-values b))
	      (check-interned! (environment-binding-value b)))
	     (environment-bindings e)))
  *expressions*)
 (for-each-interned-abstract-value! check-abstract-value!)
 (check-no-duplicate-interned-abstract-values!))

(define (verbosity)
 (format #t
	 "expressions: ~s, |analysis|=~s, max flow size: ~s, |queue|=~s~%unions: ~s, bottoms: ~s, max size: ~s, max width: ~s~%concrete reals: ~s~%"
	 (count-if (lambda (e) (not (null? (environment-bindings e))))
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
 (with-abstract
  (lambda ()
   (abstract-eval-prime!
    e
    (map
     (lambda (x)
      (value-binding-value
       (find-if (lambda (b) (variable=? x (value-binding-variable b))) bs)))
     (free-variables e)))
   (let loop ((i 0))
    (when (and
	   *verbose* (not (zero? *verbose*)) (zero? (remainder i *verbose*)))
     (verbosity))
    (unless (null? *queue*)
     (let ((e (first *queue*)))
      (set! *queue* (rest *queue*))
      (assert (enqueue? e))
      (set-enqueue?! e #f)
      (abstract-eval! e))
     (loop (+ i 1))))
   (check-analysis!)
   (when *verbose* (verbosity)))))

;;; Must-alias
;;; needs work: This is all put here for now to put all must-alias stuff in
;;;             one place in case I need to rip it out. But eventually, the
;;;             components of this will all be moved to their appropriate
;;;             places.

(define-structure tag abstract-value)

(define-structure color index pointer index2)

(define *color-index* 0)

(define (new-color)
 (set! *color-index* (+ *color-index* 1))
 (make-color *color-index* #f #f))

(define (dereference-color color)
 (if (color-pointer color) (dereference-color (color-pointer color)) color))

(define (color-index-of color) (color-index (dereference-color color)))

(define (color=? color1 color2)
 (eq? (dereference-color color1) (dereference-color color2)))

(define (equate-color! color1 color2)
 (unless (color=? color1 color2)
  (let ((color2 (dereference-color color2)))
   (let loop ((color1 color1))
    (if (color-pointer color1)
	(let ((color (color-pointer color1)))
	 (set-color-pointer! color1 color2)
	 (loop color))
	(set-color-pointer! color1 color2))))))

;;; needs work: should abstract reduce, append, length, null?, ... on aliases

(define (empty-alias) '())

(define (slot=? v1 v2)
 (or (and (tag? v1)
	  (tag? v2)
	  (abstract-value=? (tag-abstract-value v1) (tag-abstract-value v2)))
     (and (not (tag? v1)) (not (tag? v2)) (abstract-value=? v1 v2))))

(define (alias-for v)
 (let ((a (map-n-vector (lambda (i) (new-color)) (number-of-slots v))))
  (for-each (lambda (is)
	     (for-each (lambda (i1 i2)
			(equate-color! (vector-ref a i1) (vector-ref a i2)))
		       (but-last is)
		       (rest is)))
	    (equivalent-slot-indices v))
  (vector->list a)))

(define (aliases-for vs)
 (let* ((vs (map-reduce append '() slots vs))
	(a (map-n-vector (lambda (i) (new-color)) (length vs))))
  (for-each
   (lambda (v-is)
    (for-each
     (lambda (v-i1 v-i2)
      (equate-color! (vector-ref a (cdr v-i1)) (vector-ref a (cdr v-i2))))
     (but-last v-is)
     (rest v-is)))
   (transitive-equivalence-classesp
    (lambda (v-i1 v-i2) (slot=? (car v-i1) (car v-i2)))
    (map-indexed cons vs)))
  (vector->list a)))

(define (add-tag-alias v a)
 (assert (and (union? v) (not (= (length (get-union-values v)) 1))))
 (if (empty-abstract-value? v) a (cons (new-color) a)))

(define (copy-alias a)
 (for-each (lambda (color)
	    (let loop ((color color))
	     (set-color-index2! color #f)
	     (when (color-pointer color) (loop (color-pointer color)))))
	   a)
 (for-each-indexed (lambda (color i)
		    (unless (color-index2 color) (set-color-index2! color i)))
		   a)
 (let ((a-prime (map-n-vector (lambda (i) (new-color)) (length a)))
       (indices
	(removeq
	 #f
	 (map-indexed
	  (lambda (color i) (if (color-index2 (dereference-color color)) #f i))
	  a))))
  (for-each-indexed
   (lambda (color i)
    (when (color-index2 (dereference-color color))
     (equate-color!
      (vector-ref a-prime i)
      (vector-ref a-prime (color-index2 (dereference-color color))))))
   a)
  (let ((a (list->vector a)))
   (let loop ((indices indices))
    (unless (null? indices)
     (let ((i (first indices)))
      (for-each
       (lambda (j)
	(when (color=? (vector-ref a i) (vector-ref a j))
	 (equate-color! (vector-ref a-prime i) (vector-ref a-prime j))))
       (rest indices)))
     (loop (rest indices)))))
  (vector->list a-prime)))

(define (coalesce-aliases as)
 (assert (and (not (null? as))
	      (= (length (remove-duplicatesv (map length as))) 1)))
 (let ((a (find-if
	   (lambda (a)
	    (for-each
	     (lambda (color)
	      (let loop ((color color))
	       (set-color-index2! color #f)
	       (when (color-pointer color) (loop (color-pointer color)))))
	     a)
	    (for-each-indexed
	     (lambda (color i)
	      (unless (color-index2 color) (set-color-index2! color i)))
	     a)
	    (let ((indices
		   (removeq
		    #f
		    (map-indexed
		     (lambda (color i)
		      (if (color-index2 (dereference-color color)) #f i))
		     a)))
		  (a (list->vector a))
		  (as (map list->vector as)))
	     (and
	      (every-n
	       (lambda (i)
		(let ((j (color-index2 (dereference-color (vector-ref a i)))))
		 (or (not j)
		     (every (lambda (a)
			     (color=? (vector-ref a i) (vector-ref a j)))
			    as))))
	       (vector-length a))
	      (let loop ((indices indices))
	       (or (null? indices)
		   (let ((i (first indices)))
		    (and
		     (every
		      (lambda (j)
		       (or (not (color=? (vector-ref a i) (vector-ref a j)))
			   (every (lambda (a)
				   (color=? (vector-ref a i) (vector-ref a j)))
				  as)))
		      (rest indices))
		     (loop (rest indices)))))))))
	   as)))
  (if (eq? a #f)
      (let ((a-prime (map (lambda (color) (new-color)) (first as))))
       (let outer ((colors1-list as) (colors1-prime a-prime))
	(unless (null? (first colors1-list))
	 (let ((color1-list (map first colors1-list))
	       (color1-prime (first colors1-prime)))
	  (let inner ((colors2-list (map rest colors1-list))
		      (colors2-prime (rest colors1-prime)))
	   (unless (null? (first colors2-list))
	    (let ((color2-list (map first colors2-list))
		  (color2-prime (first colors2-prime)))
	     (when (every color=? color1-list color2-list)
	      (equate-color! color1-prime color2-prime)))
	    (inner (map rest colors2-list) (rest colors2-prime)))))
	 (outer (map rest colors1-list) (rest colors1-prime))))
       a-prime)
      (copy-alias a))))

(define (compatible-alias? v a)
 ;; We could try to speed up compatible-alias? but we don't bother since it is
 ;; only called in assertions.
 (assert (and (list? a) (every color? a)))
 (let ((vs (slots v)))
  (and (= (length vs) (length a))
       (every (lambda (v1 color1)
	       (every (lambda (v2 color2)
		       (or (not (color=? color1 color2)) (slot=? v1 v2)))
		      vs
		      a))
	      vs
	      a))))

(define (widen-alias v1 a1 v2 top?)
 (assert (compatible-alias? v1 a1))
 (let ((a2
	(cond
	 ((abstract-value=? v1 v2) a1)
	 ((and (not top?) (not (inline? (lookup-widener-instance v1 v2))))
	  (let ((instance (lookup-widener-instance v1 v2)))
	   (set-new-input-aliases!
	    instance (cons a1 (new-input-aliases instance)))
	   (copy-alias (output-alias instance))))
	 ((union? v1)
	  (if (empty-abstract-value? v1)
	      ;; I don't know if this will foil the must-alias analysis.
	      (alias-for v2)
	      (coalesce-aliases (map (lambda (u1 a1) (widen-alias u1 a1 v2 #f))
				     (get-union-values v1)
				     (get-union-alias-values v1 a1)))))
	 ((union? v2)
	  (assert (not (empty-abstract-value? v2)))
	  (let* ((us2 (get-union-values v2))
		 (i (position-if
		     (lambda (u2-prime) (abstract-value-subset? v1 u2-prime))
		     us2)))
	   (assert i)
	   (let* ((vs (list->vector ((if (boxed? v2) boxed-slots slots) v2)))
		  (a (map-n-vector (lambda (v) (new-color))
				   (vector-length vs)))
		  (ns (map number-of-slots us2))
		  (a-prime
		   (list->vector (widen-alias v1 a1 (list-ref us2 i) #f))))
	    (for-each-indexed
	     (lambda (n1 i1)
	      (let ((j1 (+ (reduce + (sublist ns 0 i1) 0) 1)))
	       (for-each-indexed
		(lambda (n2 i2)
		 (let ((j2 (+ (reduce + (sublist ns 0 i2) 0) 1)))
		  (for-each-n
		   (lambda (k1)
		    (let ((v1 (vector-ref vs (+ j1 k1)))
			  (color1 (vector-ref a (+ j1 k1))))
		     (for-each-n
		      (lambda (k2)
		       (let ((v2 (vector-ref vs (+ j2 k2)))
			     (color2 (vector-ref a (+ j2 k2))))
			(when (or (and (not (= i1 i))
				       (not (= i2 i))
				       (slot=? v1 v2))
				  (and (= i1 i)
				       (= i2 i)
				       (color=? (vector-ref a-prime k1)
						(vector-ref a-prime k2))))
			 (equate-color! color1 color2))))
		      n2)))
		   n1)))
		ns)))
	     ns)
	    (let ((n2 (list-ref ns i))
		  (j2 (+ (reduce + (sublist ns 0 i) 0) 1)))
	     (for-each-indexed
	      (lambda (n1 i1)
	       (unless (= i1 i)
		(let ((j1 (+ (reduce + (sublist ns 0 i1) 0) 1)))
		 (for-each-n
		  (lambda (k1)
		   (let ((v1 (vector-ref vs (+ j1 k1)))
			 (color1 (vector-ref a (+ j1 k1))))
		    (for-each-n
		     (lambda (k2)
		      (let ((v2 (vector-ref vs (+ j2 k2)))
			    (color2 (vector-ref a (+ j2 k2))))
		       (when (and (not (color-pointer color1))
				  (not (color-pointer color2))
				  (slot=? v1 v2))
			;; i2/color2 (i2=i) corresponds to the member in v2
			;; that v1 is widened to.
			;; i1/color1 (i1/=i) corresponds to the other members.
			;; This crucially sets color1 to point to color2 so
			;; that after this (not (color-pointer color1)) is #f.
			;; Because the first disjunct of the previous loop
			;; causes all slots of the same type to be equated.
			;; And you want such an equivalence class to only be
			;; equated to at most one such color2. If it were
			;; equated to two different color2s then this would
			;; unsoundly equate those two color2s.
			(equate-color! color1 color2))))
		     n2)))
		  n1))))
	      ns))
	    (let ((a (cond ((boxed? v2)
			    (set-new-aliases!
			     v2 (cons (vector->list a) (new-aliases v2)))
			    (alias-for v2))
			   (else (vector->list a)))))
	     (assert (compatible-alias? v2 a))
	     a))))
	 ((and (vlad-real? v1) (abstract-real? v2))
	  (if (real? v1) (alias-for v2) a1))
	 ((and (nonrecursive-closure? v1)
	       (nonrecursive-closure? v2)
	       ;; This used to use a nondereferencing closure match.
	       (nonrecursive-closure-match? v1 v2))
	  (new-alias-nonrecursive-closure
	   (get-nonrecursive-closure-values v2)
	   (map (lambda (u1 u2 a1) (widen-alias u1 a1 u2 #f))
		(get-nonrecursive-closure-values v1)
		(get-nonrecursive-closure-values v2)
		(get-nonrecursive-closure-alias-values v1 a1))
	   (nonrecursive-closure-lambda-expression v2)))
	 ((and (recursive-closure? v1)
	       (recursive-closure? v2)
	       ;; This used to use a nondereferencing closure match.
	       (recursive-closure-match? v1 v2))
	  (new-alias-recursive-closure
	   (get-recursive-closure-values v2)
	   (map (lambda (u1 u2 a1) (widen-alias u1 a1 u2 #f))
		(get-recursive-closure-values v1)
		(get-recursive-closure-values v2)
		(get-recursive-closure-alias-values v1 a1))
	   (recursive-closure-procedure-variables v2)
	   (recursive-closure-lambda-expressions v2)
	   (recursive-closure-index v2)))
	 ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	  (new-alias-perturbation-tagged-value
	   (get-perturbation-tagged-value-primal v2)
	   (widen-alias (get-perturbation-tagged-value-primal v1)
			(get-perturbation-tagged-value-primal-alias v1 a1)
			(get-perturbation-tagged-value-primal v2)
			#f)))
	 ((and (bundle? v1) (bundle? v2))
	  (let ((as1 (get-bundle-aliases v1 a1)))
	   (new-alias-bundle
	    (get-bundle-primal v2)
	    (widen-alias
	     (get-bundle-primal v1) (first as1) (get-bundle-primal v2) #f)
	    (get-bundle-tangent v2)
	    (widen-alias (get-bundle-tangent v1)
			 (second as1)
			 (get-bundle-tangent v2)
			 #f))))
	 ((and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	  (new-alias-sensitivity-tagged-value
	   (get-sensitivity-tagged-value-primal v2)
	   (widen-alias (get-sensitivity-tagged-value-primal v1)
			(get-sensitivity-tagged-value-primal-alias v1 a1)
			(get-sensitivity-tagged-value-primal v2)
			#f)))
	 ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	  (new-alias-reverse-tagged-value
	   (get-reverse-tagged-value-primal v2)
	   (widen-alias (get-reverse-tagged-value-primal v1)
			(get-reverse-tagged-value-primal-alias v1 a1)
			(get-reverse-tagged-value-primal v2)
			#f)))
	 ((and (vlad-pair? v1) (vlad-pair? v2))
	  (vlad-cons-alias
	   (vlad-car v2)
	   (widen-alias
	    (vlad-car v1) (vlad-car-alias v1 a1) (vlad-car v2) #f)
	   (vlad-cdr v2)
	   (widen-alias
	    (vlad-cdr v1) (vlad-cdr-alias v1 a1) (vlad-cdr v2) #f)))
	 (else (internal-error)))))
  (assert (compatible-alias? v2 a2))
  a2))

(define (alias=? a1 a2)
 ;; This used to assume that a2 is the old alias and a1 is the new alias
 ;; because it used to check that any alias in a1 must be present in a2 but
 ;; (I forget why and the example that illustrates this but) this is not the
 ;; case.
 (assert (= (length a1) (length a2)))
 (for-each (lambda (color)
	    (let loop ((color color))
	     (set-color-index2! color #f)
	     (when (color-pointer color) (loop (color-pointer color)))))
	   a1)
 (for-each (lambda (color)
	    (let loop ((color color))
	     (set-color-index2! color #f)
	     (when (color-pointer color) (loop (color-pointer color)))))
	   a2)
 (for-each-indexed (lambda (color i)
		    (unless (color-index2 color) (set-color-index2! color i)))
		   a1)
 (for-each-indexed (lambda (color i)
		    (unless (color-index2 color) (set-color-index2! color i)))
		   a2)
 (let ((indices1
	(removeq
	 #f
	 (map-indexed
	  (lambda (color i) (if (color-index2 (dereference-color color)) #f i))
	  a1)))
       (indices2
	(removeq
	 #f
	 (map-indexed
	  (lambda (color i) (if (color-index2 (dereference-color color)) #f i))
	  a2)))
       (a1 (list->vector a1))
       (a2 (list->vector a2)))
  (and
   (every-n (lambda (i)
	     (let ((j (color-index2 (dereference-color (vector-ref a1 i)))))
	      (or (not j) (color=? (vector-ref a2 i) (vector-ref a2 j)))))
	    (vector-length a1))
   (every-n (lambda (i)
	     (let ((j (color-index2 (dereference-color (vector-ref a2 i)))))
	      (or (not j) (color=? (vector-ref a1 i) (vector-ref a1 j)))))
	    (vector-length a2))
   (let loop ((indices indices1))
    (or (null? indices)
	(let ((i (first indices)))
	 (and (every (lambda (j)
		      (or (not (color=? (vector-ref a1 i) (vector-ref a1 j)))
			  (color=? (vector-ref a2 i) (vector-ref a2 j))))
		     (rest indices))
	      (loop (rest indices))))))
   (let loop ((indices indices2))
    (or (null? indices)
	(let ((i (first indices)))
	 (and (every (lambda (j)
		      (or (not (color=? (vector-ref a2 i) (vector-ref a2 j)))
			  (color=? (vector-ref a1 i) (vector-ref a1 j))))
		     (rest indices))
	      (loop (rest indices)))))))))

(define (slots v)
 (let ((vs '()))
  (let loop ((v v))
   (cond ((boxed? v) (set! vs (cons v vs)))
	 ((empty-abstract-value? v) #f)
	 ((union? v)
	  (set! vs (cons (make-tag v) vs))
	  (for-each loop (get-union-values v)))
	 ((abstract-real? v) (set! vs (cons v vs)))
	 ((scalar-value? v) #f)
	 ((nonrecursive-closure? v)
	  (for-each loop (get-nonrecursive-closure-values v)))
	 ((recursive-closure? v)
	  (for-each loop (get-recursive-closure-values v)))
	 ((perturbation-tagged-value? v)
	  (loop (get-perturbation-tagged-value-primal v)))
	 ((bundle? v)
	  (loop (get-bundle-primal v))
	  (loop (get-bundle-tangent v)))
	 ((sensitivity-tagged-value? v)
	  (loop (get-sensitivity-tagged-value-primal v)))
	 ((reverse-tagged-value? v) (loop (get-reverse-tagged-value-primal v)))
	 ((vlad-pair? v)
	  (loop (vlad-car v))
	  (loop (vlad-cdr v)))
	 (else (internal-error))))
  (reverse vs)))

(define (number-of-slots v) (length (slots v)))

(define (equivalent-slot-indices v)
 (cond
  ((union? v) (union-equivalent-slot-indices v))
  ((abstract-real? v) '((0)))
  ((scalar-value? v) '())
  ((nonrecursive-closure? v) (nonrecursive-closure-equivalent-slot-indices v))
  ((recursive-closure? v) (recursive-closure-equivalent-slot-indices v))
  ((perturbation-tagged-value? v)
   (perturbation-tagged-value-equivalent-slot-indices v))
  ((bundle? v) (bundle-equivalent-slot-indices v))
  ((sensitivity-tagged-value? v)
   (sensitivity-tagged-value-equivalent-slot-indices v))
  ((reverse-tagged-value? v)
   (reverse-tagged-value-equivalent-slot-indices v))
  ((vlad-pair? v) (vlad-pair-equivalent-slot-indices v))
  (else (internal-error))))

(define (boxed-slots v)
 (assert (boxed? v))
 (let ((vs '()))
  (let loop ((v v) (top? #t))
   (define (internal v) (loop v #f))
   (cond
    ((and (not top?) (boxed? v)) (set! vs (cons v vs)))
    ((empty-abstract-value? v) #f)
    ((union? v)
     (set! vs (cons (make-tag v) vs))
     (for-each internal (get-union-values v)))
    ((abstract-real? v) (set! vs (cons v vs)))
    ((scalar-value? v) #f)
    ((nonrecursive-closure? v)
     (for-each internal (get-nonrecursive-closure-values v)))
    ((recursive-closure? v)
     (for-each internal (get-recursive-closure-values v)))
    ((perturbation-tagged-value? v)
     (internal (get-perturbation-tagged-value-primal v)))
    ((bundle? v)
     (internal (get-bundle-primal v))
     (internal (get-bundle-tangent v)))
    ((sensitivity-tagged-value? v)
     (internal (get-sensitivity-tagged-value-primal v)))
    ((reverse-tagged-value? v) (internal (get-reverse-tagged-value-primal v)))
    ((vlad-pair? v)
     (internal (vlad-car v))
     (internal (vlad-cdr v)))
    (else (internal-error))))
  (reverse vs)))

(define (split-alias a ns)
 (cond ((null? ns)
	(assert (null? a))
	'())
       (else
	(cons (sublist a 0 (first ns))
	      (split-alias (sublist a (first ns) (length a)) (rest ns))))))

(define (new-alias-nonrecursive-closure vs as e)
 (assert (and (= (length vs) (length as)) (every compatible-alias? vs as)))
 (let ((u (new-nonrecursive-closure vs e)))
  (cond ((boxed? u)
	 (set-new-aliases!
	  u (cons (reduce append as (empty-alias)) (new-aliases u)))
	 (alias-for u))
	(else (reduce append as (empty-alias))))))

(define (get-nonrecursive-closure-alias-values u a)
 (assert (compatible-alias? u a))
 (split-alias (if (boxed? u) (copy-alias (alias u)) a)
	      (map number-of-slots (get-nonrecursive-closure-values u))))

(define (new-alias-recursive-closure vs as xs es i)
 (assert (and (= (length vs) (length as)) (every compatible-alias? vs as)))
 (let ((u (new-recursive-closure vs xs es i)))
  (cond ((boxed? u)
	 (set-new-aliases!
	  u (cons (reduce append as (empty-alias)) (new-aliases u)))
	 (alias-for u))
	(else (reduce append as (empty-alias))))))

(define (get-recursive-closure-alias-values u a)
 (assert (compatible-alias? u a))
 (split-alias (if (boxed? u) (copy-alias (alias u)) a)
	      (map number-of-slots (get-recursive-closure-values u))))

(define (get-closure-alias-values u a)
 (cond ((nonrecursive-closure? u) (get-nonrecursive-closure-alias-values u a))
       ((recursive-closure? u) (get-recursive-closure-alias-values u a))
       (else (internal-error))))

(define (closure-ref-alias v a x)
 (list-ref (get-closure-alias-values v a)
	   (positionp variable=? x (closure-variables v))))

(define (tagged-new-alias-nonrecursive-closure tags vs as e)
 (if (empty-tags? tags)
     (new-alias-nonrecursive-closure vs as e)
     (case (first tags)
      ((perturbation)
       (perturb-alias (tagged-new-nonrecursive-closure
		       (remove-tag 'perturbation tags)
		       (map unperturb vs)
		       (perturbation-transform-inverse e))
		      (tagged-new-alias-nonrecursive-closure
		       (remove-tag 'perturbation tags)
		       (map unperturb vs)
		       (map (lambda (v a) (unperturb-alias v a #f)) vs as)
		       (perturbation-transform-inverse e))
		      #f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-new-nonrecursive-closure
		    (remove-tag 'forward tags)
		    (map primal vs)
		    (forward-transform-inverse e))
		   (perturb (tagged-new-nonrecursive-closure
			     (remove-tag 'forward tags)
			     (map unperturb (map tangent vs))
			     (forward-transform-inverse e))))
	(vlad-cons-alias
	 (tagged-new-nonrecursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (forward-transform-inverse e))
	 (tagged-new-alias-nonrecursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (map (lambda (v a) (primal-alias v a #f)) vs as)
	  (forward-transform-inverse e))
	 (perturb (tagged-new-nonrecursive-closure
		   (remove-tag 'forward tags)
		   (map unperturb (map tangent vs))
		   (forward-transform-inverse e)))
	 (perturb-alias
	  (tagged-new-nonrecursive-closure
	   (remove-tag 'forward tags)
	   (map unperturb (map tangent vs))
	   (forward-transform-inverse e))
	  (tagged-new-alias-nonrecursive-closure
	   (remove-tag 'forward tags)
	   (map unperturb (map tangent vs))
	   (unperturb-alias (map tangent vs)
			    (map (lambda (v a) (tangent-alias v a #f)) vs as)
			    #f)
	   (forward-transform-inverse e))
	  #f))
	#f))
      ((sensitivity)
       (sensitize-alias (tagged-new-nonrecursive-closure
			 (remove-tag 'sensitivity tags)
			 (map unsensitize vs)
			 (sensitivity-transform-inverse e))
			(tagged-new-alias-nonrecursive-closure
			 (remove-tag 'sensitivity tags)
			 (map unsensitize vs)
			 (map (lambda (v a) (unsensitize-alias v a #f)) vs as)
			 (sensitivity-transform-inverse e))
			#f))
      ((reverse)
       (*j-alias (tagged-new-nonrecursive-closure
		  (remove-tag 'reverse tags)
		  (map *j-inverse vs)
		  (reverse-transform-inverse e))
		 (tagged-new-alias-nonrecursive-closure
		  (remove-tag 'reverse tags)
		  (map *j-inverse vs)
		  (map (lambda (v a) (*j-inverse-alias v a #f)) vs as)
		  (reverse-transform-inverse e))
		 #f))
      (else (internal-error)))))

(define (tagged-new-alias-recursive-closure tags vs as xs es i)
 (if (empty-tags? tags)
     (new-alias-recursive-closure vs as xs es i)
     (case (first tags)
      ((perturbation)
       (perturb-alias (tagged-new-recursive-closure
		       (remove-tag 'perturbation tags)
		       (map unperturb vs)
		       (map-vector unperturbationify xs)
		       (map-vector perturbation-transform-inverse es)
		       i)
		      (tagged-new-alias-recursive-closure
		       (remove-tag 'perturbation tags)
		       (map unperturb vs)
		       (map (lambda (v a) (unperturb-alias v a #f)) vs as)
		       (map-vector unperturbationify xs)
		       (map-vector perturbation-transform-inverse es)
		       i)
		      #f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-new-recursive-closure
		    (remove-tag 'forward tags)
		    (map primal vs)
		    (map-vector unforwardify xs)
		    (map-vector forward-transform-inverse es)
		    i)
		   (perturb (tagged-new-recursive-closure
			     (remove-tag 'forward tags)
			     (map unperturb (map tangent vs))
			     (map-vector unforwardify xs)
			     (map-vector forward-transform-inverse es)
			     i)))
	(vlad-cons-alias
	 (tagged-new-recursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (map-vector unforwardify xs)
	  (map-vector forward-transform-inverse es)
	  i)
	 (tagged-new-alias-recursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (map (lambda (v a) (primal-alias v a #f)) vs as)
	  (map-vector unforwardify xs)
	  (map-vector forward-transform-inverse es)
	  i)
	 (perturb (tagged-new-recursive-closure
		   (remove-tag 'forward tags)
		   (map unperturb (map tangent vs))
		   (map-vector unforwardify xs)
		   (map-vector forward-transform-inverse es)
		   i))
	 (perturb-alias (tagged-new-recursive-closure
			 (remove-tag 'forward tags)
			 (map unperturb (map tangent vs))
			 (map-vector unforwardify xs)
			 (map-vector forward-transform-inverse es)
			 i)
			(tagged-new-alias-recursive-closure
			 (remove-tag 'forward tags)
			 (map unperturb (map tangent vs))
			 (unperturb-alias
			  (map tangent vs)
			  (map (lambda (v a) (tangent-alias v a #f)) vs as)
			  #f)
			 (map-vector unforwardify xs)
			 (map-vector forward-transform-inverse es)
			 i)
			#f))
	#f))
      ((sensitivity)
       (sensitize-alias (tagged-new-recursive-closure
			 (remove-tag 'sensitivity tags)
			 (map unsensitize vs)
			 (map-vector unsensitivityify xs)
			 (map-vector sensitivity-transform-inverse es)
			 i)
			(tagged-new-alias-recursive-closure
			 (remove-tag 'sensitivity tags)
			 (map unsensitize vs)
			 (map (lambda (v a) (unsensitize-alias v a #f)) vs as)
			 (map-vector unsensitivityify xs)
			 (map-vector sensitivity-transform-inverse es)
			 i)
			#f))
      ((reverse)
       (*j-alias (tagged-new-recursive-closure
		  (remove-tag 'reverse tags)
		  (map *j-inverse vs)
		  (map-vector unreverseify xs)
		  (map-vector reverse-transform-inverse es)
		  i)
		 (tagged-new-alias-recursive-closure
		  (remove-tag 'reverse tags)
		  (map *j-inverse vs)
		  (map (lambda (v a) (*j-inverse-alias v a #f)) vs as)
		  (map-vector unreverseify xs)
		  (map-vector reverse-transform-inverse es)
		  i)
		 #f))
      (else (internal-error)))))

(define (tagged-closure-ref-alias tags v a x)
 (if (empty-tags? tags)
     (cond ((union? v)
	    ;; widening case M3
	    (unionize-alias
	     (map (lambda (u)
		   (if (closure? u) (closure-ref u x) (empty-abstract-value)))
		  (get-union-values v))
	     (map (lambda (u a)
		   (if (closure? u) (closure-ref-alias u a x) (empty-alias)))
		  (get-union-values v)
		  (get-union-alias-values v a))))
	   ((closure? v) (closure-ref-alias v a x))
	   (else (empty-alias)))
     (case (first tags)
      ((perturbation)
       (perturb-alias (tagged-closure-ref (remove-tag 'perturbation tags)
					  (unperturb v)
					  (unperturbationify x))
		      (tagged-closure-ref-alias (remove-tag 'perturbation tags)
						(unperturb v)
						(unperturb-alias v a #f)
						(unperturbationify x))
		      #f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-closure-ref (remove-tag 'forward tags)
				       (primal v)
				       (unforwardify x))
		   (perturb (tagged-closure-ref (remove-tag 'forward tags)
						(unperturb (tangent v))
						(unforwardify x))))
	(vlad-cons-alias
	 (tagged-closure-ref (remove-tag 'forward tags)
			     (primal v)
			     (unforwardify x))
	 (tagged-closure-ref-alias (remove-tag 'forward tags)
				   (primal v)
				   (primal-alias v a #f)
				   (unforwardify x))
	 (perturb (tagged-closure-ref (remove-tag 'forward tags)
				      (unperturb (tangent v))
				      (unforwardify x)))
	 (perturb-alias
	  (tagged-closure-ref (remove-tag 'forward tags)
			      (unperturb (tangent v))
			      (unforwardify x))
	  (tagged-closure-ref-alias
	   (remove-tag 'forward tags)
	   (unperturb (tangent v))
	   (unperturb-alias (tangent v) (tangent-alias v a #f) #f)
	   (unforwardify x))
	  #f))
	#f))
      ((sensitivity)
       (sensitize-alias
	(tagged-closure-ref (remove-tag 'sensitivity tags)
			    (unsensitize v)
			    (unsensitivityify x))
	(tagged-closure-ref-alias (remove-tag 'sensitivity tags)
				  (unsensitize v)
				  (unsensitize-alias v a #f)
				  (unsensitivityify x))
	#f))
      ((reverse)
       (*j-alias (tagged-closure-ref (remove-tag 'reverse tags)
				     (*j-inverse v)
				     (unreverseify x))
		 (tagged-closure-ref-alias (remove-tag 'reverse tags)
					   (*j-inverse v)
					   (*j-inverse-alias v a #f)
					   (unreverseify x))
		 #f))
      (else (internal-error)))))

(define (new-alias-perturbation-tagged-value v a)
 (assert (compatible-alias? v a))
 (let ((u (new-perturbation-tagged-value v)))
  (cond ((boxed? u)
	 (set-new-aliases! u (cons a (new-aliases u)))
	 (alias-for u))
	(else a))))

(define (get-perturbation-tagged-value-primal-alias u a)
 (assert (compatible-alias? u a))
 (if (boxed? u) (copy-alias (alias u)) a))

(define (new-alias-bundle v a v-perturbation a-perturbation)
 (assert (and (compatible-alias? v a)
	      (compatible-alias? v-perturbation a-perturbation)))
 (let ((u (new-bundle v v-perturbation)))
  (cond ((boxed? u)
	 (set-new-aliases! u (cons (append a a-perturbation) (new-aliases u)))
	 (alias-for u))
	(else (append a a-perturbation)))))

(define (get-bundle-aliases u a)
 (assert (compatible-alias? u a))
 (split-alias (if (boxed? u) (copy-alias (alias u)) a)
	      (list (number-of-slots (get-bundle-primal u))
		    (number-of-slots (get-bundle-tangent u)))))

(define (new-alias-sensitivity-tagged-value v a)
 (assert (compatible-alias? v a))
 (let ((u (new-sensitivity-tagged-value v)))
  (cond ((boxed? u)
	 (set-new-aliases! u (cons a (new-aliases u)))
	 (alias-for u))
	(else a))))

(define (get-sensitivity-tagged-value-primal-alias u a)
 (assert (compatible-alias? u a))
 (if (boxed? u) (copy-alias (alias u)) a))

(define (new-alias-reverse-tagged-value v a)
 (assert (compatible-alias? v a))
 (let ((u (new-reverse-tagged-value v)))
  (cond ((boxed? u)
	 (set-new-aliases! u (cons a (new-aliases u)))
	 (alias-for u))
	(else a))))

(define (get-reverse-tagged-value-primal-alias u a)
 (assert (compatible-alias? u a))
 (if (boxed? u) (copy-alias (alias u)) a))

(define (vlad-cons-alias v1 a1 v2 a2)
 (assert (and (compatible-alias? v1 a1) (compatible-alias? v2 a2)))
 (let ((u (vlad-cons v1 v2)))
  (cond ((boxed? u)
	 (set-new-aliases! u (cons (append a1 a2) (new-aliases u)))
	 (alias-for u))
	(else (append a1 a2)))))

(define (get-vlad-pair-aliases u a)
 (assert (compatible-alias? u a))
 (split-alias (if (boxed? u) (copy-alias (alias u)) a)
	      (list (number-of-slots (vlad-car u))
		    (number-of-slots (vlad-cdr u)))))

(define (vlad-car-alias u a) (first (get-vlad-pair-aliases u a)))

(define (vlad-cdr-alias u a) (second (get-vlad-pair-aliases u a)))

(define (lookup-unionize vs)
 (canonize-and-maybe-intern-abstract-value
  (reduce abstract-value-union-internal vs (empty-abstract-value))))

(define (unionize-alias vs as)
 (assert (and (= (length vs) (length as)) (every compatible-alias? vs as)))
 (if (null? vs)
     (empty-alias)
     (let* ((v (lookup-unionize vs))
	    (a (coalesce-aliases
		(map (lambda (v1 a1) (widen-alias v1 a1 v #f)) vs as))))
      (assert (compatible-alias? v a))
      a)))

(define (get-union-alias-values v a)
 (assert (compatible-alias? v a))
 (if (empty-abstract-value? v)
     '()
     (rest (split-alias (if (boxed? v) (copy-alias (alias v)) a)
			(cons 1 (map number-of-slots (get-union-values v)))))))

(define (union-alias-members v a)
 (assert (or (not (union? v)) (not (some union? (get-union-values v)))))
 (if (union? v) (get-union-alias-values v a) (list a)))

(define (tagged-vlad-cons-alias tags v1 a1 v2 a2)
 (if (empty-tags? tags)
     (vlad-cons-alias v1 a1 v2 a2)
     (case (first tags)
      ((perturbation)
       (perturb-alias (tagged-vlad-cons (remove-tag 'perturbation tags)
					(unperturb v1)
					(unperturb v2))
		      (tagged-vlad-cons-alias (remove-tag 'perturbation tags)
					      (unperturb v1)
					      (unperturb-alias v1 a1 #f)
					      (unperturb v2)
					      (unperturb-alias v2 a2 #f))
		      #f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-vlad-cons (remove-tag 'forward tags)
				     (primal v1)
				     (primal v2))
		   (perturb (tagged-vlad-cons (remove-tag 'forward tags)
					      (unperturb (tangent v1))
					      (unperturb (tangent v2)))))
	(vlad-cons-alias
	 (tagged-vlad-cons (remove-tag 'forward tags)
			   (primal v1)
			   (primal v2))
	 (tagged-vlad-cons-alias (remove-tag 'forward tags)
				 (primal v1)
				 (primal-alias v1 a1 #f)
				 (primal v2)
				 (primal-alias v2 a2 #f))
	 (perturb (tagged-vlad-cons (remove-tag 'forward tags)
				    (unperturb (tangent v1))
				    (unperturb (tangent v2))))
	 (perturb-alias
	  (tagged-vlad-cons (remove-tag 'forward tags)
			    (unperturb (tangent v1))
			    (unperturb (tangent v2)))
	  (tagged-vlad-cons-alias (remove-tag 'forward tags)
				  (unperturb (tangent v1))
				  (unperturb-alias (tangent v1)
						   (tangent-alias v1 a1 #f)
						   #f)
				  (unperturb (tangent v2))
				  (unperturb-alias (tangent v2)
						   (tangent-alias v2 a2 #f)
						   #f))
	  #f))
	#f))
      ((sensitivity)
       (sensitize-alias (tagged-vlad-cons (remove-tag 'sensitivity tags)
					  (unsensitize v1)
					  (unsensitize v2))
			(tagged-vlad-cons-alias (remove-tag 'sensitivity tags)
						(unsensitize v1)
						(unsensitize-alias v1 a1 #f)
						(unsensitize v2)
						(unsensitize-alias v2 a2 #f))
			#f))
      ((reverse)
       (*j-alias (tagged-vlad-cons (remove-tag 'reverse tags)
				   (*j-inverse v1)
				   (*j-inverse v2))
		 (tagged-vlad-cons-alias (remove-tag 'reverse tags)
					 (*j-inverse v1)
					 (*j-inverse-alias v1 a1 #f)
					 (*j-inverse v2)
					 (*j-inverse-alias v2 a2 #f))
		 #f))
      (else (internal-error)))))

(define (tagged-vlad-car-alias tags u a)
 (if (empty-tags? tags)
     (cond ((union? u)
	    ;; widening case M1
	    (unionize-alias
	     (map (lambda (u)
		   (if (vlad-pair? u) (vlad-car u) (empty-abstract-value)))
		  (get-union-values u))
	     (map (lambda (u a)
		   (if (vlad-pair? u) (vlad-car-alias u a) (empty-alias)))
		  (get-union-values u)
		  (get-union-alias-values u a))))
	   ((vlad-pair? u) (vlad-car-alias u a))
	   (else (empty-alias)))
     (case (first tags)
      ((perturbation)
       (perturb-alias
	(tagged-vlad-car (remove-tag 'perturbation tags) (unperturb u))
	(tagged-vlad-car-alias (remove-tag 'perturbation tags)
			       (unperturb u)
			       (unperturb-alias u a #f))
	#f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-vlad-car (remove-tag 'forward tags) (primal u))
		   (perturb (tagged-vlad-car (remove-tag 'forward tags)
					     (unperturb (tangent u)))))
	(vlad-cons-alias
	 (tagged-vlad-car (remove-tag 'forward tags) (primal u))
	 (tagged-vlad-car-alias (remove-tag 'forward tags)
				(primal u)
				(primal-alias u a #f))
	 (perturb (tagged-vlad-car (remove-tag 'forward tags)
				   (unperturb (tangent u))))
	 (perturb-alias
	  (tagged-vlad-car (remove-tag 'forward tags) (unperturb (tangent u)))
	  (tagged-vlad-car-alias
	   (remove-tag 'forward tags)
	   (unperturb (tangent u))
	   (unperturb-alias (tangent u) (tangent-alias u a #f) #f))
	  #f))
	#f))
      ((sensitivity)
       (sensitize-alias
	(tagged-vlad-car (remove-tag 'sensitivity tags) (unsensitize u))
	(tagged-vlad-car-alias (remove-tag 'sensitivity tags)
			       (unsensitize u)
			       (unsensitize-alias u a #f))
	#f))
      ((reverse)
       (*j-alias
	(tagged-vlad-car (remove-tag 'reverse tags) (*j-inverse u))
	(tagged-vlad-car-alias (remove-tag 'reverse tags)
			       (*j-inverse u)
			       (*j-inverse-alias u a #f))
	#f))
      (else (internal-error)))))

(define (tagged-vlad-cdr-alias tags u a)
 (if (empty-tags? tags)
     (cond ((union? u)
	    ;; widening case M2
	    (unionize-alias
	     (map (lambda (u)
		   (if (vlad-pair? u) (vlad-cdr u) (empty-abstract-value)))
		  (get-union-values u))
	     (map (lambda (u a)
		   (if (vlad-pair? u) (vlad-cdr-alias u a) (empty-alias)))
		  (get-union-values u)
		  (get-union-alias-values u a))))
	   ((vlad-pair? u) (vlad-cdr-alias u a))
	   (else (empty-alias)))
     (case (first tags)
      ((perturbation)
       (perturb-alias
	(tagged-vlad-cdr (remove-tag 'perturbation tags) (unperturb u))
	(tagged-vlad-cdr-alias (remove-tag 'perturbation tags)
			       (unperturb u)
			       (unperturb-alias u a #f))
	#f))
      ((forward)
       (bundle-alias1
	(vlad-cons (tagged-vlad-cdr (remove-tag 'forward tags) (primal u))
		   (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
					     (unperturb (tangent u)))))
	(vlad-cons-alias
	 (tagged-vlad-cdr (remove-tag 'forward tags) (primal u))
	 (tagged-vlad-cdr-alias (remove-tag 'forward tags)
				(primal u)
				(primal-alias u a #f))
	 (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
				   (unperturb (tangent u))))
	 (perturb-alias
	  (tagged-vlad-cdr (remove-tag 'forward tags) (unperturb (tangent u)))
	  (tagged-vlad-cdr-alias
	   (remove-tag 'forward tags)
	   (unperturb (tangent u))
	   (unperturb-alias (tangent u) (tangent-alias u a #f) #f))
	  #f))
	#f))
      ((sensitivity)
       (sensitize-alias
	(tagged-vlad-cdr (remove-tag 'sensitivity tags) (unsensitize u))
	(tagged-vlad-cdr-alias (remove-tag 'sensitivity tags)
			       (unsensitize u)
			       (unsensitize-alias u a #f))
	#f))
      ((reverse)
       (*j-alias
	(tagged-vlad-cdr (remove-tag 'reverse tags) (*j-inverse u))
	(tagged-vlad-cdr-alias (remove-tag 'reverse tags)
			       (*j-inverse u)
			       (*j-inverse-alias u a #f))
	#f))
      (else (internal-error)))))

(define (restrict-alias-environment as is)
 ;; This is identical to restrict-environment up to alpha renaming.
 (let ((as (list->vector as))) (map (lambda (i) (vector-ref as i)) is)))

(define (letrec-nested-alias-environment vs as e)
 ;; See the note in letrec-nested-environment.
 (assert (and (= (length vs) (length as)) (every compatible-alias? vs as)))
 (let ((xs (list->vector (letrec-expression-procedure-variables e)))
       (es (list->vector (letrec-expression-lambda-expressions e)))
       (as0 (list->vector as)))
  (map (lambda (p? i)
	(if p?
	    ;; See the note in letrec-nested-environment.
	    ;; foo
	    (new-alias-recursive-closure
	     (restrict-environment vs (letrec-expression-indices e))
	     (restrict-alias-environment as (letrec-expression-indices e))
	     xs
	     es
	     i)
	    (vector-ref as0 i)))
       (letrec-expression-body-free-variable-procedure-variable? e)
       (letrec-expression-body-free-variable-indices e))))

(define (construct-alias-environment-for-let e as a-alist)
 ;; This is identical to construct-environment-for-let up to alpha renaming.
 (let ((as (list->vector as)))
  (map
   (lambda (i x)
    ;; needs work: To make application-let-free-variable-indices such that
    ;;             this can be made more efficient.
    (cond ((assp variable=? x a-alist) => cdr) (else (vector-ref as i))))
   (application-let-free-variable-indices e)
   (free-variables (lambda-expression-body (application-callee e))))))

(define (construct-alias-environment u1 a1 v-alist a-alist)
 ;; See the note in construct-environment.
 (assert (compatible-alias? u1 a1))
 (cond
  ((nonrecursive-closure? u1)
   (let ((as (list->vector (get-closure-alias-values u1 a1))))
    (map
     (lambda (i x)
      ;; needs work: To make nonrecursive-closure-body-free-variable-indices
      ;;             such that this can be made more efficient.
      (cond ((assp variable=? x a-alist) => cdr) (else (vector-ref as i))))
     (nonrecursive-closure-body-free-variable-indices u1)
     (free-variables
      (lambda-expression-body (nonrecursive-closure-lambda-expression u1))))))
  ((recursive-closure? u1)
   (let ((as (list->vector (get-closure-alias-values u1 a1))))
    (map (lambda (i i1 x)
	  ;; needs work:
	  ;; To make recursive-closure-body-free-variable-indices and
	  ;; recursive-closure-body-free-variable-procedure-variable-indices
	  ;; such that this can be made more efficient.
	  (cond ((assp variable=? x a-alist) => cdr)
		;; See the note in construct-environment.
		;; foo
		(i1 (new-alias-recursive-closure
		     (get-recursive-closure-values u1)
		     (get-recursive-closure-alias-values u1 a1)
		     (recursive-closure-procedure-variables u1)
		     (recursive-closure-lambda-expressions u1)
		     i1))
		(else (vector-ref as i))))
	 (recursive-closure-body-free-variable-indices u1)
	 (recursive-closure-body-free-variable-procedure-variable-indices u1)
	 (free-variables (lambda-expression-body
			  (vector-ref (recursive-closure-lambda-expressions u1)
				      (recursive-closure-index u1)))))))
  ((perturbation-tagged-value? u1)
   (map (lambda (v a) (perturb-alias v a #f))
	(construct-environment
	 (unperturb u1)
	 (map (lambda (x-v)
	       (cons (unperturbationify (car x-v)) (unperturb (cdr x-v))))
	      v-alist))
	(construct-alias-environment
	 (unperturb u1)
	 (unperturb-alias u1 a1 #f)
	 (map (lambda (x-v)
	       (cons (unperturbationify (car x-v)) (unperturb (cdr x-v))))
	      v-alist)
	 (map (lambda (x-v x-a)
	       (assert (variable=? (car x-v) (car x-a)))
	       (cons (unperturbationify (car x-v))
		     (unperturb-alias (cdr x-v) (cdr x-a) #f)))
	      v-alist
	      a-alist))))
  ((bundle? u1)
   (map (lambda (v1 a1 v2 a2)
	 (bundle-alias1 (vlad-cons v1 v2) (vlad-cons-alias v1 a1 v2 a2) #f))
	(construct-environment
	 (primal u1)
	 (map (lambda (x-v) (cons (unforwardify (car x-v)) (primal (cdr x-v))))
	      v-alist))
	(construct-alias-environment
	 (primal u1)
	 (primal-alias u1 a1 #f)
	 (map (lambda (x-v)
	       (cons (unforwardify (car x-v))
		     (primal (cdr x-v))))
	      v-alist)
	 (map (lambda (x-v x-a)
	       (assert (variable=? (car x-v) (car x-a)))
	       (cons (unforwardify (car x-v))
		     (primal-alias (cdr x-v) (cdr x-a) #f)))
	      v-alist
	      a-alist))
	(construct-environment
	 (tangent u1)
	 (map (lambda (x-v)
	       (cons (perturbationify (unforwardify (car x-v)))
		     (tangent (cdr x-v))))
	      v-alist))
	(construct-alias-environment
	 (tangent u1)
	 (tangent-alias u1 a1 #f)
	 (map (lambda (x-v)
	       (cons (perturbationify (unforwardify (car x-v)))
		     (tangent (cdr x-v))))
	      v-alist)
	 (map (lambda (x-v x-a)
	       (assert (variable=? (car x-v) (car x-a)))
	       (cons (perturbationify (unforwardify (car x-v)))
		     (tangent-alias (cdr x-v) (cdr x-a) #f)))
	      v-alist
	      a-alist))))
  ((sensitivity-tagged-value? u1)
   (map (lambda (v a) (sensitize-alias v a #f))
	(construct-environment
	 (unsensitize u1)
	 (map (lambda (x-v)
	       (cons (unsensitivityify (car x-v)) (unsensitize (cdr x-v))))
	      v-alist))
	(construct-alias-environment
	 (unsensitize u1)
	 (unsensitize-alias u1 a1 #f)
	 (map (lambda (x-v)
	       (cons (unsensitivityify (car x-v)) (unsensitize (cdr x-v))))
	      v-alist)
	 (map (lambda (x-v x-a)
	       (assert (variable=? (car x-v) (car x-a)))
	       (cons (unsensitivityify (car x-v))
		     (unsensitize-alias (cdr x-v) (cdr x-a) #f)))
	      v-alist
	      a-alist))))
  ((reverse-tagged-value? u1)
   (map (lambda (v a) (*j-alias v a #f))
	(construct-environment
	 (*j-inverse u1)
	 (map (lambda (x-v)
	       (cons (unreverseify (car x-v)) (*j-inverse (cdr x-v))))
	      v-alist))
	(construct-alias-environment
	 (*j-inverse u1)
	 (*j-inverse-alias u1 a1 #f)
	 (map (lambda (x-v)
	       (cons (unreverseify (car x-v)) (*j-inverse (cdr x-v))))
	      v-alist)
	 (map (lambda (x-v x-a)
	       (assert (variable=? (car x-v) (car x-a)))
	       (cons (unreverseify (car x-v))
		     (*j-inverse-alias (cdr x-v) (cdr x-a) #f)))
	      v-alist
	      a-alist))))
  (else (internal-error))))

(define (alias-destructure p v a k1 k2)
 (assert (compatible-alias? v a))
 (letrec ((abstract-outer
	   (lambda (p v v-alist k1)
	    (cond
	     ;; This case comes first to avoid the dispatch.
	     ((variable-access-expression? p)
	      (k1 (cons (cons (variable-access-expression-variable p) v)
			v-alist)))
	     ((union? v)
	      ;; widening case J
	      (map-union (lambda (u) (abstract-outer p u v-alist k1)) v))
	     ((constant-expression? p)
	      ;; needs work: See the note in generate-destructure.
	      ;; widening case A
	      (if (abstract-value-nondisjoint?
		   (concrete-value->abstract-value
		    (constant-expression-value p)) v)
		  (k1 v-alist)
		  (empty-abstract-value)))
	     ((lambda-expression? p)
	      (if (and (nonrecursive-closure? v)
		       (dereferenced-expression-eqv?
			p (nonrecursive-closure-lambda-expression v)))
		  (let abstract-inner ((xs1 (parameter-variables p))
				       (xs2 (nonrecursive-closure-variables v))
				       (vs (get-nonrecursive-closure-values v))
				       (v-alist v-alist)
				       (k1 k1))
		   (if (null? xs1)
		       (k1 v-alist)
		       (abstract-outer
			(allocate-variable-access-expression (first xs1))
			(first vs)
			v-alist
			(lambda (v-alist)
			 (abstract-inner
			  (rest xs1) (rest xs2) (rest vs) v-alist k1)))))
		  (empty-abstract-value)))
	     ((letrec-expression? p)
	      (assert
	       (and (variable-access-expression? (letrec-expression-body p))
		    (memp variable=?
			  (variable-access-expression-variable
			   (letrec-expression-body p))
			  (letrec-expression-procedure-variables p))))
	      (if (and (recursive-closure? v)
		       (= (recursive-closure-index v)
			  (positionp
			   variable=?
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
		  (let abstract-inner ((xs1 (parameter-variables p))
				       (xs2 (recursive-closure-variables v))
				       (vs (get-recursive-closure-values v))
				       (v-alist v-alist)
				       (k1 k1))
		   (if (null? xs1)
		       (k1 v-alist)
		       (abstract-outer
			(allocate-variable-access-expression (first xs1))
			(first vs)
			v-alist
			(lambda (v-alist)
			 (abstract-inner
			  (rest xs1) (rest xs2) (rest vs) v-alist k1)))))
		  (empty-abstract-value)))
	     ((cons-expression? p)
	      (abstract-outer
	       (cons-expression-car p)
	       (tagged-vlad-car (cons-expression-tags p) v)
	       v-alist
	       (lambda (v-alist)
		(abstract-outer (cons-expression-cdr p)
				(tagged-vlad-cdr (cons-expression-tags p) v)
				v-alist
				k1))))
	     (else (internal-error)))))
	  (alias-outer
	   (lambda (p v a v-alist a-alist k1 k2)
	    (assert (and (compatible-alias? v a)
			 ;; The next two cheat.
			 (= (length v-alist) (length a-alist))
			 (every (lambda (x-v x-a)
				 (compatible-alias? (cdr x-v) (cdr x-a)))
				v-alist
				a-alist)))
	    (cond
	     ;; This case comes first to avoid the dispatch.
	     ((variable-access-expression? p)
	      (k2 (cons (cons (variable-access-expression-variable p) v)
			v-alist)
		  (cons (cons (variable-access-expression-variable p) a)
			a-alist)))
	     ((union? v)
	      ;; widening case J
	      (unionize-alias
	       (map (lambda (u) (abstract-outer p u v-alist k1))
		    (get-union-values v))
	       (map (lambda (u a) (alias-outer p u a v-alist a-alist k1 k2))
		    (get-union-values v)
		    (get-union-alias-values v a))))
	     ((constant-expression? p)
	      ;; needs work: See the note in generate-destructure.
	      ;; widening case A
	      (if (abstract-value-nondisjoint?
		   (concrete-value->abstract-value
		    (constant-expression-value p)) v)
		  (k2 v-alist a-alist)
		  (empty-alias)))
	     ((lambda-expression? p)
	      (if (and (nonrecursive-closure? v)
		       (dereferenced-expression-eqv?
			p (nonrecursive-closure-lambda-expression v)))
		  (letrec ((abstract-inner
			    (lambda (xs1 xs2 vs v-alist k1)
			     (if (null? xs1)
				 (k1 v-alist)
				 (abstract-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))))))
			   (alias-inner
			    (lambda (xs1 xs2 vs as v-alist a-alist k1 k2)
			     (if (null? xs1)
				 (k2 v-alist a-alist)
				 (alias-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  (first as)
				  v-alist
				  a-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))
				  (lambda (v-alist a-alist)
				   (alias-inner (rest xs1)
						(rest xs2)
						(rest vs)
						(rest as)
						v-alist
						a-alist
						k1
						k2)))))))
		   (alias-inner (parameter-variables p)
				(nonrecursive-closure-variables v)
				(get-nonrecursive-closure-values v)
				(get-nonrecursive-closure-alias-values v a)
				v-alist
				a-alist
				k1
				k2))
		  (empty-alias)))
	     ((letrec-expression? p)
	      (assert
	       (and (variable-access-expression? (letrec-expression-body p))
		    (memp variable=?
			  (variable-access-expression-variable
			   (letrec-expression-body p))
			  (letrec-expression-procedure-variables p))))
	      (if (and (recursive-closure? v)
		       (= (recursive-closure-index v)
			  (positionp
			   variable=?
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
		  (letrec ((abstract-inner
			    (lambda (xs1 xs2 vs v-alist k1)
			     (if (null? xs1)
				 (k1 v-alist)
				 (abstract-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))))))
			   (alias-inner
			    (lambda (xs1 xs2 vs as v-alist a-alist k1 k2)
			     (if (null? xs1)
				 (k2 v-alist a-alist)
				 (alias-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  (first as)
				  v-alist
				  a-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))
				  (lambda (v-alist a-alist)
				   (alias-inner (rest xs1)
						(rest xs2)
						(rest vs)
						(rest as)
						v-alist
						a-alist
						k1
						k2)))))))
		   (alias-inner (parameter-variables p)
				(recursive-closure-variables v)
				(get-recursive-closure-values v)
				(get-recursive-closure-alias-values v a)
				v-alist
				a-alist
				k1
				k2))
		  (empty-alias)))
	     ((cons-expression? p)
	      (alias-outer
	       (cons-expression-car p)
	       (tagged-vlad-car (cons-expression-tags p) v)
	       (tagged-vlad-car-alias (cons-expression-tags p) v a)
	       v-alist
	       a-alist
	       (lambda (v-alist)
		(abstract-outer (cons-expression-cdr p)
				(tagged-vlad-cdr (cons-expression-tags p) v)
				v-alist
				k1))
	       (lambda (v-alist a-alist)
		(alias-outer
		 (cons-expression-cdr p)
		 (tagged-vlad-cdr (cons-expression-tags p) v)
		 (tagged-vlad-cdr-alias (cons-expression-tags p) v a)
		 v-alist
		 a-alist
		 k1
		 k2))))
	     (else (internal-error))))))
  (alias-outer p v a '() '() k1 k2)))

(define (alias-apply v1 a1 v2 a2 top?)
 (assert (and (compatible-alias? v1 a1) (compatible-alias? v2 a2)))
 (let ((a (cond
	   ((empty-abstract-value? v2) (empty-alias))
	   ((union? v1)
	    ;; widening case I
	    (unionize-alias
	     (map (lambda (u1) (abstract-apply u1 v2)) (get-union-values v1))
	     (map (lambda (u1 a1) (alias-apply u1 a1 v2 a2 #f))
		  (get-union-values v1)
		  (get-union-alias-values v1 a1))))
	   ((primitive-procedure? v1) ((primitive-procedure-alias v1) v2 a2))
	   ((closure? v1)
	    (cond
	     ;; Function instances are not created for functions that return
	     ;; void values.
	     ((and (not top?) (void? (abstract-apply v1 v2)))
	      (alias-for (abstract-apply v1 v2)))
	     ((and (not top?)
		   ;; Function instances are not created for functions that
		   ;; return void values.
		   (not (void? (abstract-apply v1 v2)))
		   (not (inline? (lookup-function-instance v1 v2))))
	      (let ((instance (lookup-function-instance v1 v2)))
	       (set-new-input-aliases!
		instance (cons (append a1 a2) (new-input-aliases instance)))
	       (copy-alias (output-alias instance))))
	     ((some-value-tags
	       (lambda (tags2) (prefix-tags? (value-tags v1) tags2)) v2)
	      ;; widening case J
	      (alias-destructure
	       (closure-parameter v1)
	       v2
	       a2
	       (lambda (v-alist)
		;; bar
		(abstract-eval1 (closure-body v1)
				(construct-environment v1 v-alist)))
	       (lambda (v-alist a-alist)
		;; bar
		(alias-eval
		 (closure-body v1)
		 (construct-environment v1 v-alist)
		 (construct-alias-environment v1 a1 v-alist a-alist)))))
	     (else (empty-alias))))
	   (else (empty-alias)))))
  (assert (compatible-alias? (abstract-apply v1 v2) a))
  a))

(define (alias-eval e vs as)
 (assert (and (= (length vs) (length as))
	      (every compatible-alias? vs as)
	      (one (lambda (b)
		    (abstract-environment=? vs (environment-binding-values b)))
		   (environment-bindings e))))
 (let* ((v0 (abstract-eval1 e vs))
	(a0
	 (cond
	  ((constant-expression? e)
	   ;; widening case E
	   (widen-alias (constant-expression-value e) (empty-alias) v0 #f))
	  ;; There is no widening case F.
	  ((variable-access-expression? e) (first as))
	  ((lambda-expression? e)
	   ;; widening case G
	   ;; foo
	   (widen-alias (new-nonrecursive-closure vs e)
			(new-alias-nonrecursive-closure vs as e)
			v0
			#f))
	  ((application? e)
	   (if (lambda-expression? (application-callee e))
	       ;; This handling of LET is an optimization. See the note in
	       ;; concrete-eval.
	       (let* ((e1 (lambda-expression-body (application-callee e)))
		      (p (lambda-expression-parameter (application-callee e)))
		      (tags1 (lambda-expression-tags (application-callee e)))
		      (v (abstract-eval1
			  (application-argument e)
			  (restrict-environment
			   vs (application-argument-indices e)))))
		(if (some-value-tags
		     (lambda (tags) (prefix-tags? tags1 tags)) v)
		    ;; widening case B-prime
		    (widen-alias
		     (abstract-destructure
		      ;; widening case J
		      map-union
		      (empty-abstract-value)
		      p
		      v
		      (lambda (v-alist)
		       ;; bar
		       (abstract-eval1
			e1 (construct-environment-for-let e vs v-alist))))
		     ;; widening case J
		     (alias-destructure
		      p
		      v
		      (alias-eval
		       (application-argument e)
		       (restrict-environment
			vs (application-argument-indices e))
		       (restrict-alias-environment
			as (application-argument-indices e)))
		      (lambda (v-alist)
		       ;; bar
		       (abstract-eval1
			e1 (construct-environment-for-let e vs v-alist)))
		      (lambda (v-alist a-alist)
		       ;; bar
		       (alias-eval
			e1
			(construct-environment-for-let e vs v-alist)
			(construct-alias-environment-for-let e as a-alist))))
		     v0
		     #f)
		    ;; widening case B-prime
		    (widen-alias (empty-abstract-value) (empty-alias) v0 #f)))
	       (let ((v1 (abstract-eval1
			  (application-callee e)
			  (restrict-environment
			   vs (application-callee-indices e))))
		     (v2 (abstract-eval1
			  (application-argument e)
			  (restrict-environment
			   vs (application-argument-indices e)))))
		;; widening case B
		(widen-alias
		 (abstract-apply v1 v2)
		 (alias-apply
		  v1
		  (alias-eval
		   (application-callee e)
		   (restrict-environment vs (application-callee-indices e))
		   (restrict-alias-environment
		    as (application-callee-indices e)))
		  v2
		  (alias-eval
		   (application-argument e)
		   (restrict-environment vs (application-argument-indices e))
		   (restrict-alias-environment
		    as (application-argument-indices e)))
		  #f)
		 v0
		 #f))))
	  ((letrec-expression? e)
	   ;; widening case C
	   ;; bar
	   (widen-alias (abstract-eval1 (letrec-expression-body e)
					(letrec-nested-environment vs e))
			;; bar
			(alias-eval (letrec-expression-body e)
				    (letrec-nested-environment vs e)
				    (letrec-nested-alias-environment vs as e))
			v0
			#f))
	  ((cons-expression? e)
	   (let ((v1 (abstract-eval1 (cons-expression-car e)
				     (restrict-environment
				      vs (cons-expression-car-indices e))))
		 (v2 (abstract-eval1 (cons-expression-cdr e)
				     (restrict-environment
				      vs (cons-expression-cdr-indices e)))))
	    ;; widening case D
	    (widen-alias
	     (tagged-vlad-cons (cons-expression-tags e) v1 v2)
	     (tagged-vlad-cons-alias
	      (cons-expression-tags e)
	      v1
	      (alias-eval
	       (cons-expression-car e)
	       (restrict-environment vs (cons-expression-car-indices e))
	       (restrict-alias-environment as (cons-expression-car-indices e)))
	      v2
	      (alias-eval
	       (cons-expression-cdr e)
	       (restrict-environment vs (cons-expression-cdr-indices e))
	       (restrict-alias-environment
		as (cons-expression-cdr-indices e))))
	     v0
	     #f)))
	  (else (internal-error)))))
  (assert (compatible-alias? v0 a0))
  a0))

(define (zero-alias v a top?)
 (let ((instance (find-instance 'zero v)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v)
    ;; widening case H1
    (unionize-alias (map zero (get-union-values v))
		    (map (lambda (u a) (zero-alias u a #f))
			 (get-union-values v)
			 (get-union-alias-values v a))))
   ((vlad-empty-list? v) (alias-for v))
   ((vlad-true? v) (alias-for v))
   ((vlad-false? v) (alias-for v))
   ;; debugging
   ((vlad-real? v) (if #t (alias-for 0) (alias-for (abstract-real))))
   ((primitive-procedure? v) (alias-for v))
   ((nonrecursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-nonrecursive-closure
     (map zero (get-nonrecursive-closure-values v))
     (map (lambda (v a) (zero-alias v a #f))
	  (get-nonrecursive-closure-values v)
	  (get-nonrecursive-closure-alias-values v a))
     (nonrecursive-closure-lambda-expression v)))
   ((recursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-recursive-closure (map zero (get-recursive-closure-values v))
				 (map (lambda (v a) (zero-alias v a #f))
				      (get-recursive-closure-values v)
				      (get-recursive-closure-alias-values v a))
				 (recursive-closure-procedure-variables v)
				 (recursive-closure-lambda-expressions v)
				 (recursive-closure-index v)))
   ((perturbation-tagged-value? v)
    (new-alias-perturbation-tagged-value
     (zero (get-perturbation-tagged-value-primal v))
     (zero-alias (get-perturbation-tagged-value-primal v)
		 (get-perturbation-tagged-value-primal-alias v a)
		 #f)))
   ((bundle? v)
    (let ((as (get-bundle-aliases v a)))
     (new-alias-bundle (zero (get-bundle-primal v))
		       (zero-alias (get-bundle-primal v) (first as) #f)
		       (zero (get-bundle-tangent v))
		       (zero-alias (get-bundle-tangent v) (second as) #f))))
   ((sensitivity-tagged-value? v)
    (new-alias-sensitivity-tagged-value
     (zero (get-sensitivity-tagged-value-primal v))
     (zero-alias (get-sensitivity-tagged-value-primal v)
		 (get-sensitivity-tagged-value-primal-alias v a)
		 #f)))
   ((reverse-tagged-value? v)
    (new-alias-reverse-tagged-value
     (zero (get-reverse-tagged-value-primal v))
     (zero-alias (get-reverse-tagged-value-primal v)
		 (get-reverse-tagged-value-primal-alias v a)
		 #f)))
   ((vlad-pair? v)
    (vlad-cons-alias (zero (vlad-car v))
		     (zero-alias (vlad-car v) (vlad-car-alias v a) #f)
		     (zero (vlad-cdr v))
		     (zero-alias (vlad-cdr v) (vlad-cdr-alias v a) #f)))
   (else (internal-error)))))

(define (perturb-alias v a top?)
 (let ((instance (find-instance 'perturb v)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v)
    ;; widening case H2
    (unionize-alias (map perturb (get-union-values v))
		    (map (lambda (u a) (perturb-alias u a #f))
			 (get-union-values v)
			 (get-union-alias-values v a))))
   ((or (vlad-empty-list? v)
	(vlad-true? v)
	(vlad-false? v)
	(vlad-real? v)
	(primitive-procedure? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (new-alias-perturbation-tagged-value v a))
   ((nonrecursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-nonrecursive-closure
     (map perturb (get-nonrecursive-closure-values v))
     (map (lambda (v a) (perturb-alias v a #f))
	  (get-nonrecursive-closure-values v)
	  (get-nonrecursive-closure-alias-values v a))
     (perturbation-transform (nonrecursive-closure-lambda-expression v))))
   ((recursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-recursive-closure
     (map perturb (get-recursive-closure-values v))
     (map (lambda (v a) (perturb-alias v a #f))
	  (get-recursive-closure-values v)
	  (get-recursive-closure-alias-values v a))
     (map-vector perturbationify (recursive-closure-procedure-variables v))
     (map-vector perturbation-transform
		 (recursive-closure-lambda-expressions v))
     (recursive-closure-index v)))
   (else (internal-error)))))

(define (unperturb-alias v-perturbation a-perturbation top?)
 (let ((instance (find-instance 'unperturb v-perturbation)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases!
     instance (cons a-perturbation (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v-perturbation)
    ;; widening case H3
    (unionize-alias
     (map unperturb (get-union-values v-perturbation))
     (map (lambda (u-perturbation a-perturbation)
	   (unperturb-alias u-perturbation a-perturbation #f))
	  (get-union-values v-perturbation)
	  (get-union-alias-values v-perturbation a-perturbation))))
   ((or (vlad-empty-list? v-perturbation)
	(vlad-true? v-perturbation)
	(vlad-false? v-perturbation)
	(vlad-real? v-perturbation)
	(primitive-procedure? v-perturbation)
	(bundle? v-perturbation)
	(sensitivity-tagged-value? v-perturbation)
	(reverse-tagged-value? v-perturbation)
	(vlad-pair? v-perturbation))
    (empty-alias))
   ((nonrecursive-closure? v-perturbation)
    (if (tagged? 'perturbation (nonrecursive-closure-tags v-perturbation))
	;; See the note in abstract-environment=?.
	(new-alias-nonrecursive-closure
	 (map unperturb (get-nonrecursive-closure-values v-perturbation))
	 (map (lambda (v-perturbation a-perturbation)
	       (unperturb-alias v-perturbation a-perturbation #f))
	      (get-nonrecursive-closure-values v-perturbation)
	      (get-nonrecursive-closure-alias-values
	       v-perturbation a-perturbation))
	 (perturbation-transform-inverse
	  (nonrecursive-closure-lambda-expression v-perturbation)))
	(empty-alias)))
   ((recursive-closure? v-perturbation)
    (if (tagged? 'perturbation (recursive-closure-tags v-perturbation))
	;; See the note in abstract-environment=?.
	(new-alias-recursive-closure
	 (map unperturb (get-recursive-closure-values v-perturbation))
	 (map (lambda (v-perturbation a-perturbation)
	       (unperturb-alias v-perturbation a-perturbation #f))
	      (get-recursive-closure-values v-perturbation)
	      (get-recursive-closure-alias-values
	       v-perturbation a-perturbation))
	 (map-vector unperturbationify
		     (recursive-closure-procedure-variables v-perturbation))
	 (map-vector perturbation-transform-inverse
		     (recursive-closure-lambda-expressions v-perturbation))
	 (recursive-closure-index v-perturbation))
	(empty-alias)))
   ((perturbation-tagged-value? v-perturbation)
    (get-perturbation-tagged-value-primal-alias v-perturbation a-perturbation))
   (else (internal-error)))))

(define (primal-alias v-forward a-forward top?)
 (let ((instance (find-instance 'primal v-forward)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases!
     instance (cons a-forward (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v-forward)
    ;; widening case H4
    (unionize-alias
     (map primal (get-union-values v-forward))
     (map (lambda (u-forward a-forward) (primal-alias u-forward a-forward #f))
	  (get-union-values v-forward)
	  (get-union-alias-values v-forward a-forward))))
   ((or (vlad-empty-list? v-forward)
	(vlad-true? v-forward)
	(vlad-false? v-forward)
	(vlad-real? v-forward)
	(primitive-procedure? v-forward)
	(perturbation-tagged-value? v-forward)
	(sensitivity-tagged-value? v-forward)
	(reverse-tagged-value? v-forward)
	(vlad-pair? v-forward))
    (empty-alias))
   ((nonrecursive-closure? v-forward)
    (let ((b (find-if (lambda (b)
		       (deep-abstract-value=?
			v-forward
			(primitive-procedure-forward (value-binding-value b))))
		      *value-bindings*)))
     (cond (b (alias-for (value-binding-value b)))
	   ((tagged? 'forward (nonrecursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (new-alias-nonrecursive-closure
	     (map primal (get-nonrecursive-closure-values v-forward))
	     (map (lambda (v-forward a-forward)
		   (primal-alias v-forward a-forward #f))
		  (get-nonrecursive-closure-values v-forward)
		  (get-nonrecursive-closure-alias-values v-forward a-forward))
	     (forward-transform-inverse
	      (nonrecursive-closure-lambda-expression v-forward))))
	   (else (empty-alias)))))
   ((recursive-closure? v-forward)
    (if (tagged? 'forward (recursive-closure-tags v-forward))
	;; See the note in abstract-environment=?.
	(new-alias-recursive-closure
	 (map primal (get-recursive-closure-values v-forward))
	 (map (lambda (v-forward a-forward)
	       (primal-alias v-forward a-forward #f))
	      (get-recursive-closure-values v-forward)
	      (get-recursive-closure-alias-values v-forward a-forward))
	 (map-vector unforwardify
		     (recursive-closure-procedure-variables v-forward))
	 (map-vector forward-transform-inverse
		     (recursive-closure-lambda-expressions v-forward))
	 (recursive-closure-index v-forward))
	(empty-alias)))
   ((bundle? v-forward) (first (get-bundle-aliases v-forward a-forward)))
   (else (internal-error)))))

(define (tangent-alias v-forward a-forward top?)
 (let ((instance (find-instance 'tangent v-forward)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases!
     instance (cons a-forward (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v-forward)
    ;; widening case H5
    (unionize-alias (map tangent (get-union-values v-forward))
		    (map (lambda (u-forward a-forward)
			  (tangent-alias u-forward a-forward #f))
			 (get-union-values v-forward)
			 (get-union-alias-values v-forward a-forward))))
   ((or (vlad-empty-list? v-forward)
	(vlad-true? v-forward)
	(vlad-false? v-forward)
	(vlad-real? v-forward)
	(primitive-procedure? v-forward)
	(perturbation-tagged-value? v-forward)
	(sensitivity-tagged-value? v-forward)
	(reverse-tagged-value? v-forward)
	(vlad-pair? v-forward))
    (empty-alias))
   ((nonrecursive-closure? v-forward)
    (let ((b (find-if (lambda (b)
		       (deep-abstract-value=?
			v-forward
			(primitive-procedure-forward (value-binding-value b))))
		      *value-bindings*)))
     (cond (b (alias-for (perturb (value-binding-value b))))
	   ((tagged? 'forward (nonrecursive-closure-tags v-forward))
	    ;; See the note in abstract-environment=?.
	    (new-alias-nonrecursive-closure
	     (map tangent (get-nonrecursive-closure-values v-forward))
	     (map (lambda (v-forward a-forward)
		   (tangent-alias v-forward a-forward #f))
		  (get-nonrecursive-closure-values v-forward)
		  (get-nonrecursive-closure-alias-values v-forward a-forward))
	     (perturbation-transform
	      (forward-transform-inverse
	       (nonrecursive-closure-lambda-expression v-forward)))))
	   (else (empty-alias)))))
   ((recursive-closure? v-forward)
    (if (tagged? 'forward (recursive-closure-tags v-forward))
	;; See the note in abstract-environment=?.
	(new-alias-recursive-closure
	 (map tangent (get-recursive-closure-values v-forward))
	 (map (lambda (v-forward a-forward)
	       (tangent-alias v-forward a-forward #f))
	      (get-recursive-closure-values v-forward)
	      (get-recursive-closure-alias-values v-forward a-forward))
	 (map-vector (lambda (x) (perturbationify (unforwardify x)))
		     (recursive-closure-procedure-variables v-forward))
	 (map-vector (lambda (e)
		      (perturbation-transform (forward-transform-inverse e)))
		     (recursive-closure-lambda-expressions v-forward))
	 (recursive-closure-index v-forward))
	(empty-alias)))
   ((bundle? v-forward) (second (get-bundle-aliases v-forward a-forward)))
   (else (internal-error)))))

(define (bundle-alias1 v0 a0 top?)
 ;; needs work: There is a naming clash with the alias slot of bundle.
 ;; needs work: v0 naming convention
 (let ((instance (find-instance 'bundle v0)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a0 (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v0)
    ;; widening case H6
    (unionize-alias (map bundle (get-union-values v0))
		    (map (lambda (v0 a0) (bundle-alias1 v0 a0 #f))
			 (get-union-values v0)
			 (get-union-alias-values v0 a0)
			 #f)))
   ((vlad-pair? v0)
    (let ((v (vlad-car v0))
	  (v-perturbation (vlad-cdr v0))
	  (a (vlad-car-alias v0 a0))
	  (a-perturbation (vlad-cdr-alias v0 a0)))
     (cond
      ((union? v)
       ;; widening case H7
       (unionize-alias
	(map (lambda (u) (bundle (vlad-cons u v-perturbation)))
	     (get-union-values v))
	(map (lambda (u a)
	      (bundle-alias1
	       (vlad-cons u v-perturbation)
	       (vlad-cons-alias u a v-perturbation a-perturbation)
	       #f))
	     (get-union-values v)
	     (get-union-alias-values v a))))
      ((union? v-perturbation)
       ;; widening case H8
       (unionize-alias
	(map (lambda (u-perturbation) (bundle (vlad-cons v u-perturbation)))
	     (get-union-values v-perturbation))
	(map (lambda (u-perturbation a-perturbation)
	      (bundle-alias1
	       (vlad-cons v u-perturbation)
	       (vlad-cons-alias v a u-perturbation a-perturbation)
	       #f))
	     (get-union-values v-perturbation)
	     (get-union-alias-values v-perturbation a-perturbation))))
      ((and (or (vlad-empty-list? v)
		(vlad-true? v)
		(vlad-false? v)
		(vlad-real? v)
		(perturbation-tagged-value? v)
		(bundle? v)
		(sensitivity-tagged-value? v)
		(reverse-tagged-value? v)
		(vlad-pair? v))
	    (some-bundlable? v v-perturbation))
       (new-alias-bundle v a v-perturbation a-perturbation))
      ((and (primitive-procedure? v) (some-bundlable? v v-perturbation))
       (alias-for (primitive-procedure-forward v)))
      ((and (nonrecursive-closure? v)
	    (nonrecursive-closure? v-perturbation)
	    (perturbation-parameter?
	     (nonrecursive-closure-parameter v-perturbation))
	    (nonrecursive-closure-match? v (unperturb v-perturbation)))
       ;; See the note in abstract-environment=?.
       (new-alias-nonrecursive-closure
	(map (lambda (v v-perturbation) (bundle (vlad-cons v v-perturbation)))
	     (get-nonrecursive-closure-values v)
	     (get-nonrecursive-closure-values v-perturbation))
	(map (lambda (v a v-perturbation a-perturbation)
	      (bundle-alias1
	       (vlad-cons v v-perturbation)
	       (vlad-cons-alias v a v-perturbation a-perturbation)
	       #f))
	     (get-nonrecursive-closure-values v)
	     (get-nonrecursive-closure-alias-values v a)
	     (get-nonrecursive-closure-values v-perturbation)
	     (get-nonrecursive-closure-alias-values
	      v-perturbation a-perturbation))
	(forward-transform (nonrecursive-closure-lambda-expression v))))
      ((and (recursive-closure? v)
	    (recursive-closure? v-perturbation)
	    (perturbation-parameter?
	     (recursive-closure-parameter v-perturbation))
	    (recursive-closure-match? v (unperturb v-perturbation)))
       ;; See the note in abstract-environment=?.
       (new-alias-recursive-closure
	(map (lambda (v v-perturbation) (bundle (vlad-cons v v-perturbation)))
	     (get-recursive-closure-values v)
	     (get-recursive-closure-values v-perturbation))
	(map
	 (lambda (v a v-perturbation a-perturbation)
	  (bundle-alias1
	   (vlad-cons v v-perturbation)
	   (vlad-cons-alias v a v-perturbation a-perturbation)
	   #f))
	 (get-recursive-closure-values v)
	 (get-recursive-closure-alias-values v a)
	 (get-recursive-closure-values v-perturbation)
	 (get-recursive-closure-alias-values v-perturbation a-perturbation))
	(map-vector forwardify (recursive-closure-procedure-variables v))
	(map-vector forward-transform (recursive-closure-lambda-expressions v))
	(recursive-closure-index v)))
      (else (empty-alias)))))
   (else (empty-alias)))))

(define (sensitize-alias v a top?)
 (let ((instance (find-instance 'sensitize v)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v)
    ;; widening case H10
    (unionize-alias (map sensitize (get-union-values v))
		    (map (lambda (u a) (sensitize-alias u a #f))
			 (get-union-values v)
			 (get-union-alias-values v a))))
   ((or (vlad-empty-list? v)
	(vlad-true? v)
	(vlad-false? v)
	(vlad-real? v)
	(primitive-procedure? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (new-alias-sensitivity-tagged-value v a))
   ((nonrecursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-nonrecursive-closure
     (map sensitize (get-nonrecursive-closure-values v))
     (map (lambda (v a) (sensitize-alias v a #f))
	  (get-nonrecursive-closure-values v)
	  (get-nonrecursive-closure-alias-values v a))
     (sensitivity-transform (nonrecursive-closure-lambda-expression v))))
   ((recursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-recursive-closure
     (map sensitize (get-recursive-closure-values v))
     (map (lambda (v a) (sensitize-alias v a #f))
	  (get-recursive-closure-values v)
	  (get-recursive-closure-alias-values v a))
     (map-vector sensitivityify (recursive-closure-procedure-variables v))
     (map-vector sensitivity-transform
		 (recursive-closure-lambda-expressions v))
     (recursive-closure-index v)))
   (else (internal-error)))))

(define (unsensitize-alias v-sensitivity a-sensitivity top?)
 (let ((instance (find-instance 'unsensitize v-sensitivity)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases!
     instance (cons a-sensitivity (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v-sensitivity)
    ;; widening case H11
    (unionize-alias
     (map unsensitize (get-union-values v-sensitivity))
     (map (lambda (u-sensitivity a-sensitivity)
	   (unsensitize-alias u-sensitivity a-sensitivity #f))
	  (get-union-values v-sensitivity)
	  (get-union-alias-values v-sensitivity a-sensitivity))))
   ((or (vlad-empty-list? v-sensitivity)
	(vlad-true? v-sensitivity)
	(vlad-false? v-sensitivity)
	(vlad-real? v-sensitivity)
	(primitive-procedure? v-sensitivity)
	(perturbation-tagged-value? v-sensitivity)
	(bundle? v-sensitivity)
	(reverse-tagged-value? v-sensitivity)
	(vlad-pair? v-sensitivity))
    (empty-alias))
   ((nonrecursive-closure? v-sensitivity)
    (if (and (tagged? 'sensitivity (nonrecursive-closure-tags v-sensitivity))
	     (sensitivity-transform-inverse?
	      (nonrecursive-closure-lambda-expression v-sensitivity)))
	;; See the note in abstract-environment=?.
	(new-alias-nonrecursive-closure
	 (map unsensitize (get-nonrecursive-closure-values v-sensitivity))
	 (map (lambda (v-sensitivity a-sensitivity)
	       (unsensitize-alias v-sensitivity a-sensitivity #f))
	      (get-nonrecursive-closure-values v-sensitivity)
	      (get-nonrecursive-closure-alias-values
	       v-sensitivity a-sensitivity))
	 (sensitivity-transform-inverse
	  (nonrecursive-closure-lambda-expression v-sensitivity)))
	(empty-alias)))
   ((recursive-closure? v-sensitivity)
    (if (and
	 (tagged? 'sensitivity (recursive-closure-tags v-sensitivity))
	 (every-vector unsensitivityify?
		       (recursive-closure-procedure-variables v-sensitivity))
	 (every-vector sensitivity-transform-inverse?
		       (recursive-closure-lambda-expressions v-sensitivity)))
	;; See the note in abstract-environment=?.
	(new-alias-recursive-closure
	 (map unsensitize (get-recursive-closure-values v-sensitivity))
	 (map
	  (lambda (v-sensitivity a-sensitivity)
	   (unsensitize-alias v-sensitivity a-sensitivity #f))
	  (get-recursive-closure-values v-sensitivity)
	  (get-recursive-closure-alias-values v-sensitivity a-sensitivity))
	 (map-vector
	  unsensitivityify
	  (recursive-closure-procedure-variables v-sensitivity))
	 (map-vector
	  sensitivity-transform-inverse
	  (recursive-closure-lambda-expressions v-sensitivity))
	 (recursive-closure-index v-sensitivity))
	(empty-alias)))
   ((sensitivity-tagged-value? v-sensitivity)
    (get-sensitivity-tagged-value-primal-alias v-sensitivity a-sensitivity))
   (else (internal-error)))))

(define (plus-alias v0 a0 top?)
 ;; needs work: v0 naming convention
 (let ((instance (find-instance 'plus v0)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a0 (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v0)
    ;; widening case H12
    (unionize-alias (map plus (get-union-values v0))
		    (map (lambda (u0 a0) (plus-alias u0 a0 #f))
			 (get-union-values v0)
			 (get-union-alias-values v0 a0))))
   ((vlad-pair? v0)
    (let ((v1 (vlad-car v0))
	  (v2 (vlad-cdr v0))
	  (a1 (vlad-car-alias v0 a0))
	  (a2 (vlad-cdr-alias v0 a0)))
     (cond
      ;; needs work: The following two don't check conformance.
      ((is-zero? v1) a2)
      ((is-zero? v2) a1)
      ((union? v1)
       ;; widening case H13
       (unionize-alias
	(map (lambda (u1) (plus (vlad-cons u1 v2))) (get-union-values v1))
	(map (lambda (u1 a1)
	      (plus-alias (vlad-cons u1 v2) (vlad-cons-alias u1 a1 v2 a2) #f))
	     (get-union-values v1)
	     (get-union-alias-values v1 a1))))
      ((union? v2)
       ;; widening case H14
       ;; There is no widening case H15
       (unionize-alias
	(map (lambda (u2) (plus (vlad-cons v1 u2))) (get-union-values v2))
	(map (lambda (u2 a2)
	      (plus-alias (vlad-cons v1 u2) (vlad-cons-alias v1 a1 u2 a2) #f))
	     (get-union-values v2)
	     (get-union-alias-values v2 a2))))
      ((and (vlad-empty-list? v1) (vlad-empty-list? v2)) a1)
      ((and (vlad-true? v1) (vlad-true? v2)) a1)
      ((and (vlad-false? v1) (vlad-false? v2)) a1)
      ((and (abstract-real? v1) (vlad-real? v2)) a1)
      ((and (vlad-real? v1) (abstract-real? v2)) a2)
      ((and (real? v1) (real? v2)) (alias-for (+ v1 v2)))
      ((and (primitive-procedure? v1) (primitive-procedure? v2) (eq? v1 v2))
       a1)
      ((and (nonrecursive-closure? v1)
	    (nonrecursive-closure? v2)
	    (nonrecursive-closure-match? v1 v2))
       ;; See the note in abstract-environment=?.
       (new-alias-nonrecursive-closure
	(map (lambda (v1 v2) (plus (vlad-cons v1 v2)))
	     (get-nonrecursive-closure-values v1)
	     (get-nonrecursive-closure-values v2))
	(map (lambda (v1 a1 v2 a2)
	      (plus-alias (vlad-cons v1 v2) (vlad-cons-alias v1 a1 v2 a2) #f))
	     (get-nonrecursive-closure-values v1)
	     (get-nonrecursive-closure-alias-values v1 a1)
	     (get-nonrecursive-closure-values v2)
	     (get-nonrecursive-closure-alias-values v2 a2))
	(nonrecursive-closure-lambda-expression v1)))
      ((and (recursive-closure? v1)
	    (recursive-closure? v2)
	    (recursive-closure-match? v1 v2))
       ;; See the note in abstract-environment=?.
       (new-alias-recursive-closure
	(map (lambda (v1 v2) (plus (vlad-cons v1 v2)))
	     (get-recursive-closure-values v1)
	     (get-recursive-closure-values v2))
	(map (lambda (v1 a1 v2 a2)
	      (plus-alias (vlad-cons v1 v2) (vlad-cons-alias v1 a1 v2 a2) #f))
	     (get-recursive-closure-values v1)
	     (get-recursive-closure-alias-values v1 a1)
	     (get-recursive-closure-values v2)
	     (get-recursive-closure-alias-values v2 a2))
	(recursive-closure-procedure-variables v1)
	(recursive-closure-lambda-expressions v1)
	(recursive-closure-index v1)))
      ((and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
       (new-alias-perturbation-tagged-value
	(plus (vlad-cons (get-perturbation-tagged-value-primal v1)
			 (get-perturbation-tagged-value-primal v2)))
	(plus-alias (vlad-cons (get-perturbation-tagged-value-primal v1)
			       (get-perturbation-tagged-value-primal v2))
		    (vlad-cons-alias
		     (get-perturbation-tagged-value-primal v1)
		     (get-perturbation-tagged-value-primal-alias v1 a1)
		     (get-perturbation-tagged-value-primal v2)
		     (get-perturbation-tagged-value-primal-alias v2 a2))
		    #f)))
      ((and (bundle? v1) (bundle? v2))
       (let ((as1 (get-bundle-aliases v1 a1))
	     (as2 (get-bundle-aliases v2 a2)))
	(new-alias-bundle
	 (plus (vlad-cons (get-bundle-primal v1)
			  (get-bundle-primal v2)))
	 (plus-alias (vlad-cons (get-bundle-primal v1)
				(get-bundle-primal v2))
		     (vlad-cons-alias (get-bundle-primal v1)
				      (first as1)
				      (get-bundle-primal v2)
				      (first as2))
		     #f)
	 (plus (vlad-cons (get-bundle-tangent v1)
			  (get-bundle-tangent v2)))
	 (plus-alias (vlad-cons (get-bundle-tangent v1)
				(get-bundle-tangent v2))
		     (vlad-cons-alias (get-bundle-tangent v1)
				      (second as1)
				      (get-bundle-tangent v2)
				      (second as2))
		     #f))))
      ((and (sensitivity-tagged-value? v1)
	    (sensitivity-tagged-value? v2))
       (new-alias-sensitivity-tagged-value
	(plus (vlad-cons (get-sensitivity-tagged-value-primal v1)
			 (get-sensitivity-tagged-value-primal v2)))
	(plus-alias (vlad-cons (get-sensitivity-tagged-value-primal v1)
			       (get-sensitivity-tagged-value-primal v2))
		    (vlad-cons-alias
		     (get-sensitivity-tagged-value-primal v1)
		     (get-sensitivity-tagged-value-primal-alias v1 a1)
		     (get-sensitivity-tagged-value-primal v2)
		     (get-sensitivity-tagged-value-primal-alias v2 a2))
		    #f)))
      ((and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
       (new-alias-reverse-tagged-value
	(plus (vlad-cons (get-reverse-tagged-value-primal v1)
			 (get-reverse-tagged-value-primal v2)))
	(plus-alias (vlad-cons (get-reverse-tagged-value-primal v1)
			       (get-reverse-tagged-value-primal v2))
		    (vlad-cons-alias
		     (get-reverse-tagged-value-primal v1)
		     (get-reverse-tagged-value-primal-alias v1 a1)
		     (get-reverse-tagged-value-primal v2)
		     (get-reverse-tagged-value-primal-alias v2 a2))
		    #f)))
      ((and (vlad-pair? v1) (vlad-pair? v2))
       (vlad-cons-alias (plus (vlad-cons (vlad-car v1) (vlad-car v2)))
			(plus-alias (vlad-cons (vlad-car v1) (vlad-car v2))
				    (vlad-cons-alias (vlad-car v1)
						     (vlad-car-alias v1 a1)
						     (vlad-car v2)
						     (vlad-car-alias v2 a2))
				    #f)
			(plus (vlad-cons (vlad-cdr v1) (vlad-cdr v2)))
			(plus-alias (vlad-cons (vlad-cdr v1) (vlad-cdr v2))
				    (vlad-cons-alias (vlad-cdr v1)
						     (vlad-cdr-alias v1 a1)
						     (vlad-cdr v2)
						     (vlad-cdr-alias v2 a2))
				    #f)))
      (else (empty-alias)))))
   (else (empty-alias)))))

(define (*j-alias v a top?)
 (let ((instance (find-instance '*j v)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases! instance (cons a (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v)
    ;; widening case H16
    (unionize-alias (map *j (get-union-values v))
		    (map (lambda (u a) (*j-alias u a #f))
			 (get-union-values v)
			 (get-union-alias-values v a))))
   ((or (vlad-empty-list? v)
	(vlad-true? v)
	(vlad-false? v)
	(vlad-real? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (new-alias-reverse-tagged-value v a))
   ((primitive-procedure? v) (alias-for (primitive-procedure-reverse v)))
   ((nonrecursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-nonrecursive-closure
     (map *j (get-nonrecursive-closure-values v))
     (map (lambda (v a) (*j-alias v a #f))
	  (get-nonrecursive-closure-values v)
	  (get-nonrecursive-closure-alias-values v a))
     (reverse-transform (nonrecursive-closure-lambda-expression v))))
   ((recursive-closure? v)
    ;; See the note in abstract-environment=?.
    (new-alias-recursive-closure
     (map *j (get-recursive-closure-values v))
     (map (lambda (v a) (*j-alias v a #f))
	  (get-recursive-closure-values v)
	  (get-recursive-closure-alias-values v a))
     (map-vector reverseify (recursive-closure-procedure-variables v))
     (map-n-vector (lambda (i)
		    (reverse-transform-internal
		     (vector-ref (recursive-closure-lambda-expressions v) i)
		     (vector->list (recursive-closure-procedure-variables v))
		     (vector->list (recursive-closure-lambda-expressions v))
		     i))
		   (vector-length (recursive-closure-lambda-expressions v)))
     (recursive-closure-index v)))
   (else (internal-error)))))

(define (*j-inverse-alias v-reverse a-reverse top?)
 (let ((instance (find-instance '*j-inverse v-reverse)))
  (cond
   ((and instance (not top?) (not (inline? instance)))
    (set-new-input-aliases!
     instance (cons a-reverse (new-input-aliases instance)))
    (copy-alias (output-alias instance)))
   ((union? v-reverse)
    ;; widening case H17
    (unionize-alias (map *j-inverse (get-union-values v-reverse))
		    (map (lambda (u-reverse a-reverse)
			  (*j-inverse-alias u-reverse a-reverse #f))
			 (get-union-values v-reverse)
			 (get-union-alias-values v-reverse a-reverse))))
   ((or (vlad-empty-list? v-reverse)
	(vlad-true? v-reverse)
	(vlad-false? v-reverse)
	(vlad-real? v-reverse)
	(primitive-procedure? v-reverse)
	(perturbation-tagged-value? v-reverse)
	(bundle? v-reverse)
	(sensitivity-tagged-value? v-reverse)
	(vlad-pair? v-reverse))
    (empty-alias))
   ((nonrecursive-closure? v-reverse)
    (let ((b (find-if (lambda (b)
		       (deep-abstract-value=?
			v-reverse
			(primitive-procedure-reverse (value-binding-value b))))
		      *value-bindings*)))
     (cond
      (b (alias-for (value-binding-value b)))
      ((tagged? 'reverse (nonrecursive-closure-tags v-reverse))
       ;; See the note in abstract-environment=?.
       (new-alias-nonrecursive-closure
	(map *j-inverse (get-nonrecursive-closure-values v-reverse))
	(map (lambda (v-reverse a-reverse)
	      (*j-inverse-alias v-reverse a-reverse #f))
	     (get-nonrecursive-closure-values v-reverse)
	     (get-nonrecursive-closure-alias-values v-reverse a-reverse))
	(reverse-transform-inverse
	 (nonrecursive-closure-lambda-expression v-reverse))))
      (else (empty-alias)))))
   ((recursive-closure? v-reverse)
    (if (tagged? 'reverse (recursive-closure-tags v-reverse))
	;; See the note in abstract-environment=?.
	(new-alias-recursive-closure
	 (map *j-inverse (get-recursive-closure-values v-reverse))
	 (map (lambda (v-reverse a-reverse)
	       (*j-inverse-alias v-reverse a-reverse #f))
	      (get-recursive-closure-values v-reverse)
	      (get-recursive-closure-alias-values v-reverse a-reverse))
	 (map-vector
	  unreverseify (recursive-closure-procedure-variables v-reverse))
	 (map-vector reverse-transform-inverse
		     (recursive-closure-lambda-expressions v-reverse))
	 (recursive-closure-index v-reverse))
	(empty-alias)))
   ((reverse-tagged-value? v-reverse)
    (get-reverse-tagged-value-primal-alias v-reverse a-reverse))
   (else (internal-error)))))

;;; needs work: The widening case is not annotated yet.
(define (alias-read-real v a)
 (assert (compatible-alias? v a))
 (if (vlad-empty-list? v) (alias-for (abstract-real)) (empty-alias)))

(define (alias-ad f) (lambda (v a) (f v a #f)))

;;; needs work: The widening case is not annotated yet.
(define (alias-unary-predicate f)
 (lambda (v a)
  (assert (compatible-alias? v a))
  (if (and (some f (union-members v))
	   (some (lambda (u) (not (f u))) (union-members v)))
      (alias-for (abstract-boolean))
      (empty-alias))))

;;; needs work: The widening case is not annotated yet.
(define (alias-real v a)
 (assert (compatible-alias? v a))
 (if (some (lambda (u) (vlad-real? u)) (union-members v))
     (alias-for (abstract-real))
     (empty-alias)))

;;; needs work: The widening case is not annotated yet.
(define (alias-unary-real f s)
 (lambda (v a)
  (assert (compatible-alias? v a))
  (if (some (lambda (u) (and (vlad-real? u) (not (real? u))))
	    (union-members v))
      (alias-for (abstract-real))
      (empty-alias))))

;;; needs work: The widening case is not annotated yet.
(define (alias-unary-real-predicate f s)
 (lambda (v a)
  (assert (compatible-alias? v a))
  (if (or (some (lambda (u) (and (vlad-real? u) (not (real? u))))
		(union-members v))
	  (and (some (lambda (u) (and (vlad-real? u) (real? u) (f u)))
		     (union-members v))
	       (some (lambda (u) (and (vlad-real? u) (real? u) (not (f u))))
		     (union-members v))))
      (alias-for (abstract-boolean))
      (empty-alias))))

;;; needs work: The widening case is not annotated yet.
(define (alias-binary-real f s)
 (lambda (v a)
  (assert (compatible-alias? v a))
  (if (some (lambda (u)
	     (and (vlad-pair? u)
		  (some (lambda (u1)
			 (some (lambda (u2)
				(and (vlad-real? u1)
				     (vlad-real? u2)
				     ;; needs work: This may be imprecise for
				     ;;             *, /, and atan.
				     (or (not (real? u1)) (not (real? u2)))))
			       (union-members (vlad-cdr u))))
			(union-members (vlad-car u)))))
	    (union-members v))
      (alias-for (abstract-real))
      (empty-alias))))

;;; needs work: The widening case is not annotated yet.
(define (alias-binary-real-predicate f s)
 (lambda (v a)
  (assert (compatible-alias? v a))
  (if (or (some (lambda (u)
		 (and (vlad-pair? u)
		      (some (lambda (u1)
			     (some (lambda (u2)
				    (and (vlad-real? u1)
					 (vlad-real? u2)
					 (or (not (real? u1))
					     (not (real? u2)))))
				   (union-members (vlad-cdr u))))
			    (union-members (vlad-car u)))))
		(union-members v))
	  (and (some (lambda (u)
		      (and (vlad-pair? u)
			   (some (lambda (u1)
				  (some (lambda (u2)
					 (and (vlad-real? u1)
					      (vlad-real? u2)
					      (real? u1)
					      (real? u2)
					      (f u1 u2)))
					(union-members (vlad-cdr u))))
				 (union-members (vlad-car u)))))
		     (union-members v))
	       (some (lambda (u)
		      (and (vlad-pair? u)
			   (some (lambda (u1)
				  (some (lambda (u2)
					 (and (vlad-real? u1)
					      (vlad-real? u2)
					      (real? u1)
					      (real? u2)
					      (not (f u1 u2))))
					(union-members (vlad-cdr u))))
				 (union-members (vlad-car u)))))
		     (union-members v))))
      (alias-for (abstract-boolean))
      (empty-alias))))

(define (alias-if-procedure2 v1 a1 v2 a2 v3 a3)
 (assert (and (compatible-alias? v1 a1)
	      (compatible-alias? v2 a2)
	      (compatible-alias? v3 a3)))
 (cond
  ((union? v1)
   ;; widening case L1
   (unionize-alias
    (map (lambda (u1) (abstract-if-procedure2 u1 v2 v3)) (get-union-values v1))
    (map (lambda (u1 a1) (alias-if-procedure2 u1 a1 v2 a2 v3 a3))
	 (get-union-values v1)
	 (get-union-alias-values v1 a1))))
  ((vlad-false? v1) (alias-apply v3 a3 (vlad-empty-list) (empty-alias) #f))
  (else (alias-apply v2 a2 (vlad-empty-list) (empty-alias) #f))))

(define (alias-if-procedure1 v1 a1 v23 a23)
 (assert (and (compatible-alias? v1 a1) (compatible-alias? v23 a23)))
 (cond
  ((union? v23)
   ;; widening case L2
   (unionize-alias
    (map (lambda (u23) (abstract-if-procedure1 v1 u23)) (get-union-values v23))
    (map (lambda (u23 a23) (alias-if-procedure1 v1 a1 u23 a23))
	 (get-union-values v23)
	 (get-union-alias-values v23 a23))))
  ((vlad-pair? v23)
   (alias-if-procedure2 v1
			a1
			(vlad-car v23)
			(vlad-car-alias v23 a23)
			(vlad-cdr v23)
			(vlad-cdr-alias v23 a23)))
  (else (empty-alias))))

(define (alias-if-procedure v a)
 (assert (compatible-alias? v a))
 (cond
  ((union? v)
   ;; widening case L3
   (unionize-alias
    (map (lambda (u) (abstract-if-procedure u)) (get-union-values v))
    (map (lambda (u a) (alias-if-procedure u a))
	 (get-union-values v)
	 (get-union-alias-values v a))))
  ((vlad-pair? v)
   (alias-if-procedure1
    (vlad-car v) (vlad-car-alias v a) (vlad-cdr v) (vlad-cdr-alias v a)))
  (else (empty-alias))))

(define (some-alias? a)
 (some (lambda (color1)
	(some (lambda (color2)
	       (and (not (eq? color1 color2)) (color=? color1 color2)))
	      a))
       a))

(define (write-alias string a)
 (format #t "~a alias: ~s~%"
	 string
	 (map (lambda (color-is) (map cdr color-is))
	      (transitive-equivalence-classesp
	       (lambda (color-i1 color-i2)
		(color=? (car color-i1) (car color-i2)))
	       (map-indexed cons a)))))

(define (write-structure-alias v a)
 (when (some-alias? a)
  (write-alias "structure" a)
  ;; debugging
  (when #f
   (write (safe-externalize v))
   (newline))))

(define (write-ad-alias string v a)
 (when (some-alias? a)
  (write-alias string a)
  ;; debugging
  (when #f
   (write (safe-externalize v))
   (newline))))

(define (write-aliasing vs)
 (for-each
  (lambda (instance)
   (unless (inline? instance)
    (when (some-alias? (input-alias instance))
     (write-alias (string-append (c:instance-name instance) " input")
		  (input-alias instance))
     ;; debugging
     (when #f
      (write (safe-externalize (function-instance-v1 instance)))
      (newline)
      (write (safe-externalize (function-instance-v2 instance)))
      (newline)))
    (when (some-alias? (output-alias instance))
     (write-alias (string-append (c:instance-name instance) " output")
		  (output-alias instance))
     ;; debugging
     (when #f
      (write (safe-externalize (function-instance-v1 instance)))
      (newline)
      (write (safe-externalize (function-instance-v2 instance)))
      (newline)))))
  *function-instances*)
 (for-each
  (lambda (instance)
   (unless (inline? instance)
    (when (some-alias? (input-alias instance))
     (write-alias (string-append (c:instance-name instance) " input")
		  (input-alias instance))
     ;; debugging
     (when #f
      (write (safe-externalize (widener-instance-v1 instance)))
      (newline)
      (write (safe-externalize (widener-instance-v2 instance)))
      (newline)))
    (when (some-alias? (output-alias instance))
     (write-alias (string-append (c:instance-name instance) " output")
		  (output-alias instance))
     ;; debugging
     (when #f
      (write (safe-externalize (widener-instance-v1 instance)))
      (newline)
      (write (safe-externalize (widener-instance-v2 instance)))
      (newline)))))
  *widener-instances*)
 (for-each (lambda (v) (when (boxed? v) (write-structure-alias v (alias v))))
	   vs)
 (for-each
  (lambda (b)
   (for-each (lambda (instance)
	      (unless (inline? instance)
	       (write-ad-alias
		(string-append (c:instance-name instance) " input")
		(primitive-procedure-instance-v instance)
		(input-alias instance))
	       (write-ad-alias
		(string-append (c:instance-name instance) " output")
		(primitive-procedure-instance-v instance)
		(output-alias instance))))
	     (primitive-procedure-instances (value-binding-value b))))
  *value-bindings*))

(define (determine-aliasing! e vs)
 (profile
  "~a determine-aliasing! 01~%"
  (lambda ()
   (for-each
    (lambda (v)
     (when (or (union? v) (not (scalar-value? v)))
      (let ((iis (map (lambda (v-is) (map cdr v-is))
		      (transitive-equivalence-classesp
		       (lambda (v-i1 v-i2) (slot=? (car v-i1) (car v-i2)))
		       (map-indexed cons (slots v))))))
       (cond
	((nonrecursive-closure? v)
	 (set-nonrecursive-closure-equivalent-slot-indices! v iis))
	((recursive-closure? v)
	 (set-recursive-closure-equivalent-slot-indices! v iis))
	((perturbation-tagged-value? v)
	 (set-perturbation-tagged-value-equivalent-slot-indices! v iis))
	((bundle? v) (set-bundle-equivalent-slot-indices! v iis))
	((sensitivity-tagged-value? v)
	 (set-sensitivity-tagged-value-equivalent-slot-indices! v iis))
	((reverse-tagged-value? v)
	 (set-reverse-tagged-value-equivalent-slot-indices! v iis))
	((vlad-pair? v) (set-vlad-pair-equivalent-slot-indices! v iis))
	((union? v) (set-union-equivalent-slot-indices! v iis))
	(else (internal-error))))))
    vs)))
 (profile
  "~a determine-aliasing! 02~%"
  (lambda ()
   (for-each
    (lambda (v)
     (when (boxed? v)
      (cond
       ((nonrecursive-closure? v)
	(set-alias! v (aliases-for (get-nonrecursive-closure-values v))))
       ((recursive-closure? v)
	(set-alias! v (aliases-for (get-recursive-closure-values v))))
       ((perturbation-tagged-value? v)
	(set-alias! v (alias-for (get-perturbation-tagged-value-primal v))))
       ((bundle? v)
	(set-alias!
	 v (aliases-for (list (get-bundle-primal v) (get-bundle-tangent v)))))
       ((sensitivity-tagged-value? v)
	(set-alias! v (alias-for (get-sensitivity-tagged-value-primal v))))
       ((reverse-tagged-value? v)
	(set-alias! v (alias-for (get-reverse-tagged-value-primal v))))
       ((vlad-pair? v)
	(set-alias! v (aliases-for (list (vlad-car v) (vlad-cdr v)))))
       ((union? v)
	(set-alias! v (add-tag-alias v (aliases-for (get-union-values v)))))
       (else (internal-error)))))
    vs)))
 (profile
  "~a determine-aliasing! 03~%"
  (lambda ()
   (for-each (lambda (instance)
	      (unless (inline? instance)
	       (set-input-alias!
		instance
		(aliases-for (list (function-instance-v1 instance)
				   (function-instance-v2 instance))))
	       (set-output-alias!
		instance (alias-for (instance-return-value instance)))))
	     *function-instances*)))
 (profile
  "~a determine-aliasing! 04~%"
  (lambda ()
   (for-each (lambda (instance)
	      (unless (inline? instance)
	       (set-input-alias!
		instance (alias-for (widener-instance-v1 instance)))
	       (set-output-alias!
		instance (alias-for (instance-return-value instance)))))
	     *widener-instances*)))
 (profile
  "~a determine-aliasing! 05~%"
  (lambda ()
   (for-each
    (lambda (b)
     (for-each
      (lambda (instance)
       (unless (inline? instance)
	(set-input-alias!
	 instance (alias-for (primitive-procedure-instance-v instance)))
	(set-output-alias!
	 instance (alias-for (instance-return-value instance)))))
      (primitive-procedure-instances (value-binding-value b))))
    *value-bindings*)))
 (let loop ()
  ;; debugging
  (when #f
   (format #t "aliasing pass~%")
   (write-aliasing vs))
  (let ((again? #f))
   (profile
    "~a determine-aliasing! 06~%"
    (lambda ()
     (for-each (lambda (v) (when (boxed? v) (set-new-aliases! v '()))) vs)))
   (profile "~a determine-aliasing! 07~%"
	    (lambda ()
	     (for-each (lambda (instance)
			(unless (inline? instance)
			 (set-new-input-aliases! instance '())))
		       *function-instances*)))
   (profile "~a determine-aliasing! 08~%"
	    (lambda ()
	     (for-each (lambda (instance)
			(unless (inline? instance)
			 (set-new-input-aliases! instance '())))
		       *widener-instances*)))
   (profile
    "~a determine-aliasing! 09~%"
    (lambda ()
     (for-each
      (lambda (b)
       (for-each (lambda (instance)
		  (unless (inline? instance)
		   (set-new-input-aliases! instance '())))
		 (primitive-procedure-instances (value-binding-value b))))
      *value-bindings*)))
   (profile
    "~a determine-aliasing! 10~%"
    (lambda ()
     (let ((vs (environment-binding-values (first (environment-bindings e)))))
      (alias-eval e vs (map alias-for vs)))))
   (profile
    "~a determine-aliasing! 11~%"
    (lambda ()
     (for-each
      (lambda (instance)
       (unless (inline? instance)
	(let* ((as (split-alias
		    (input-alias instance)
		    (list (number-of-slots (function-instance-v1 instance))
			  (number-of-slots (function-instance-v2 instance)))))
	       (a (copy-alias (alias-apply (function-instance-v1 instance)
					   (first as)
					   (function-instance-v2 instance)
					   (second as)
					   #t))))
	 (unless (alias=? a (output-alias instance))
	  (set! again? #t)
	  (set-output-alias! instance a)))))
      *function-instances*)))
   (profile
    "~a determine-aliasing! 12~%"
    (lambda ()
     (for-each
      (lambda (instance)
       (unless (inline? instance)
	(let ((a (copy-alias (widen-alias (widener-instance-v1 instance)
					  (input-alias instance)
					  (widener-instance-v2 instance)
					  #t))))
	 (unless (alias=? a (output-alias instance))
	  (set! again? #t)
	  (set-output-alias! instance a)))))
      *widener-instances*)))
   (profile
    "~a determine-aliasing! 13~%"
    (lambda ()
     (for-each
      (lambda (b)
       (for-each
	(lambda (instance)
	 (unless (inline? instance)
	  (let ((a (copy-alias
		    ;; needs work: This is a kludge to allow us to call the
		    ;;             alias procedures with a #t third argument
		    ;;             that alias-ad does not allow. This works
		    ;;             because the only non-inlined primitives must
		    ;;             be ad primitives.
		    ((case (primitive-procedure-instance-symbol instance)
		      ((zero) zero-alias)
		      ((perturb) perturb-alias)
		      ((unperturb) unperturb-alias)
		      ((primal) primal-alias)
		      ((tangent) tangent-alias)
		      ((bundle) bundle-alias1)
		      ((sensitize) sensitize-alias)
		      ((unsensitize) unsensitize-alias)
		      ((plus) plus-alias)
		      ((*j) *j-alias)
		      ((*j-inverse) *j-inverse-alias)
		      (else (internal-error)))
		     (primitive-procedure-instance-v instance)
		     (input-alias instance)
		     #t))))
	   (unless (alias=? a (output-alias instance))
	    (set! again? #t)
	    (set-output-alias! instance a)))))
	(primitive-procedure-instances (value-binding-value b))))
      *value-bindings*)))
   ;; Here and below the null? checks are a workaround to a situation where
   ;; coalesce-aliases is called with no aliases. This happens because of
   ;; imprecision and the fact that the analysis creates boxed abstract values
   ;; that are never allocated and noninlined function instances and AD
   ;; primitives that are never called. Someday we can modify the code
   ;; generator to not generate code for such. But we would also need to keep
   ;; track of unboxed abstract values that are never allocated and inlined
   ;; function instances and AD primitives that are never called.
   (profile "~a determine-aliasing! 14~%"
	    (lambda ()
	     (for-each (lambda (v)
			(when (and (boxed? v) (not (null? (new-aliases v))))
			 (let ((a (coalesce-aliases (new-aliases v))))
			  (unless (alias=? a (alias v))
			   (set! again? #t)
			   (set-alias! v a)))))
		       vs)))
   (profile
    "~a determine-aliasing! 15~%"
    (lambda ()
     (for-each
      (lambda (instance)
       (unless (or (inline? instance) (null? (new-input-aliases instance)))
	(let ((a (coalesce-aliases (new-input-aliases instance))))
	 (unless (alias=? a (input-alias instance))
	  (set! again? #t)
	  (set-input-alias! instance a)))))
      *function-instances*)))
   (profile
    "~a determine-aliasing! 16~%"
    (lambda ()
     (for-each
      (lambda (instance)
       (unless (or (inline? instance) (null? (new-input-aliases instance)))
	(let ((a (coalesce-aliases (new-input-aliases instance))))
	 (unless (alias=? a (input-alias instance))
	  (set! again? #t)
	  (set-input-alias! instance a)))))
      *widener-instances*)))
   (profile
    "~a determine-aliasing! 17~%"
    (lambda ()
     (for-each
      (lambda (b)
       (for-each
	(lambda (instance)
	 (unless (or (inline? instance) (null? (new-input-aliases instance)))
	  (let ((a (coalesce-aliases (new-input-aliases instance))))
	   (unless (alias=? a (input-alias instance))
	    (set! again? #t)
	    (set-input-alias! instance a)))))
	(primitive-procedure-instances (value-binding-value b))))
      *value-bindings*)))
   (when again? (loop))))
 ;; debugging
 (when #f
  (format #t "aliasing final~%")
  (write-aliasing vs)))

;;; Intermediate-language code generator

;;; We box abstract values, not slots of aggregates, not arguments, not return
;;; values, not local variables, not type tags, and not unions.

;;; here I am: In all or almost all of the cases where we eliminate void
;;;            expressions, parameters, arguments, or functions that return
;;;            void results we unsoundly remove code that might do I/O, panic,
;;;            signal an error, or not terminate.

(define (void? v)
 (let ((p?
	(cond
	 ((tag? v) #f)
	 ((union? v) (union-void? v))
	 ((abstract-real? v) #f)
	 ((scalar-value? v) #t)
	 ((nonrecursive-closure? v) (nonrecursive-closure-void? v))
	 ((recursive-closure? v) (recursive-closure-void? v))
	 ((perturbation-tagged-value? v) (perturbation-tagged-value-void? v))
	 ((bundle? v) (bundle-void? v))
	 ((sensitivity-tagged-value? v) (sensitivity-tagged-value-void? v))
	 ((reverse-tagged-value? v) (reverse-tagged-value-void? v))
	 ((vlad-pair? v) (vlad-pair-void? v))
	 (else (internal-error)))))
  (assert (boolean? p?))
  p?))

(define (deep-void? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  35
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
 (for-each (lambda (v) (set-nonrecursive-closure-void?! v (deep-void? v)))
	   *nonrecursive-closures*)
 (for-each (lambda (v) (set-recursive-closure-void?! v (deep-void? v)))
	   *recursive-closures*)
 (for-each (lambda (v) (set-perturbation-tagged-value-void?! v (deep-void? v)))
	   *perturbation-tagged-values*)
 (for-each (lambda (v) (set-bundle-void?! v (deep-void? v))) *bundles*)
 (for-each (lambda (v) (set-sensitivity-tagged-value-void?! v (deep-void? v)))
	   *sensitivity-tagged-values*)
 (for-each (lambda (v) (set-reverse-tagged-value-void?! v (deep-void? v)))
	   *reverse-tagged-values*)
 (for-each (lambda (v) (set-vlad-pair-void?! v (deep-void? v))) *vlad-pairs*)
 (for-each (lambda (v) (set-union-void?! v (deep-void? v))) *unions*))

(define (for-each-call-site s f)
 ;; needs work: This ignores if-procedure call sites.
 (for-each
  (lambda (e)
   (when (application? e)
    (for-each
     (lambda (b)
      (let ((v1 (abstract-eval1
		 (application-callee e)
		 (restrict-environment
		  (environment-binding-values b)
		  (application-callee-indices e)))))
       (when (and (primitive-procedure? v1)
		  (eq? (primitive-procedure-symbol v1) s))
	(f (abstract-eval1
	    (application-argument e)
	    (restrict-environment (environment-binding-values b)
				  (application-argument-indices e)))))))
     (environment-bindings e))))
  *expressions*))

(define (union-abstract-values vs1 vs2) (unionp abstract-value=? vs1 vs2))

(define (all-real*real-abstract-subvalues v)
 (union-abstract-values
  (list v)
  (cond
   ((union? v)
    (map-reduce union-abstract-values
		'()
		all-real*real-abstract-subvalues
		(get-union-values v)))
   ((vlad-pair? v)
    (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
     (cond
      ((union? v1)
       (map-reduce
	union-abstract-values
	'()
	(lambda (u1) (all-real*real-abstract-subvalues (vlad-cons u1 v2)))
	(get-union-values v1)))
      ((union? v2)
       (map-reduce
	union-abstract-values
	'()
	(lambda (u2) (all-real*real-abstract-subvalues (vlad-cons v1 u2)))
	(get-union-values v2)))
      ((and (vlad-real? v1) (vlad-real? v2)) '())
      (else '()))))
   (else '()))))

(define (all-real*real-instances! s)
 (lambda ()
  (for-each-call-site
   s
   (lambda (v)
    (for-each (lambda (v) (new-instance s v))
	      ;; needs work: to make imperative
	      (all-real*real-abstract-subvalues v))))))

(define (all-real-abstract-subvalues v)
 (union-abstract-values (list v)
			(cond ((union? v)
			       (map-reduce union-abstract-values
					   '()
					   all-real-abstract-subvalues
					   (get-union-values v)))
			      ((vlad-real? v) '())
			      (else '()))))

(define (all-real-instances! s)
 (lambda ()
  (for-each-call-site
   s
   (lambda (v)
    (for-each (lambda (v) (new-instance s v))
	      ;; needs work: to make imperative
	      (all-real-abstract-subvalues v))))))

(define (all-type-abstract-subvalues v)
 (union-abstract-values (list v)
			(cond ((union? v)
			       (map-reduce union-abstract-values
					   '()
					   all-type-abstract-subvalues
					   (get-union-values v)))
			      (else '()))))

(define (all-type-instances! s)
 (lambda ()
  (for-each-call-site
   s
   (lambda (v)
    (for-each (lambda (v) (new-instance s v))
	      ;; needs work: to make imperative
	      (all-type-abstract-subvalues v))))))

(define (all-instances! s)
 (lambda () (for-each-call-site s (lambda (v) (new-instance s v)))))

(define (all-null-abstract-subvalues v)
 (union-abstract-values (list v)
			(cond ((union? v)
			       (map-reduce union-abstract-values
					   '()
					   all-null-abstract-subvalues
					   (get-union-values v)))
			      ((vlad-empty-list? v) '())
			      (else '()))))

(define (all-read-real-instances!)
 (for-each-call-site
  'read-real
  (lambda (v)
   (for-each (lambda (v) (new-instance 'read-real v))
	     ;; needs work: to make imperative
	     (all-null-abstract-subvalues v)))))

(define (descend? s)
 (case s
  ((zero) (lambda (v) #t))
  ((perturb)
   (lambda (v)
    (and (not (perturbation-tagged-value? v))
	 (not (bundle? v))
	 (not (sensitivity-tagged-value? v))
	 (not (reverse-tagged-value? v))
	 (not (vlad-pair? v)))))
  ((unperturb)
   (lambda (v)
    (and (perturbation-value? v) (not (perturbation-tagged-value? v)))))
  ((primal) (lambda (v) (and (forward-value? v) (not (bundle? v)))))
  ((tangent) (lambda (v) (and (forward-value? v) (not (bundle? v)))))
  ((bundle)
   (lambda (v)
    (and (not (perturbation-tagged-value? v))
	 (not (bundle? v))
	 (not (sensitivity-tagged-value? v))
	 (not (reverse-tagged-value? v))
	 (not (vlad-pair? v)))))
  ((sensitize)
   (lambda (v)
    (and (not (perturbation-tagged-value? v))
	 (not (bundle? v))
	 (not (sensitivity-tagged-value? v))
	 (not (reverse-tagged-value? v))
	 (not (vlad-pair? v)))))
  ((unsensitize)
   (lambda (v)
    (and (sensitivity-value? v) (not (sensitivity-tagged-value? v)))))
  ((plus) (lambda (v) #t))
  ((*j)
   (lambda (v)
    (and (not (perturbation-tagged-value? v))
	 (not (bundle? v))
	 (not (sensitivity-tagged-value? v))
	 (not (reverse-tagged-value? v))
	 (not (vlad-pair? v)))))
  ((*j-inverse)
   (lambda (v) (and (reverse-value? v) (not (reverse-tagged-value? v)))))
  (else (internal-error))))

(define (all-unary-abstract-subvalues descend? v)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  36
  (let outer ((v v) (vs '()) (n '()) (k (lambda (n vs) n)))
   (cond
    ((memq v vs) (k n vs))
    ((union? v)
     (let inner ((us (get-union-values v))
		 (vs (cons v vs))
		 (n (adjoinp abstract-value=? v n)))
      (if (null? us)
	  (k n vs)
	  (outer (first us) vs n (lambda (n vs) (inner (rest us) vs n))))))
    ;; here I am: Need to return an empty abstract value for certain inputs to
    ;;            certain AD primitives.
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

(define (bundle-aggregates-match? v1 v2)
 (and (or (and (nonrecursive-closure? v1)
	       (nonrecursive-closure? v2)
	       (perturbation-parameter? (nonrecursive-closure-parameter v2))
	       (nonrecursive-closure-match? v1 (unperturb v2)))
	  (and (recursive-closure? v1)
	       (recursive-closure? v2)
	       (perturbation-parameter? (recursive-closure-parameter v2))
	       (recursive-closure-match? v1 (unperturb v2))))
      (not (empty-abstract-value? (bundle (vlad-cons v1 v2))))))

(define (plus-aggregates-match? v1 v2)
 (and (or (and (nonrecursive-closure? v1)
	       (nonrecursive-closure? v2)
	       (nonrecursive-closure-match? v1 v2))
	  (and (recursive-closure? v1)
	       (recursive-closure? v2)
	       (recursive-closure-match? v1 v2))
	  (and (perturbation-tagged-value? v1) (perturbation-tagged-value? v2))
	  (and (bundle? v1) (bundle? v2))
	  (and (sensitivity-tagged-value? v1) (sensitivity-tagged-value? v2))
	  (and (reverse-tagged-value? v1) (reverse-tagged-value? v2))
	  (and (vlad-pair? v1) (vlad-pair? v2)))
      (not (empty-abstract-value? (plus (vlad-cons v1 v2))))))

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
	;; needs work: Do we need to update vs here?
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
	      (outer2
	       (first vs1)
	       (first vs2)
	       vs
	       cs
	       n
	       (lambda (n vs cs) (inner (rest vs1) (rest vs2) vs cs n))))))
	;; here I am: Need to return an empty abstract value for nonconforming
	;;            inputs.
	(else (k (adjoinp abstract-value=? (vlad-cons v1 v2) n) vs cs))))
 (time-it-bucket
  37
  (outer1 v '() '() '() (lambda (n vs cs) n))))

(define (if-function-instances2! v1 v2 v3)
 (cond
  ((union? v1)
   ;; widening case L1
   (for-each (lambda (u1) (if-function-instances2! u1 v2 v3))
	     (get-union-values v1)))
  ((vlad-false? v1)
   (cond ((union? v3)
	  ;; widening case I
	  (for-each (lambda (u3) (if-function-instances2! v1 v2 u3))
		    (get-union-values v3)))
	 ((closure? v3) (new-function-instance v3 (vlad-empty-list)))))
  (else (cond ((union? v2)
	       ;; widening case I
	       (for-each (lambda (u2) (if-function-instances2! v1 u2 v3))
			 (get-union-values v2)))
	      ((closure? v2) (new-function-instance v2 (vlad-empty-list)))))))

(define (if-function-instances1! v1 v23)
 (cond ((union? v23)
	;; widening case L2
	(for-each (lambda (u23) (if-function-instances1! v1 u23))
		  (get-union-values v23)))
       ((vlad-pair? v23)
	(if-function-instances2! v1 (vlad-car v23) (vlad-cdr v23)))))

(define (if-function-instances! v)
 (cond ((union? v)
	;; widening case L3
	(for-each (lambda (u) (if-function-instances! u))
		  (get-union-values v)))
       ((vlad-pair? v) (if-function-instances1! (vlad-car v) (vlad-cdr v)))))

(define (all-function-instances!)
 (for-each
  (lambda (e)
   (when (and (application? e)
	      ;; This handling of LET is an optimization.
	      (not (lambda-expression? (application-callee e))))
    (for-each
     (lambda (b)
      (let ((v1 (abstract-eval1
		 (application-callee e)
		 (restrict-environment (environment-binding-values b)
				       (application-callee-indices e))))
	    (v2 (abstract-eval1
		 (application-argument e)
		 (restrict-environment (environment-binding-values b)
				       (application-argument-indices e)))))
       (cond
	((union? v1)
	 (for-each
	  (lambda (u1)
	   (cond ((and (primitive-procedure? u1)
		       (eq? (primitive-procedure-symbol u1) 'if-procedure))
		  (if-function-instances! v2))
		 ((closure? u1) (new-function-instance u1 v2))))
	  (get-union-values v1)))
	((and (primitive-procedure? v1)
	      (eq? (primitive-procedure-symbol v1) 'if-procedure))
	 (if-function-instances! v2))
	((closure? v1) (new-function-instance v1 v2)))))
     (environment-bindings e))))
  *expressions*))

(define (all-subwidener-instances! v1 v2)
 ;; This is written in CPS so as not to break structure sharing.
 (time-it-bucket
  38
  (let outer ((v1 v1) (v2 v2) (cs '()) (k (lambda (cs) #f)))
   (cond
    ((some (lambda (c) (and (eq? (car c) v1) (eq? (cdr c) v2))) cs) (k cs))
    ((abstract-value=? v1 v2) (k cs))
    ;; Note that we have syntactic constraints that widen (union r1 r2) to R
    ;; but not things like (union (perturbation r1) (perturbation r2)) to
    ;; (perturbation R). Because of this, v1 might be a union even though v2
    ;; might not be.
    ((union? v1)
     ;; widening case K1
     (new-widener-instance v1 v2)
     (let inner ((us (get-union-values v1)) (cs (cons (cons v1 v2) cs)))
      (if (null? us)
	  (k cs)
	  (outer (first us) v2 cs (lambda (cs) (inner (rest us) cs))))))
    ;; If v2 is an empty abstract value then v1 will be and the first case
    ;; where (abstract-value=? v1 v2) will be taken and this case will never
    ;; be.
    ((union? v2)
     ;; widening case K2
     (new-widener-instance v1 v2)
     (outer v1
	    ;; The fact that such a u2 exists that is a member of v2 relies on
	    ;; our imprecise notion of abstract-value subset. There may be more
	    ;; than one. Any will do, it is only a matter of efficiency to
	    ;; choose between the alternatives. I don't even know how to
	    ;; define/determine which alternative would be most efficient.
	    (find-if (lambda (u2) (abstract-value-subset? v1 u2))
		     (get-union-values v2))
	    ;; needs work: Do we need to update cs here?
	    cs
	    k))
    ((scalar-value? v2)
     ;; widening case K3
     (new-widener-instance v1 v2)
     (k cs))
    ;; This will only be done on conforming structures since the analysis is
    ;; almost union free.
    ;; needs work: To check conformance.
    ;; widening case K4
    (else (new-widener-instance v1 v2)
	  (let inner ((vs1 (aggregate-value-values v1))
		      (vs2 (aggregate-value-values v2))
		      (cs (cons (cons v1 v2) cs)))
	   (if (null? vs1)
	       (k cs)
	       (outer (first vs1)
		      (first vs2)
		      cs
		      (lambda (cs) (inner (rest vs1) (rest vs2) cs))))))))))

(define (all-unary-ad-subinstances! s v)
 (let ((f (case s
	   ((zero) zero)
	   ((perturb) perturb)
	   ((unperturb) unperturb)
	   ((primal) primal)
	   ((tangent) tangent)
	   ((sensitize) sensitize)
	   ((unsensitize) unsensitize)
	   ((*j) *j)
	   ((*j-inverse) *j-inverse)
	   (else (internal-error)))))
  (for-each (lambda (v)
	     (new-instance s v)
	     (when (union? v)
	      ;; The calls to f might issue "might" warnings and might return
	      ;; empty abstract values.
	      ;; widening case H1, H2, H3, H4, H5, H10, H11, H16, H17
	      (for-each (lambda (u) (all-subwidener-instances! (f u) (f v)))
			(get-union-values v))))
	    ;; needs work: to make imperative
	    (all-unary-abstract-subvalues (descend? s) v))))

(define (all-unary-ad-instances! s)
 (lambda ()
  (for-each-call-site s (lambda (v) (all-unary-ad-subinstances! s v)))))

(define (all-binary-ad-subinstances! s v)
 (let ((f? (case s
	    ((bundle) perturbation-tagged-value?)
	    ((plus) (lambda (v) #f))
	    (else (internal-error))))
       (f (case s
	   ((bundle) perturb)
	   ((plus) identity)
	   (else (internal-error))))
       (f-inverse (case s
		   ((bundle) unperturb)
		   ((plus) identity)
		   (else (internal-error))))
       (g (case s
	   ((bundle) bundle)
	   ((plus) plus)
	   (else (internal-error)))))
  (for-each
   (lambda (v)
    (new-instance s v)
    (cond
     ((union? v)
      ;; The calls to g might issue "might" warnings and might return empty
      ;; abstract values.
      ;; widening case H6, H12
      (for-each (lambda (u) (all-subwidener-instances! (g u) (g v)))
		(get-union-values v)))
     ((vlad-pair? v)
      (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
       (cond ((union? v1)
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (for-each (lambda (u1)
			 ;; widening case H7, H13
			 (all-subwidener-instances!
			  (g (vlad-cons u1 v2)) (g (vlad-cons v1 v2))))
			(get-union-values v1)))
	     ((union? v2)
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (for-each (lambda (u2)
			 ;; widening case H8, H14
			 ;; There is no widening case H15
			 (all-subwidener-instances!
			  (g (vlad-cons v1 u2)) (g (vlad-cons v1 v2))))
			(get-union-values v2)))
	     ;; The calls to f and f-inverse should never return an empty
	     ;; abstract value. The call to f-inverse might issue "might"
	     ;; warnings.
	     ((and (f? v2) (union? (f-inverse v2)))
	      ;; The calls to g might issue "might" warnings and might return
	      ;; empty abstract values.
	      (for-each (lambda (u2)
			 ;; widening case H9
			 (all-subwidener-instances!
			  (g (vlad-cons v1 (f u2))) (g (vlad-cons v1 v2))))
			(get-union-values (f-inverse v2)))))))))
   ;; needs work: to make imperative
   (all-binary-abstract-subvalues (descend? s)
				  f?
				  f
				  f-inverse
				  (case s
				   ((bundle) bundle-aggregates-match?)
				   ((plus) plus-aggregates-match?)
				   (else (internal-error)))
				  v))))

(define (all-binary-ad-instances! s)
 (lambda ()
  (for-each-call-site s (lambda (v) (all-binary-ad-subinstances! s v)))))

(define (if-widener-instances2! v1 v2 v3)
 (cond
  ((union? v1)
   (for-each (lambda (u1)
	      ;; widening case L1
	      (all-subwidener-instances! (abstract-if-procedure2 u1 v2 v3)
					 (abstract-if-procedure2 v1 v2 v3))
	      (if-widener-instances2! u1 v2 v3))
	     (get-union-values v1)))
  ((vlad-false? v1)
   (when (union? v3)
    ;; widening case I
    (for-each (lambda (u3)
	       (all-subwidener-instances! (abstract-if-procedure2 v1 v2 u3)
					  (abstract-if-procedure2 v1 v2 v3))
	       (if-widener-instances2! v1 v2 u3))
	      (get-union-values v3))))
  (else (when (union? v2)
	 ;; widening case I
	 (for-each (lambda (u2)
		    (all-subwidener-instances!
		     (abstract-if-procedure2 v1 u2 v3)
		     (abstract-if-procedure2 v1 v2 v3))
		    (if-widener-instances2! v1 u2 v3))
		   (get-union-values v2))))))

(define (if-widener-instances1! v1 v23)
 (cond ((union? v23)
	(for-each (lambda (u23)
		   ;; widening case L2
		   (all-subwidener-instances! (abstract-if-procedure1 v1 u23)
					      (abstract-if-procedure1 v1 v23))
		   (if-widener-instances1! v1 u23))
		  (get-union-values v23)))
       ((vlad-pair? v23)
	(if-widener-instances2! v1 (vlad-car v23) (vlad-cdr v23)))))

(define (if-widener-instances! v)
 (cond ((union? v)
	(for-each (lambda (u)
		   ;; widening case L3
		   (all-subwidener-instances!
		    (abstract-if-procedure u) (abstract-if-procedure v))
		   (if-widener-instances! u))
		  (get-union-values v)))
       ((vlad-pair? v) (if-widener-instances1! (vlad-car v) (vlad-cdr v)))))

(define (all-widener-instances!)
 ;; needs work: The widening case is not annotated yet.
 (all-subwidener-instances! (empty-abstract-value) (abstract-real))
 ;; needs work: The widening case is not annotated yet.
 (all-subwidener-instances! (empty-abstract-value) (abstract-boolean))
 ;; needs work: The widening case is not annotated yet.
 (all-subwidener-instances! (vlad-true) (abstract-boolean))
 ;; needs work: The widening case is not annotated yet.
 (all-subwidener-instances! (vlad-false) (abstract-boolean))
 (for-each (lambda (instance)
	    (let ((v1 (function-instance-v1 instance))
		  (v2 (function-instance-v2 instance)))
	     (when (some-value-tags
		    (lambda (tags2) (prefix-tags? (value-tags v1) tags2)) v2)
	      (abstract-destructure
	       ;; widening case J
	       (lambda (f v)
		(let* ((vs (map f (get-union-values v))) (v (unionize vs)))
		 (for-each (lambda (v1) (all-subwidener-instances! v1 v)) vs)
		 v))
	       (empty-abstract-value)
	       (closure-parameter v1)
	       v2
	       (lambda (v-alist)
		;; bar
		(abstract-eval1
		 (closure-body v1) (construct-environment v1 v-alist)))))))
	   *function-instances*)
 (for-each
  (lambda (e)
   (for-each
    (lambda (b)
     (let ((vs (environment-binding-values b)))
      (cond
       ((constant-expression? e)
	;; widening case E
	(all-subwidener-instances!
	 (constant-expression-value e) (environment-binding-value b)))
       ;; There is no widening case F.
       ((variable-access-expression? e) '())
       ((lambda-expression? e)
	;; widening case G
	;; foo
	(all-subwidener-instances!
	 (new-nonrecursive-closure vs e) (environment-binding-value b)))
       ((application? e)
	(if (lambda-expression? (application-callee e))
	    ;; This handling of LET is an optimization.
	    (let* ((e1 (lambda-expression-body (application-callee e)))
		   (p (lambda-expression-parameter (application-callee e)))
		   (tags1 (lambda-expression-tags (application-callee e)))
		   (v (abstract-eval1 (application-argument e)
				      (restrict-environment
				       vs (application-argument-indices e))))
		   (v0
		    (if (some-value-tags
			 (lambda (tags) (prefix-tags? tags1 tags)) v)
			(abstract-destructure
			 ;; widening case J
			 (lambda (f v)
			  (let* ((vs (map f (get-union-values v)))
				 (v (unionize vs)))
			   (for-each
			    (lambda (v1) (all-subwidener-instances! v1 v)) vs)
			   v))
			 (empty-abstract-value)
			 p
			 v
			 (lambda (v-alist)
			  ;; bar
			  (abstract-eval1
			   e1 (construct-environment-for-let e vs v-alist))))
			(empty-abstract-value))))
	     ;; widening case B-prime
	     (all-subwidener-instances! v0 (environment-binding-value b)))
	    (let ((v1 (abstract-eval1 (application-callee e)
				      (restrict-environment
				       vs (application-callee-indices e))))
		  (v2 (abstract-eval1 (application-argument e)
				      (restrict-environment
				       vs
				       (application-argument-indices e)))))
	     ;; widening case B
	     (all-subwidener-instances!
	      (abstract-apply v1 v2) (environment-binding-value b))
	     (cond ((union? v1)
		    (for-each (lambda (u1)
			       ;; needs work: To handle the case where
			       ;;             if-procedure is a member of the
			       ;;             union v1.
			       ;; widening case I
			       (all-subwidener-instances!
				(abstract-apply u1 v2) (abstract-apply v1 v2)))
			      (get-union-values v1)))
		   ((and (primitive-procedure? v1)
			 (eq? (primitive-procedure-symbol v1) 'if-procedure))
		    (if-widener-instances! v2))))))
       ((letrec-expression? e)
	;; widening case C
	(all-subwidener-instances!
	 ;; bar
	 (abstract-eval1
	  (letrec-expression-body e) (letrec-nested-environment vs e))
	 (environment-binding-value b)))
       ((cons-expression? e)
	;; widening case D
	(all-subwidener-instances!
	 (tagged-vlad-cons
	  (cons-expression-tags e)
	  (abstract-eval1
	   (cons-expression-car e)
	   (restrict-environment vs (cons-expression-car-indices e)))
	  (abstract-eval1
	   (cons-expression-cdr e)
	   (restrict-environment vs (cons-expression-cdr-indices e))))
	 (environment-binding-value b)))
       (else (internal-error)))))
    (environment-bindings e)))
  *expressions*))

(define (all-nested-abstract-values)
 ;; needs work: to make imperative
 (map-reduce
  union-abstract-values
  '()
  (lambda (v) (all-unary-abstract-subvalues (lambda (v) #t) v))
  ;; Adding in the empty abstract value, abstract real, and abstract boolean
  ;; is a conservative overapproximation for now.
  (union-abstract-values
   (list (empty-abstract-value)
	 (abstract-real)
	 (abstract-boolean))
   (union-abstract-values
    (map-reduce union-abstract-values
		'()
		(lambda (e)
		 (map-reduce union-abstract-values
			     '()
			     (lambda (b) (list (environment-binding-value b)))
			     (environment-bindings e)))
		*expressions*)
    (union-abstract-values
     (map-reduce
      union-abstract-values
      '()
      (lambda (b)
       (let ((f (primitive-procedure-abstract (value-binding-value b))))
	(map-reduce union-abstract-values
		    '()
		    (lambda (instance)
		     (union-abstract-values
		      (list (primitive-procedure-instance-v instance))
		      (list (f (primitive-procedure-instance-v instance)))))
		    (primitive-procedure-instances (value-binding-value b)))))
      *value-bindings*)
     (union-abstract-values
      (union-abstract-values
       (union-abstract-values
	(map-reduce union-abstract-values
		    '()
		    (lambda (instance) (list (function-instance-v1 instance)))
		    *function-instances*)
	(map-reduce union-abstract-values
		    '()
		    (lambda (instance) (list (function-instance-v2 instance)))
		    *function-instances*))
       (map-reduce union-abstract-values
		   '()
		   (lambda (instance) (list (instance-return-value instance)))
		   *function-instances*))
      (union-abstract-values
       (map-reduce union-abstract-values
		   '()
		   (lambda (instance) (list (widener-instance-v1 instance)))
		   *widener-instances*)
       (map-reduce union-abstract-values
		   '()
		   (lambda (instance) (list (instance-return-value instance)))
		   *widener-instances*))))))))

(define (cyclic? vertex=? vertex-flag? set-vertex-flag?! before vertices)
 (let loop ((vertices vertices)
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
  (cond
   ((null? vertices) #f)
   (else
    ;; Mark all vertices as #f.
    (for-each (lambda (vertex) (set-vertex-flag?! vertex #f)) vertices)
    ;; Mark all vertices with in-edges as #t.
    (for-each (lambda (edge) (set-vertex-flag?! (second edge) #t)) edges)
    ;; vertices-prime is the set of vertices in vertices with no in-edges.
    (let ((vertices-prime (remove-if vertex-flag? vertices)))
     (if (null? vertices-prime)
	 ;; Each time through the loop the graph only contains edges that
	 ;; both enter and leave vertices in l.
	 #t
	 (loop (begin
		;; Mark all vertices as #f.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #f))
			  vertices)
		;; Mark all vertices-prime as #t.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			  vertices-prime)
		;; Remove vertices-prime from vertices.
		(remove-if vertex-flag? vertices))
	       ;; We are removing vertices-prime from vertices so remove all
	       ;; edges leaving vertices-prime. Since vertices-prime=
	       ;; (set-differenceq vertices (map second edges)) there can be
	       ;; no edges entering vertices-prime.
	       (begin
		;; Mark all edge in-vertices as #f.
		(for-each (lambda (edge) (set-vertex-flag?! (first edge) #f))
			  edges)
		;; Mark all vertices-prime as #t.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			  vertices-prime)
		(remove-if (lambda (edge) (vertex-flag? (first edge)))
			   edges)))))))))

(define (topological-sort-vertices
	 vertex=? vertex-flag? set-vertex-flag?! before vertices)
 (let loop ((vertices vertices)
	    (vertices1 '())
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
  (cond
   ((null? vertices) (reverse vertices1))
   (else
    ;; Mark all vertices as #f.
    (for-each (lambda (vertex) (set-vertex-flag?! vertex #f)) vertices)
    ;; Mark all vertices with in-edges as #t.
    (for-each (lambda (edge) (set-vertex-flag?! (second edge) #t)) edges)
    ;; vertices-prime is the set of vertices in vertices with no in-edges.
    (let ((vertices-prime (remove-if vertex-flag? vertices)))
     (if (null? vertices-prime)
	 ;; Each time through the loop the graph only contains edges that
	 ;; both enter and leave vertices in l.
	 (internal-error)
	 (loop (begin
		;; Mark all vertices as #f.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #f))
			  vertices)
		;; Mark all vertices-prime as #t.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			  vertices-prime)
		;; Remove vertices-prime from vertices.
		(remove-if vertex-flag? vertices))
	       (append vertices-prime vertices1)
	       ;; We are removing vertices-prime from vertices so remove all
	       ;; edges leaving vertices-prime. Since vertices-prime=
	       ;; (set-differenceq vertices (map second edges)) there can be
	       ;; no edges entering vertices-prime.
	       (begin
		;; Mark all edge in-vertices as #f.
		(for-each (lambda (edge) (set-vertex-flag?! (first edge) #f))
			  edges)
		;; Mark all vertices-prime as #t.
		(for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			  vertices-prime)
		(remove-if (lambda (edge) (vertex-flag? (first edge)))
			   edges)))))))))

(define (put-back-vertices
	 vertex=? p! vertex-flag? set-vertex-flag?! before vertices1 vertices2)
 (let loop ((vertices1 vertices1)
	    (vertices2 '())
	    (vertices3 vertices2))
  (cond
   ((null? vertices3)
    (let ((vertices1
	   (topological-sort-vertices
	    vertex=? vertex-flag? set-vertex-flag?! before vertices1)))
     (for-each (lambda (vertex) (p! vertex #t)) vertices1)
     (for-each (lambda (vertex) (p! vertex #f)) vertices2)
     (append vertices1 vertices2)))
   ((cyclic? vertex=?
	     vertex-flag?
	     set-vertex-flag?!
	     before
	     (cons (first vertices3) vertices1))
    (loop vertices1 (cons (first vertices3) vertices2) (rest vertices3)))
   (else
    (loop (cons (first vertices3) vertices1) vertices2 (rest vertices3))))))

(define (feedback-topological-sort
	 vertex=? p! vertex-flag? set-vertex-flag?! before choose vertices)
 ;; Minimal feedback set is the problem of computing the smallest set of edges
 ;; to remove from a digraph to make it acyclic. It is NP complete. This solves
 ;; a related problem of finding a minimal set of vertices to remove from a
 ;; digraph to make it acyclic. I don't know if this problem is NP hard. This
 ;; is a greedy heuristic for solving this problem. It partitions vertices into
 ;; two sets, vertices1 and vertices2, where vertices2 is the set of removed
 ;; vertices and vertices1 is topologically sorted. (before vertex) returns the
 ;; vertices that must come before vertex.
 (let ((edges (profile
	       "~a feedback-topological-sort 1~%"
	       (lambda ()
		(map-reduce
		 append
		 '()
		 (lambda (vertex2)
		  (map (lambda (vertex1) (list vertex1 vertex2))
		       (remove-if-not
			(lambda (vertex1) (memp vertex=? vertex1 vertices))
			(before vertex2))))
		 vertices)))))
  (profile
   "~a feedback-topological-sort 2~%"
   (lambda ()
    (let loop ((vertices vertices)
	       (vertices1 '())
	       (vertices2 '())
	       ;; edges is a list of pairs (vertex1 vertex2) where vertex1 must
	       ;; come before vertex2.
	       (edges edges))
     ;; Each time through the loop the graph only contains edges that both
     ;; enter and leave vertices in vertices.
     (cond
      ((null? vertices)
       (put-back-vertices
	vertex=? p! vertex-flag? set-vertex-flag?! before vertices1 vertices2))
      (else
       ;; Mark all vertices as #f.
       (for-each (lambda (vertex) (set-vertex-flag?! vertex #f)) vertices)
       ;; Mark all vertices with in-edges as #t.
       (for-each (lambda (edge) (set-vertex-flag?! (second edge) #t)) edges)
       ;; vertices-prime is the set of vertices in vertices with no in-edges.
       (let ((vertices-prime (remove-if vertex-flag? vertices)))
	(if (null? vertices-prime)
	    ;; Each time through the loop the graph only contains edges that
	    ;; both enter and leave vertices in l.
	    (let ((vertex
		   (let loop ((vertices vertices) (edges edges))
		    ;; Mark all vertices as #f.
		    (for-each (lambda (vertex) (set-vertex-flag?! vertex #f))
			      vertices)
		    ;; Mark all vertices with out-edges as #t.
		    (for-each
		     (lambda (edge) (set-vertex-flag?! (first edge) #t))
		     edges)
		    ;; vertices-prime is the set of vertices in vertices with
		    ;; out-edges.
		    (let ((vertices-prime
			   (remove-if-not vertex-flag? vertices)))
		     (if (= (length vertices) (length vertices-prime))
			 (choose vertices)
			 (loop vertices-prime
			       ;; Update the graph to contain only edges that
			       ;; leave vertices in vertices-prime which is
			       ;; the new vertices.
			       (begin
				;; Mark all edge out-vertices as #f.
				(for-each
				 (lambda (edge)
				  (set-vertex-flag?! (second edge) #f))
				 edges)
				;; Mark all vertices-prime as #t.
				(for-each (lambda (vertex)
					   (set-vertex-flag?! vertex #t))
					  vertices-prime)
				(remove-if-not
				 (lambda (edge) (vertex-flag? (second edge)))
				 edges))))))))
	     (loop (removep vertex=? vertex vertices)
		   vertices1
		   (cons vertex vertices2)
		   ;; We are removing vertex from vertices so remove all edges
		   ;; entering or leaving vertex.
		   (remove-if (lambda (edge)
			       (or (vertex=? (first edge) vertex)
				   (vertex=? (second edge) vertex)))
			      edges)))
	    (loop (begin
		   ;; Mark all vertices as #f.
		   (for-each (lambda (vertex) (set-vertex-flag?! vertex #f))
			     vertices)
		   ;; Mark all vertices-prime as #t.
		   (for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			     vertices-prime)
		   ;; Remove vertices-prime from vertices.
		   (remove-if vertex-flag? vertices))
		  (append vertices-prime vertices1)
		  vertices2
		  ;; We are removing vertices-prime from vertices so remove all
		  ;; edges leaving vertices-prime. Since vertices-prime=
		  ;; (set-differenceq vertices (map second edges)) there can be
		  ;; no edges entering vertices-prime.
		  (begin
		   ;; Mark all edge in-vertices as #f.
		   (for-each
		    (lambda (edge) (set-vertex-flag?! (first edge) #f))
		    edges)
		   ;; Mark all vertices-prime as #t.
		   (for-each (lambda (vertex) (set-vertex-flag?! vertex #t))
			     vertices-prime)
		   (remove-if (lambda (edge) (vertex-flag? (first edge)))
			      edges))))))))))))

;;; Intermediate-language primitives

(define (il:c) 'il:c)

(define (il:c? il) (eq? il 'il:c))

(define (il:x) 'il:x)

(define (il:x? il) (eq? il 'il:x))

(define (il:y) 'il:y)

(define (il:y? il) (eq? il 'il:y))

(define (il:z) 'il:z)

(define (il:z? il) (eq? il 'il:z))

(define (il:t)
 (set! *il:t* (+ *il:t* 1))
 (make-il:t *il:t*))

(define (il:a instance index) (make-il:a instance index))

(define (il:r instance index) (make-il:r instance index))

(define (il:empty v) (make-il:empty v))

(define (il:tag u v) (make-il:tag u v))

(define (il:constant number) (make-il:constant number))

(define (il:let v x il1 il2)
 ;; Panics are propagated upward, except through dispatches. Doing so might
 ;; unsoundly remove code that might do I/O, panic, signal an error, or not
 ;; terminate.
 (cond ((il:panic? il1) il1)
       ((il:panic? il2) il2)
       ((void? v) il2)
       (else (make-il:let v x il1 il2))))

(define (il:dispatch v0 v il ils)
 (if (void? v0)
     (il:empty v0)
     (if (and (not (boxed? v)) (il:tag? il))
	 (list-ref ils (c:tag (il:tag-u il) (il:tag-v il)))
	 (make-il:dispatch v0 v il ils))))

(define (il:panic string) (make-il:panic string))

;; needs work: to distinguish between nonrecursive and recursive
(define (il:closure-ref v il x)
 (let ((v0 (closure-ref v x)))
  (if (void? v0) (il:empty v0) (make-il:closure-ref v il x))))

(define (il:perturbation-tagged-value-primal v il)
 (let ((v0 (get-perturbation-tagged-value-primal v)))
  (if (void? v0)
      (il:empty v0)
      (make-il:perturbation-tagged-value-primal v il))))

(define (il:bundle-primal v il)
 (let ((v0 (get-bundle-primal v)))
  (if (void? v0) (il:empty v0) (make-il:bundle-primal v il))))

(define (il:bundle-tangent v il)
 (let ((v0 (get-bundle-tangent v)))
  (if (void? v0) (il:empty v0) (make-il:bundle-tangent v il))))

(define (il:sensitivity-tagged-value-primal v il)
 (let ((v0 (get-sensitivity-tagged-value-primal v)))
  (if (void? v0)
      (il:empty v0)
      (make-il:sensitivity-tagged-value-primal v il))))

(define (il:reverse-tagged-value-primal v il)
 (let ((v0 (get-reverse-tagged-value-primal v)))
  (if (void? v0)
      (il:empty v0)
      (make-il:reverse-tagged-value-primal v il))))

(define (il:car v il)
 (let ((v0 (vlad-car v))) (if (void? v0) (il:empty v0) (make-il:car v il))))

(define (il:cdr v il)
 (let ((v0 (vlad-cdr v))) (if (void? v0) (il:empty v0) (make-il:cdr v il))))

(define (il:union-ref v u il)
 (if (void? u) (il:empty u) (make-il:union-ref v u il)))

(define (il:construct* v ils)
 (assert (= (length (aggregate-value-values v)) (length ils)))
 (if (void? v)
     (il:empty v)
     (make-il:construct*
      v
      (removeq #f
	       (map (lambda (v il) (if (void? v) #f il))
		    (aggregate-value-values v)
		    ils)))))

(define (il:construct-union u v il)
 (if (void? v)
     (il:empty v)
     (if (void? u)
	 (make-il:construct-union0 u v)
	 (make-il:construct-union u v il))))

;; needs work: to distinguish between calls to instances and to strings
(define (il:call* instance ils)
 (assert (= (length (instance-argument-values instance)) (length ils)))
 (if (void? (instance-return-value instance))
     (il:empty (instance-return-value instance))
     (make-il:call*
      instance
      (cond
       ((string? instance) ils)
       ((function-instance? instance)
	(if (void? (function-instance-v1 instance))
	    (if (void? (function-instance-v2 instance))
		'()
		(list (second ils)))
	    (if (void? (function-instance-v2 instance))
		(list (first ils))
		(list (first ils) (second ils)))))
       ((widener-instance? instance)
	(if (void? (widener-instance-v1 instance)) '() ils))
       ((primitive-procedure-instance? instance)
	(if (void? (primitive-procedure-instance-v instance)) '() ils))
       (else (internal-error))))))

(define (il:binary il1 string il2) (make-il:binary il1 string il2))

(define (il:binary-boolean il1 string il2)
 (make-il:binary-boolean il1 string il2))

(define (il:mv-let vs xs il1 il2)
 ;; Panics are propagated upward, except through dispatches. Doing so might
 ;; unsoundly remove code that might do I/O, panic, signal an error, or not
 ;; terminate.
 (cond ((il:panic? il1) il1)
       ((il:panic? il2) il2)
       (else (make-il:mv-let vs xs il1 il2))))

(define (il:values* v ils) (make-il:values* v ils))

;;; Derived intermediate-language constructs

(define (il:generate-slots v)
 (cond
  ((nonrecursive-closure? v)
   (map (lambda (x) (lambda (v il) (il:closure-ref v il x)))
	(nonrecursive-closure-variables v)))
  ((recursive-closure? v)
   (map (lambda (x) (lambda (v il) (il:closure-ref v il x)))
	(recursive-closure-variables v)))
  ((perturbation-tagged-value? v) (list il:perturbation-tagged-value-primal))
  ((bundle? v) (list il:bundle-primal il:bundle-tangent))
  ((sensitivity-tagged-value? v) (list il:sensitivity-tagged-value-primal))
  ((reverse-tagged-value? v) (list il:reverse-tagged-value-primal))
  ((vlad-pair? v) (list il:car il:cdr))
  (else (internal-error))))

(define (il:widen v1 v2 il)
 (if (abstract-value=? v1 v2) il (il:call (lookup-widener-instance v1 v2) il)))

(define (il:generate-members v)
 (map (lambda (u) (lambda (v il) (il:union-ref v u il)))
      (get-union-values v)))

(define (il:map-dispatch v il g f)
 (il:dispatch
  (g v)
  v
  il
  ;; widening case H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14,
  ;;               H16, H17, I, L1, L2, L3, M
  (map (lambda (il:member u) (il:widen (g u) (g v) (f (il:member v il) u)))
       (il:generate-members v)
       (get-union-values v))))

(define (il:construct v . ils) (il:construct* v ils))

(define (il:call instance . ils) (il:call* instance ils))

(define (il:unary-boolean string)
 (lambda (il) (il:binary-boolean il string (il:constant 0))))

(define (il:values v . ils) (il:values* v ils))

(define (il:tagged-construct-nonrecursive-closure tags vs e ils)
 (if (empty-tags? tags)
     (il:construct (new-nonrecursive-closure vs e) ils)
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance 'perturb
			 (tagged-new-nonrecursive-closure
			  (remove-tag 'perturbation tags)
			  (map unperturb vs)
			  (perturbation-transform-inverse e)))
	(il:tagged-construct-nonrecursive-closure
	 (remove-tag 'perturbation tags)
	 (map unperturb vs)
	 (perturbation-transform-inverse e)
	 (map (lambda (v il) (il:call (lookup-instance 'unperturb v) il))
	      vs
	      ils))))
      ((forward)
       (il:call
	(lookup-instance 'bundle
			 (vlad-cons (tagged-new-nonrecursive-closure
				     (remove-tag 'forward tags)
				     (map primal vs)
				     (forward-transform-inverse e))
				    (perturb (tagged-new-nonrecursive-closure
					      (remove-tag 'forward tags)
					      (map unperturb (map tangent vs))
					      (forward-transform-inverse e)))))
	(il:construct
	 (vlad-cons (tagged-new-nonrecursive-closure
		     (remove-tag 'forward tags)
		     (map primal vs)
		     (forward-transform-inverse e))
		    (perturb (tagged-new-nonrecursive-closure
			      (remove-tag 'forward tags)
			      (map unperturb (map tangent vs))
			      (forward-transform-inverse e))))
	 (il:tagged-construct-nonrecursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (forward-transform-inverse e)
	  (map (lambda (v il) (il:call (lookup-instance 'primal v) il))
	       vs
	       ils))
	 (il:call (lookup-instance 'perturb
				   (tagged-new-nonrecursive-closure
				    (remove-tag 'forward tags)
				    (map unperturb (map tangent vs))
				    (forward-transform-inverse e)))
		  (il:tagged-construct-nonrecursive-closure
		   (remove-tag 'forward tags)
		   (map unperturb (map tangent vs))
		   (forward-transform-inverse e)
		   (map (lambda (v il)
			 (il:call (lookup-instance 'unperturb (tangent v))
				  (il:call (lookup-instance 'tangent v) il)))
			vs
			ils))))))
      ((sensitivity)
       (il:call
	(lookup-instance 'sensitize
			 (tagged-new-nonrecursive-closure
			  (remove-tag 'sensitivity tags)
			  (map unsensitize vs)
			  (sensitivity-transform-inverse e)))
	(il:tagged-construct-nonrecursive-closure
	 (remove-tag 'sensitivity tags)
	 (map unsensitize vs)
	 (sensitivity-transform-inverse e)
	 (map (lambda (v il) (il:call (lookup-instance 'unsensitize v) il))
	      vs
	      ils))))
      ((reverse)
       (il:call
	(lookup-instance '*j
			 (tagged-new-nonrecursive-closure
			  (remove-tag 'reverse tags)
			  (map *j-inverse vs)
			  (reverse-transform-inverse e)))
	(il:tagged-construct-nonrecursive-closure
	 (remove-tag 'reverse tags)
	 (map *j-inverse vs)
	 (reverse-transform-inverse e)
	 (map (lambda (v il) (il:call (lookup-instance '*j-inverse v) il))
	      vs
	      ils))))
      (else (internal-error)))))

(define (il:tagged-construct-recursive-closure tags vs xs es i ils)
 (if (empty-tags? tags)
     (il:construct (new-recursive-closure vs xs es i) ils)
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance 'perturb
			 (tagged-new-recursive-closure
			  (remove-tag 'perturbation tags)
			  (map unperturb vs)
			  (map-vector unperturbationify xs)
			  (map-vector perturbation-transform-inverse es)
			  i))
	(il:tagged-construct-recursive-closure
	 (remove-tag 'perturbation tags)
	 (map unperturb vs)
	 (map-vector unperturbationify xs)
	 (map-vector perturbation-transform-inverse es)
	 i
	 (map (lambda (v il) (il:call (lookup-instance 'unperturb v) il))
	      vs
	      ils))))
      ((forward)
       (il:call
	(lookup-instance
	 'bundle
	 (vlad-cons (tagged-new-recursive-closure
		     (remove-tag 'forward tags)
		     (map primal vs)
		     (map-vector unforwardify xs)
		     (map-vector forward-transform-inverse es)
		     i)
		    (perturb (tagged-new-recursive-closure
			      (remove-tag 'forward tags)
			      (map unperturb (map tangent vs))
			      (map-vector unforwardify xs)
			      (map-vector forward-transform-inverse es)
			      i))))
	(il:construct
	 (vlad-cons (tagged-new-recursive-closure
		     (remove-tag 'forward tags)
		     (map primal vs)
		     (map-vector unforwardify xs)
		     (map-vector forward-transform-inverse es)
		     i)
		    (perturb (tagged-new-recursive-closure
			      (remove-tag 'forward tags)
			      (map unperturb (map tangent vs))
			      (map-vector unforwardify xs)
			      (map-vector forward-transform-inverse es)
			      i)))
	 (il:tagged-construct-recursive-closure
	  (remove-tag 'forward tags)
	  (map primal vs)
	  (map-vector unforwardify xs)
	  (map-vector forward-transform-inverse es)
	  i
	  (map (lambda (v il) (il:call (lookup-instance 'primal v) il))
	       vs
	       ils))
	 (il:call (lookup-instance 'perturb
				   (tagged-new-recursive-closure
				    (remove-tag 'forward tags)
				    (map unperturb (map tangent vs))
				    (map-vector unforwardify xs)
				    (map-vector forward-transform-inverse es)
				    i))
		  (il:tagged-construct-recursive-closure
		   (remove-tag 'forward tags)
		   (map unperturb (map tangent vs))
		   (map-vector unforwardify xs)
		   (map-vector forward-transform-inverse es)
		   i
		   (map (lambda (v il)
			 (il:call (lookup-instance 'unperturb (tangent v))
				  (il:call (lookup-instance 'tangent v) il)))
			vs
			ils))))))
      ((sensitivity)
       (il:call
	(lookup-instance 'sensitize
			 (tagged-new-recursive-closure
			  (remove-tag 'sensitivity tags)
			  (map unsensitize vs)
			  (map-vector unsensitivityify xs)
			  (map-vector sensitivity-transform-inverse es)
			  i))
	(il:tagged-construct-recursive-closure
	 (remove-tag 'sensitivity tags)
	 (map unsensitize vs)
	 (map-vector unsensitivityify xs)
	 (map-vector sensitivity-transform-inverse es)
	 i
	 (map (lambda (v il) (il:call (lookup-instance 'unsensitize v) il))
	      vs
	      ils))))
      ((reverse)
       (il:call
	(lookup-instance '*j
			 (tagged-new-recursive-closure
			  (remove-tag 'reverse tags)
			  (map *j-inverse vs)
			  (map-vector unreverseify xs)
			  (map-vector reverse-transform-inverse es)
			  i))
	(il:tagged-construct-recursive-closure
	 (remove-tag 'reverse tags)
	 (map *j-inverse vs)
	 (map-vector unreverseify xs)
	 (map-vector reverse-transform-inverse es)
	 i
	 (map (lambda (v il) (il:call (lookup-instance '*j-inverse v) il))
	      vs
	      ils))))
      (else (internal-error)))))

(define (il:tagged-closure-ref tags v il x)
 (if (empty-tags? tags)
     (cond
      ((empty-abstract-value? v)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v)
       (il:let v
	       (il:y)
	       il
	       ;; widening case M3
	       (il:map-dispatch
		v
		(il:y)
		(lambda (u)
		 (map-union
		  (lambda (u)
		   (if (closure? u) (closure-ref u x) (empty-abstract-value)))
		  u))
		(lambda (il u)
		 (if (closure? u)
		     (il:closure-ref u il x)
		     (il:panic "Argument is not a closure"))))))
      ((closure? v) (il:closure-ref v il x))
      (else (il:panic "Argument is not a closure")))
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance
	 'perturb
	 (tagged-closure-ref (remove-tag 'perturbation tags)
			     (unperturb v)
			     (unperturbationify x)))
	(il:tagged-closure-ref (remove-tag 'perturbation tags)
			       (unperturb v)
			       (il:call (lookup-instance 'unperturb v) il)
			       (unperturbationify x))))
      ((forward)
       (il:call
	(lookup-instance
	 'bundle
	 (vlad-cons (tagged-closure-ref (remove-tag 'forward tags)
					(primal v)
					(unforwardify x))
		    (perturb (tagged-closure-ref (remove-tag 'forward tags)
						 (unperturb (tangent v))
						 (unforwardify x)))))
	(il:construct
	 (vlad-cons (tagged-closure-ref (remove-tag 'forward tags)
					(primal v)
					(unforwardify x))
		    (perturb (tagged-closure-ref (remove-tag 'forward tags)
						 (unperturb (tangent v))
						 (unforwardify x))))
	 (il:tagged-closure-ref (remove-tag 'forward tags)
				(primal v)
				(il:call (lookup-instance 'primal v) il)
				(unforwardify x))
	 (il:call
	  (lookup-instance 'perturb
			   (tagged-closure-ref (remove-tag 'forward tags)
					       (unperturb (tangent v))
					       (unforwardify x)))
	  (il:tagged-closure-ref
	   (remove-tag 'forward tags)
	   (unperturb (tangent v))
	   (il:call (lookup-instance 'unperturb (tangent v))
		    (il:call (lookup-instance 'tangent v) il))
	   (unforwardify x))))))
      ((sensitivity)
       (il:call
	(lookup-instance
	 'sensitize
	 (tagged-closure-ref (remove-tag 'sensitivity tags)
			     (unsensitize v)
			     (unsensitivityify x)))
	(il:tagged-closure-ref (remove-tag 'sensitivity tags)
			       (unsensitize v)
			       (il:call (lookup-instance 'unsensitize v) il)
			       (unsensitivityify x))))
      ((reverse)
       (il:call
	(lookup-instance
	 '*j
	 (tagged-closure-ref (remove-tag 'reverse tags)
			     (*j-inverse v)
			     (unreverseify x)))
	(il:tagged-closure-ref (remove-tag 'reverse tags)
			       (*j-inverse v)
			       (il:call (lookup-instance '*j-inverse v) il)
			       (unreverseify x))))
      (else (internal-error)))))

(define (il:tagged-cons tags v1 v2 il1 il2)
 (if (empty-tags? tags)
     (il:construct (vlad-cons v1 v2) il1 il2)
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance 'perturb
			 (tagged-vlad-cons (remove-tag 'perturbation tags)
					   (unperturb v1)
					   (unperturb v2)))
	(il:tagged-cons (remove-tag 'perturbation tags)
			(unperturb v1)
			(unperturb v2)
			(il:call (lookup-instance 'unperturb v1) il1)
			(il:call (lookup-instance 'unperturb v2) il2))))
      ((forward)
       (il:call
	(lookup-instance
	 'bundle
	 (vlad-cons (tagged-vlad-cons (remove-tag 'forward tags)
				      (primal v1)
				      (primal v2))
		    (perturb (tagged-vlad-cons (remove-tag 'forward tags)
					       (unperturb (tangent v1))
					       (unperturb (tangent v2))))))
	(il:construct
	 (vlad-cons (tagged-vlad-cons (remove-tag 'forward tags)
				      (primal v1)
				      (primal v2))
		    (perturb (tagged-vlad-cons (remove-tag 'forward tags)
					       (unperturb (tangent v1))
					       (unperturb (tangent v2)))))
	 (il:tagged-cons (remove-tag 'forward tags)
			 (primal v1)
			 (primal v2)
			 (il:call (lookup-instance 'primal v1) il1)
			 (il:call (lookup-instance 'primal v2) il2))
	 (il:call (lookup-instance 'perturb
				   (tagged-vlad-cons (remove-tag 'forward tags)
						     (unperturb (tangent v1))
						     (unperturb (tangent v2))))
		  (il:tagged-cons
		   (remove-tag 'forward tags)
		   (unperturb (tangent v1))
		   (unperturb (tangent v2))
		   (il:call (lookup-instance 'unperturb (tangent v1))
			    (il:call (lookup-instance 'tangent v1) il1))
		   (il:call (lookup-instance 'unperturb (tangent v2))
			    (il:call (lookup-instance 'tangent v2) il2)))))))
      ((sensitivity)
       (il:call
	(lookup-instance 'sensitize
			 (tagged-vlad-cons (remove-tag 'sensitivity tags)
					   (unsensitize v1)
					   (unsensitize v2)))
	(il:tagged-cons (remove-tag 'sensitivity tags)
			(unsensitize v1)
			(unsensitize v2)
			(il:call (lookup-instance 'unsensitize v1) il1)
			(il:call (lookup-instance 'unsensitize v2) il2))))
      ((reverse)
       (il:call
	(lookup-instance '*j
			 (tagged-vlad-cons (remove-tag 'reverse tags)
					   (*j-inverse v1)
					   (*j-inverse v2)))
	(il:tagged-cons (remove-tag 'reverse tags)
			(*j-inverse v1)
			(*j-inverse v2)
			(il:call (lookup-instance '*j-inverse v1) il1)
			(il:call (lookup-instance '*j-inverse v2) il2))))
      (else (internal-error)))))

(define (il:tagged-car tags v il)
 (if (empty-tags? tags)
     (cond
      ((empty-abstract-value? v)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v)
       (il:let
	v
	(il:y)
	il
	;; widening case M1
	(il:map-dispatch
	 v
	 (il:y)
	 (lambda (u)
	  (map-union
	   (lambda (u) (if (vlad-pair? u) (vlad-car u) (empty-abstract-value)))
	   u))
	 (lambda (il u)
	  (if (vlad-pair? u)
	      (il:car u il)
	      (il:panic "Argument is not a pair"))))))
      ((vlad-pair? v) (il:car v il))
      (else (il:panic "Argument is not a pair")))
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance
	 'perturb
	 (tagged-vlad-car (remove-tag 'perturbation tags) (unperturb v)))
	(il:tagged-car (remove-tag 'perturbation tags)
		       (unperturb v)
		       (il:call (lookup-instance 'unperturb v) il))))
      ((forward)
       (il:call
	(lookup-instance
	 'bundle
	 (vlad-cons (tagged-vlad-car (remove-tag 'forward tags) (primal v))
		    (perturb (tagged-vlad-car (remove-tag 'forward tags)
					      (unperturb (tangent v))))))
	(il:construct
	 (vlad-cons (tagged-vlad-car (remove-tag 'forward tags) (primal v))
		    (perturb (tagged-vlad-car (remove-tag 'forward tags)
					      (unperturb (tangent v)))))
	 (il:tagged-car (remove-tag 'forward tags)
			(primal v)
			(il:call (lookup-instance 'primal v) il))
	 (il:call (lookup-instance 'perturb
				   (tagged-vlad-car (remove-tag 'forward tags)
						    (unperturb (tangent v))))
		  (il:tagged-car
		   (remove-tag 'forward tags)
		   (unperturb (tangent v))
		   (il:call (lookup-instance 'unperturb (tangent v))
			    (il:call (lookup-instance 'tangent v) il)))))))
      ((sensitivity)
       (il:call
	(lookup-instance
	 'sensitize
	 (tagged-vlad-car (remove-tag 'sensitivity tags) (unsensitize v)))
	(il:tagged-car (remove-tag 'sensitivity tags)
		       (unsensitize v)
		       (il:call (lookup-instance 'unsensitize v) il))))
      ((reverse)
       (il:call
	(lookup-instance
	 '*j (tagged-vlad-car (remove-tag 'reverse tags) (*j-inverse v)))
	(il:tagged-car (remove-tag 'reverse tags)
		       (*j-inverse v)
		       (il:call (lookup-instance '*j-inverse v) il))))
      (else (internal-error)))))

(define (il:tagged-cdr tags v il)
 (if (empty-tags? tags)
     (cond
      ((empty-abstract-value? v)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v)
       (il:let
	v
	(il:y)
	il
	;; widening case M2
	(il:map-dispatch
	 v
	 (il:y)
	 (lambda (u)
	  (map-union
	   (lambda (u) (if (vlad-pair? u) (vlad-cdr u) (empty-abstract-value)))
	   u))
	 (lambda (il u)
	  (if (vlad-pair? u)
	      (il:cdr u il)
	      (il:panic "Argument is not a pair"))))))
      ((vlad-pair? v) (il:cdr v il))
      (else (il:panic "Argument is not a pair")))
     (case (first tags)
      ((perturbation)
       (il:call
	(lookup-instance
	 'perturb
	 (tagged-vlad-cdr (remove-tag 'perturbation tags) (unperturb v)))
	(il:tagged-cdr (remove-tag 'perturbation tags)
		       (unperturb v)
		       (il:call (lookup-instance 'unperturb v) il))))
      ((forward)
       (il:call
	(lookup-instance
	 'bundle
	 (vlad-cons (tagged-vlad-cdr (remove-tag 'forward tags) (primal v))
		    (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
					      (unperturb (tangent v))))))
	(il:construct
	 (vlad-cons (tagged-vlad-cdr (remove-tag 'forward tags) (primal v))
		    (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
					      (unperturb (tangent v)))))
	 (il:tagged-cdr (remove-tag 'forward tags)
			(primal v)
			(il:call (lookup-instance 'primal v) il))
	 (il:call (lookup-instance 'perturb
				   (tagged-vlad-cdr (remove-tag 'forward tags)
						    (unperturb (tangent v))))
		  (il:tagged-cdr
		   (remove-tag 'forward tags)
		   (unperturb (tangent v))
		   (il:call (lookup-instance 'unperturb (tangent v))
			    (il:call (lookup-instance 'tangent v) il)))))))
      ((sensitivity)
       (il:call
	(lookup-instance
	 'sensitize
	 (tagged-vlad-cdr (remove-tag 'sensitivity tags) (unsensitize v)))
	(il:tagged-cdr (remove-tag 'sensitivity tags)
		       (unsensitize v)
		       (il:call (lookup-instance 'unsensitize v) il))))
      ((reverse)
       (il:call
	(lookup-instance
	 '*j (tagged-vlad-cdr (remove-tag 'reverse tags) (*j-inverse v)))
	(il:tagged-cdr (remove-tag 'reverse tags)
		       (*j-inverse v)
		       (il:call (lookup-instance '*j-inverse v) il))))
      (else (internal-error)))))

;;; Expression generators

(define (generate-destructure p v il k1 k2)
 (letrec ((abstract-outer
	   (lambda (p v v-alist k1)
	    (cond
	     ;; This case comes first to avoid the dispatch.
	     ((variable-access-expression? p)
	      (k1 (cons (cons (variable-access-expression-variable p) v)
			v-alist)))
	     ((union? v)
	      ;; widening case J
	      (map-union (lambda (u) (abstract-outer p u v-alist k1)) v))
	     ((constant-expression? p)
	      ;; needs work: See the note in destructure-outer.
	      ;; widening case A
	      (if (abstract-value-nondisjoint?
		   (concrete-value->abstract-value
		    (constant-expression-value p)) v)
		  (k1 v-alist)
		  (empty-abstract-value)))
	     ((lambda-expression? p)
	      (if (and (nonrecursive-closure? v)
		       (dereferenced-expression-eqv?
			p (nonrecursive-closure-lambda-expression v)))
		  (let abstract-inner ((xs1 (parameter-variables p))
				       (xs2 (nonrecursive-closure-variables v))
				       (vs (get-nonrecursive-closure-values v))
				       (v-alist v-alist)
				       (k1 k1))
		   (if (null? xs1)
		       (k1 v-alist)
		       (abstract-outer
			(allocate-variable-access-expression (first xs1))
			(first vs)
			v-alist
			(lambda (v-alist)
			 (abstract-inner
			  (rest xs1) (rest xs2) (rest vs) v-alist k1)))))
		  (empty-abstract-value)))
	     ((letrec-expression? p)
	      (assert
	       (and (variable-access-expression? (letrec-expression-body p))
		    (memp variable=?
			  (variable-access-expression-variable
			   (letrec-expression-body p))
			  (letrec-expression-procedure-variables p))))
	      (if (and (recursive-closure? v)
		       (= (recursive-closure-index v)
			  (positionp
			   variable=?
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
		  (let abstract-inner ((xs1 (parameter-variables p))
				       (xs2 (recursive-closure-variables v))
				       (vs (get-recursive-closure-values v))
				       (v-alist v-alist)
				       (k1 k1))
		   (if (null? xs1)
		       (k1 v-alist)
		       (abstract-outer
			(allocate-variable-access-expression (first xs1))
			(first vs)
			v-alist
			(lambda (v-alist)
			 (abstract-inner
			  (rest xs1) (rest xs2) (rest vs) v-alist k1)))))
		  (empty-abstract-value)))
	     ((cons-expression? p)
	      (abstract-outer
	       (cons-expression-car p)
	       (tagged-vlad-car (cons-expression-tags p) v)
	       v-alist
	       (lambda (v-alist)
		(abstract-outer (cons-expression-cdr p)
				(tagged-vlad-cdr (cons-expression-tags p) v)
				v-alist
				k1))))
	     (else (internal-error)))))
	  (generate-outer
	   (lambda (p v il v-alist k1 k2)
	    (cond
	     ;; This case comes first to avoid the dispatch.
	     ((variable-access-expression? p)
	      (il:let
	       v
	       (variable-access-expression-variable p)
	       il
	       (k2 (cons (cons (variable-access-expression-variable p) v)
			 v-alist))))
	     ((union? v)
	      ;; widening case J
	      (let ((v2 (map-union
			 (lambda (u) (abstract-outer p u v-alist k1)) v)))
	       (il:dispatch
		v2
		v
		il
		(map (lambda (il:member1 u1)
		      ;; widening case J
		      (il:widen (abstract-outer p u1 v-alist k1)
				v2
				(generate-outer
				 p u1 (il:member1 v il) v-alist k1 k2)))
		     (il:generate-members v)
		     (get-union-values v)))))
	     ((constant-expression? p)
	      ;; needs work: To generate run-time equivalence check when the
	      ;;             constant expression parameter and/or argument
	      ;;             contain abstract booleans or abstract reals. When
	      ;;             we do so, we need to call il:widen appropriately.
	      ;; widening case A
	      (if (abstract-value-nondisjoint?
		   (concrete-value->abstract-value
		    (constant-expression-value p)) v)
		  (k2 v-alist)
		  (il:panic
		   (format #f "Argument is not an equivalent value for ~s"
			   (externalize-expression p)))))
	     ((lambda-expression? p)
	      (if (and (nonrecursive-closure? v)
		       (dereferenced-expression-eqv?
			p (nonrecursive-closure-lambda-expression v)))
		  (letrec ((abstract-inner
			    (lambda (xs1 xs2 vs v-alist k1)
			     (if (null? xs1)
				 (k1 v-alist)
				 (abstract-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))))))
			   (generate-inner
			    (lambda (xs1 xs2 vs v-alist k1 k2)
			     (if (null? xs1)
				 (k2 v-alist)
				 (generate-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  ;; foo
				  (il:closure-ref v il (first xs2))
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))
				  (lambda (v-alist)
				   (generate-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1
						   k2)))))))
		   (generate-inner (parameter-variables p)
				   (nonrecursive-closure-variables v)
				   (get-nonrecursive-closure-values v)
				   v-alist
				   k1
				   k2))
		  (il:panic
		   (format
		    #f "Argument is not a matching nonrecursive closure for ~s"
		    (externalize-expression p)))))
	     ((letrec-expression? p)
	      (assert
	       (and (variable-access-expression? (letrec-expression-body p))
		    (memp variable=?
			  (variable-access-expression-variable
			   (letrec-expression-body p))
			  (letrec-expression-procedure-variables p))))
	      (if (and (recursive-closure? v)
		       (= (recursive-closure-index v)
			  (positionp
			   variable=?
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
		  (letrec ((abstract-inner
			    (lambda (xs1 xs2 vs v-alist k1)
			     (if (null? xs1)
				 (k1 v-alist)
				 (abstract-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))))))
			   (generate-inner
			    (lambda (xs1 xs2 vs v-alist k1 k2)
			     (if (null? xs1)
				 (k2 v-alist)
				 (generate-outer
				  (allocate-variable-access-expression
				   (first xs1))
				  (first vs)
				  ;; foo
				  (il:closure-ref v il (first xs2))
				  v-alist
				  (lambda (v-alist)
				   (abstract-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1))
				  (lambda (v-alist)
				   (generate-inner (rest xs1)
						   (rest xs2)
						   (rest vs)
						   v-alist
						   k1
						   k2)))))))
		   (generate-inner (parameter-variables p)
				   (recursive-closure-variables v)
				   (get-recursive-closure-values v)
				   v-alist
				   k1
				   k2))
		  (il:panic
		   (format
		    #f "Argument is not a matching recursive closure for ~s"
		    (externalize-expression p)))))
	     ((cons-expression? p)
	      (generate-outer
	       (cons-expression-car p)
	       (tagged-vlad-car (cons-expression-tags p) v)
	       (il:tagged-car (cons-expression-tags p) v il)
	       v-alist
	       (lambda (v-alist)
		(abstract-outer (cons-expression-cdr p)
				(tagged-vlad-cdr (cons-expression-tags p) v)
				v-alist
				k1))
	       (lambda (v-alist)
		(generate-outer (cons-expression-cdr p)
				(tagged-vlad-cdr (cons-expression-tags p) v)
				(il:tagged-cdr (cons-expression-tags p) v il)
				v-alist
				k1
				k2))))
	     (else (internal-error))))))
  (generate-outer p v il '() k1 k2)))

(define (generate-reference v0 v1 x xs xs2)
 (cond ((memp variable=? x xs2) (il:c))
       ((memp variable=? x xs)
	;; foo
	(if (void? v1) (il:empty v1) (il:closure-ref v0 (il:c) x)))
       (else x)))

(define (generate-call v1 v2 il1 il2)
 ;; needs work: We don't check the "Argument has wrong type for target"
 ;;             condition.
 (cond ((empty-abstract-value? v2)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v1)
	(il:let
	 v1
	 (il:y)
	 il1
	 ;; widening case I
	 (il:map-dispatch v1
			  (il:y)
			  (lambda (u1) (abstract-apply u1 v2))
			  (lambda (il1 u1) (generate-call u1 v2 il1 il2)))))
       ((primitive-procedure? v1)
	(il:call (lookup-instance (primitive-procedure-symbol v1) v2) il2))
       ((closure? v1) (il:call (lookup-function-instance v1 v2) il1 il2))
       (else (il:panic "Target is not a procedure"))))

(define (generate-expression e vs v0 xs xs2 bs)
 ;; xs is the list of free variables of the environent in which e is evaluated.
 ;; xs2 is the list of procedure variables of the environent in which e is
 ;;     evaluated.
 (cond
  ((empty-abstract-value? (abstract-eval1 e vs))
   (il:panic
    "A run-time error that was detected at compile time has occurred"))
  ((constant-expression? e)
   (assert (void? (constant-expression-value e)))
   ;; widening case E
   (il:widen (constant-expression-value e)
	     (abstract-eval1 e vs)
	     (il:empty (abstract-eval1 e vs))))
  ;; There is no widening case F.
  ((variable-access-expression? e)
   (generate-reference
    v0 (abstract-eval1 e vs) (variable-access-expression-variable e) xs xs2))
  ((lambda-expression? e)
   ;; widening case G
   (il:widen
    (new-nonrecursive-closure vs e)
    (abstract-eval1 e vs)
    ;; foo
    (il:construct* (new-nonrecursive-closure vs e)
		   (map (lambda (x1 v1) (generate-reference v0 v1 x1 xs xs2))
			(free-variables e)
			vs))))
  ((application? e)
   (if (lambda-expression? (application-callee e))
       ;; This handling of LET is an optimization.
       ;; needs work: We don't check the "Argument has wrong type for target"
       ;;             condition.
       (let ((e1 (lambda-expression-body (application-callee e)))
	     (p (lambda-expression-parameter (application-callee e)))
	     (tags1 (lambda-expression-tags (application-callee e)))
	     (v (abstract-eval1
		 (application-argument e)
		 (restrict-environment vs (application-argument-indices e)))))
	(il:let
	 v
	 (il:z)
	 (generate-expression
	  (application-argument e)
	  (restrict-environment vs (application-argument-indices e))
	  v0
	  xs
	  xs2
	  bs)
	 ;; widening case B-prime
	 (il:widen
	  (if (some-value-tags (lambda (tags) (prefix-tags? tags1 tags)) v)
	      (abstract-destructure
	       ;; widening case J
	       map-union
	       (empty-abstract-value)
	       p
	       v
	       (lambda (v-alist)
		;; bar
		(abstract-eval1
		 e1 (construct-environment-for-let e vs v-alist))))
	      (empty-abstract-value))
	  (abstract-eval1 e vs)
	  ;; widening case J
	  (generate-destructure
	   p
	   v
	   (il:z)
	   (lambda (v-alist)
	    ;; bar
	    (abstract-eval1 e1 (construct-environment-for-let e vs v-alist)))
	   (lambda (v-alist)
	    ;; bar
	    (generate-expression
	     e1 (construct-environment-for-let e vs v-alist) v0 xs xs2 bs))))))
       (let ((v1 (abstract-eval1
		  (application-callee e)
		  (restrict-environment vs (application-callee-indices e))))
	     (v2 (abstract-eval1
		  (application-argument e)
		  (restrict-environment vs (application-argument-indices e)))))
	;; widening case B
	(il:widen
	 (abstract-apply v1 v2)
	 (abstract-eval1 e vs)
	 (generate-call
	  v1
	  v2
	  (generate-expression
	   (application-callee e)
	   (restrict-environment vs (application-callee-indices e))
	   v0
	   xs
	   xs2
	   bs)
	  (generate-expression
	   (application-argument e)
	   (restrict-environment vs (application-argument-indices e))
	   v0
	   xs
	   xs2
	   bs))))))
  ((letrec-expression? e)
   ;; widening case C
   ;; bar
   (il:widen (abstract-eval1 (letrec-expression-body e)
			     (letrec-nested-environment vs e))
	     (abstract-eval1 e vs)
	     ;; bar
	     (generate-expression (letrec-expression-body e)
				  (letrec-nested-environment vs e)
				  v0
				  xs
				  xs2
				  bs)))
  ((cons-expression? e)
   (let ((v1 (abstract-eval1
	      (cons-expression-car e)
	      (restrict-environment vs (cons-expression-car-indices e))))
	 (v2 (abstract-eval1
	      (cons-expression-cdr e)
	      (restrict-environment vs (cons-expression-cdr-indices e)))))
    ;; widening case D
    (il:widen
     (tagged-vlad-cons (cons-expression-tags e) v1 v2)
     (abstract-eval1 e vs)
     (il:tagged-cons (cons-expression-tags e)
		     v1
		     v2
		     (generate-expression
		      (cons-expression-car e)
		      (restrict-environment vs (cons-expression-car-indices e))
		      v0
		      xs
		      xs2
		      bs)
		     (generate-expression
		      (cons-expression-cdr e)
		      (restrict-environment vs (cons-expression-cdr-indices e))
		      v0
		      xs
		      xs2
		      bs)))))
  (else (internal-error))))

(define (generate-letrec-bindings e vs v0 xs xs2 il)
 (cond
  ((constant-expression? e) il)
  ((variable-access-expression? e) il)
  ((lambda-expression? e) il)
  ((application? e)
   (generate-letrec-bindings
    (application-callee e)
    (restrict-environment vs (application-callee-indices e))
    v0
    xs
    xs2
    (generate-letrec-bindings
     (application-argument e)
     (restrict-environment vs (application-argument-indices e))
     v0
     xs
     xs2
     il)))
  ((letrec-expression? e)
   (let loop ((xs1 (letrec-expression-procedure-variables e)))
    (if (null? xs1)
	;; bar
	(generate-letrec-bindings (letrec-expression-body e)
				  (letrec-nested-environment vs e)
				  v0
				  xs
				  xs2
				  il)
	;; foo
	(let ((v (new-recursive-closure
		  (restrict-environment vs (letrec-expression-indices e))
		  (list->vector (letrec-expression-procedure-variables e))
		  (list->vector (letrec-expression-lambda-expressions e))
		  (positionp variable=?
			     (first xs1)
			     (letrec-expression-procedure-variables e)))))
	 (il:let
	  v
	  (first xs1)
	  (il:construct*
	   v
	   (map (lambda (x1 v1) (generate-reference v0 v1 x1 xs xs2))
		(letrec-expression-variables e)
		(restrict-environment vs (letrec-expression-indices e))))
	  (loop (rest xs1)))))))
  ((cons-expression? e)
   (generate-letrec-bindings
    (cons-expression-car e)
    (restrict-environment vs (cons-expression-car-indices e))
    v0
    xs
    xs2
    (generate-letrec-bindings
     (cons-expression-cdr e)
     (restrict-environment vs (cons-expression-cdr-indices e))
     v0
     xs
     xs2
     il)))
  (else (internal-error))))

;;; Definition generators

(define (generate-real*real-primitive generate)
 (lambda (instance)
  (let* ((v (primitive-procedure-instance-v instance))
	 (symbol (primitive-procedure-instance-symbol instance))
	 (primitive-procedure (lookup-primitive-procedure symbol))
	 (name (primitive-procedure-name primitive-procedure))
	 (f (primitive-procedure-abstract primitive-procedure)))
   (cond
    ((empty-abstract-value? v)
     (il:panic
      "A run-time error that was detected at compile time has occurred"))
    ((union? v)
     ;; needs work: The widening case is not annotated yet.
     (il:map-dispatch
      v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
    ((vlad-pair? v)
     (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
      (cond
       ((empty-abstract-value? v1)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v1)
	;; needs work: The widening case is not annotated yet.
	(il:map-dispatch
	 v1
	 (il:car v (il:x))
	 (lambda (u1) (f (vlad-cons u1 v2)))
	 (lambda (il1 u1)
	  (il:call (lookup-instance symbol (vlad-cons u1 v2))
		   (il:construct (vlad-cons u1 v2) il1 (il:cdr v (il:x)))))))
       ((empty-abstract-value? v2)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v2)
	;; needs work: The widening case is not annotated yet.
	(il:map-dispatch
	 v2
	 (il:cdr v (il:x))
	 (lambda (u2) (f (vlad-cons v1 u2)))
	 (lambda (il2 u2)
	  (il:call (lookup-instance symbol (vlad-cons v1 u2))
		   (il:construct (vlad-cons v1 u2) (il:car v (il:x)) il2)))))
       ((and (vlad-real? v1) (vlad-real? v2))
	(generate (if (void? v1) (il:constant v1) (il:car v (il:x)))
		  (if (void? v2) (il:constant v2) (il:cdr v (il:x)))))
       (else (il:panic (format #f "Argument to ~a is invalid" name))))))
    (else (il:panic (format #f "Argument to ~a is invalid" name)))))))

(define (generate-real-primitive generate)
 (lambda (instance)
  (let* ((v (primitive-procedure-instance-v instance))
	 (symbol (primitive-procedure-instance-symbol instance))
	 (primitive-procedure (lookup-primitive-procedure symbol))
	 (name (primitive-procedure-name primitive-procedure))
	 (f (primitive-procedure-abstract primitive-procedure)))
   (cond ((empty-abstract-value? v)
	  (il:panic
	   "A run-time error that was detected at compile time has occurred"))
	 ((union? v)
	  ;; needs work: The widening case is not annotated yet.
	  (il:map-dispatch
	   v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
	 ((vlad-real? v) (generate (if (void? v) (il:constant v) (il:x))))
	 (else (il:panic (format #f "Argument to ~a is invalid" name)))))))

(define (generate-type-predicate p?)
 (lambda (instance)
  (let* ((v (primitive-procedure-instance-v instance))
	 (symbol (primitive-procedure-instance-symbol instance))
	 (f (primitive-procedure-abstract
	     (lookup-primitive-procedure symbol))))
   (cond ((empty-abstract-value? v)
	  (il:panic
	   "A run-time error that was detected at compile time has occurred"))
	 ((union? v)
	  ;; needs work: The widening case is not annotated yet.
	  (il:map-dispatch
	   v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
	 ((p? v) (il:empty (abstract-boolean)))
	 (else (il:empty (abstract-boolean)))))))

(define (generate-if2 v1 v2 v3 il1 il2 il3)
 (cond ((empty-abstract-value? v1)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v1)
	;; widening case L1
	(il:map-dispatch
	 v1
	 il1
	 (lambda (u1) (abstract-if-procedure2 u1 v2 v3))
	 (lambda (il1 u1) (generate-if2 u1 v2 v3 il1 il2 il3))))
       ((vlad-false? v1)
	(generate-call v3 (vlad-empty-list) il3 (il:empty (vlad-empty-list))))
       (else (generate-call
	      v2 (vlad-empty-list) il2 (il:empty (vlad-empty-list))))))

(define (generate-if1 v1 v23 il1 il23)
 (cond ((empty-abstract-value? v23)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v23)
	;; widening case L2
	(il:map-dispatch v23
			 il23
			 (lambda (u23) (abstract-if-procedure1 v1 u23))
			 (lambda (il23 u23) (generate-if1 v1 u23 il1 il23))))
       ((vlad-pair? v23)
	(generate-if2 v1
		      (vlad-car v23)
		      (vlad-cdr v23)
		      il1
		      (il:car v23 il23)
		      (il:cdr v23 il23)))
       (else (il:panic "Argument to if-procedure is invalid"))))

(define (generate-if v il)
 (cond ((empty-abstract-value? v)
	(il:panic
	 "A run-time error that was detected at compile time has occurred"))
       ((union? v)
	;; widening case L3
	(il:map-dispatch
	 v il abstract-if-procedure (lambda (il u) (generate-if u il))))
       ((vlad-pair? v)
	(generate-if1 (vlad-car v) (vlad-cdr v) (il:car v il) (il:cdr v il)))
       (else (il:panic "Argument to if-procedure is invalid"))))

(define (generate-if-procedure instance)
 (generate-if (primitive-procedure-instance-v instance) (il:x)))

(define (generate-read-real instance)
 (let* ((v (primitive-procedure-instance-v instance))
	(symbol (primitive-procedure-instance-symbol instance))
	(primitive-procedure (lookup-primitive-procedure symbol))
	(f (primitive-procedure-abstract primitive-procedure)))
  (cond ((empty-abstract-value? v)
	 (il:panic
	  "A run-time error that was detected at compile time has occurred"))
	((union? v)
	 ;; needs work: The widening case is not annotated yet.
	 (il:map-dispatch
	  v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
	((vlad-empty-list? v) (il:call "read_real"))
	(else (il:panic "Argument to read-real is invalid")))))

(define (generate-real instance)
 (let* ((v (primitive-procedure-instance-v instance))
	(symbol (primitive-procedure-instance-symbol instance))
	(primitive-procedure (lookup-primitive-procedure symbol))
	(f (primitive-procedure-abstract primitive-procedure)))
  (cond ((empty-abstract-value? v)
	 (il:panic
	  "A run-time error that was detected at compile time has occurred"))
	((union? v)
	 ;; needs work: The widening case is not annotated yet.
	 (il:map-dispatch
	  v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
	((vlad-real? v) (if (void? v) (il:constant v) (il:x)))
	(else (il:panic "Argument to real is invalid")))))

(define (generate-write-real instance)
 (let* ((v (primitive-procedure-instance-v instance))
	(symbol (primitive-procedure-instance-symbol instance))
	(primitive-procedure (lookup-primitive-procedure symbol))
	(f (primitive-procedure-abstract primitive-procedure)))
  (cond ((empty-abstract-value? v)
	 (il:panic
	  "A run-time error that was detected at compile time has occurred"))
	((union? v)
	 ;; needs work: The widening case is not annotated yet.
	 (il:map-dispatch
	  v (il:x) f (lambda (il u) (il:call (lookup-instance symbol u) il))))
	((vlad-real? v)
	 (il:call "write_real" (if (void? v) (il:constant v) (il:x))))
	(else (il:panic "Argument to write-real is invalid")))))

(define (generate-zero instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H1
    (il:map-dispatch v
		     (il:x)
		     zero
		     (lambda (il u) (il:call (lookup-instance 'zero u) il))))
   ((or (nonrecursive-closure? v)
	(recursive-closure? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (il:construct*
     (zero v)
     (map (lambda (il:slot1 v1)
	   (il:call (lookup-instance 'zero v1) (il:slot1 v (il:x))))
	  (il:generate-slots v)
	  (aggregate-value-values v))))
   ;; In all cases, the result will be void so this case should never happen.
   (else (il:empty (zero v))))))

(define (generate-perturb instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H2
    (il:map-dispatch
     v
     (il:x)
     perturb
     (lambda (il u) (il:call (lookup-instance 'perturb u) il))))
   ((or (vlad-real? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (il:construct (perturb v) (il:x)))
   ((closure? v)
    (il:construct*
     (perturb v)
     (map (lambda (il:slot1 v1)
	   (il:call (lookup-instance 'perturb v1) (il:slot1 v (il:x))))
	  (il:generate-slots v)
	  (aggregate-value-values v))))
   ;; In all cases, the result will be void so this case should never happen.
   (else (il:empty (perturb v))))))

(define (generate-unperturb instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H3
    (il:map-dispatch
     v
     (il:x)
     unperturb
     (lambda (il u) (il:call (lookup-instance 'unperturb u) il))))
   ((perturbation-tagged-value? v)
    (il:perturbation-tagged-value-primal v (il:x)))
   ((and (closure? v) (not (empty-abstract-value? (unperturb v))))
    (il:construct*
     (unperturb v)
     (map (lambda (il:slot1 v1)
	   (il:call (lookup-instance 'unperturb v1) (il:slot1 v (il:x))))
	  (il:generate-slots v)
	  (aggregate-value-values v))))
   (else (il:panic "Argument to unperturb is not a perturbation value")))))

(define (generate-primal instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H4
    (il:map-dispatch v
		     (il:x)
		     primal
		     (lambda (il u) (il:call (lookup-instance 'primal u) il))))
   ((bundle? v) (il:bundle-primal v (il:x)))
   ((and (closure? v) (not (empty-abstract-value? (primal v))))
    (if (primitive-procedure? (primal v))
	;; In this case, the result will be void so this case should never
	;; happen.
	(il:empty (primal v))
	(il:construct*
	 (primal v)
	 (map (lambda (il:slot1 v1)
	       (il:call (lookup-instance 'primal v1) (il:slot1 v (il:x))))
	      (il:generate-slots v)
	      (aggregate-value-values v)))))
   (else (il:panic "Argument to primal is not a forward value")))))

(define (generate-tangent instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H5
    (il:map-dispatch
     v
     (il:x)
     tangent
     (lambda (il u) (il:call (lookup-instance 'tangent u) il))))
   ((bundle? v) (il:bundle-tangent v (il:x)))
   ((and (closure? v) (not (empty-abstract-value? (tangent v))))
    (if (primitive-procedure? (primal v))
	;; In this case, the result will be void so this case should never
	;; happen.
	(il:empty (tangent v))
	(il:construct*
	 (tangent v)
	 (map (lambda (il:slot1 v1)
	       (il:call (lookup-instance 'tangent v1) (il:slot1 v (il:x))))
	      (il:generate-slots v)
	      (aggregate-value-values v)))))
   (else (il:panic "Argument to tangent is not a forward value")))))

(define (generate-bundle instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H6
    (il:map-dispatch v
		     (il:x)
		     bundle
		     (lambda (il u) (il:call (lookup-instance 'bundle u) il))))
   ((vlad-pair? v)
    (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
     (cond
      ((empty-abstract-value? v1)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v1)
       ;; widening case H7
       (il:map-dispatch
	v1
	(il:car v (il:x))
	(lambda (u1) (bundle (vlad-cons u1 v2)))
	(lambda (il1 u1)
	 (il:call (lookup-instance 'bundle (vlad-cons u1 v2))
		  (il:construct (vlad-cons u1 v2) il1 (il:cdr v (il:x)))))))
      ((empty-abstract-value? v2)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v2)
       ;; widening case H8
       (il:map-dispatch
	v2
	(il:cdr v (il:x))
	(lambda (u2) (bundle (vlad-cons v1 u2)))
	(lambda (il2 u2)
	 (il:call (lookup-instance 'bundle (vlad-cons v1 u2))
		  (il:construct (vlad-cons v1 u2) (il:car v (il:x)) il2)))))
      ((and (perturbation-tagged-value? v2) (union? (unperturb v2)))
       ;; widening case H9
       ;; needs work
       ;; This can't use il:map-dispatch for now because of a freezing issue
       ;; that comes up with perturb, probably calling
       ;; (lambda (u2) (bundle (vlad-cons v1 (perturb u2)))) on (unperturb v2)
       ;; which is supposed to yield (bundle (vlad-cons v1 v2)). I'm not going
       ;; to debug this right now.
       ;; This happens in run-1-3 t16 -imprecise-inexacts.
       (il:dispatch
	(bundle (vlad-cons v1 v2))
	(unperturb v2)
	(il:perturbation-tagged-value-primal v2 (il:cdr v (il:x)))
	(map (lambda (il:member2 u2)
	      (il:widen
	       (bundle (vlad-cons v1 (perturb u2)))
	       (bundle (vlad-cons v1 v2))
	       (il:call
		(lookup-instance 'bundle (vlad-cons v1 (perturb u2)))
		(il:construct
		 (vlad-cons v1 (perturb u2))
		 (il:car v (il:x))
		 (il:construct (perturb u2)
			       (il:member2 (unperturb v2)
					   (il:perturbation-tagged-value-primal
					    v2 (il:cdr v (il:x)))))))))
	     (il:generate-members (unperturb v2))
	     (get-union-values (unperturb v2)))))
      ((and (or (vlad-empty-list? v1)
		(vlad-true? v1)
		(vlad-false? v1)
		(primitive-procedure? v1))
	    (every-bundlable? v1 v2))
       ;; In all cases, the result will be void so this case should never
       ;; happen.
       (il:empty (bundle (vlad-cons v1 v2))))
      ((or (and (vlad-real? v1) (every-bundlable? v1 v2))
	   ;; here I am: need to check conformance
	   ;;            even when one or both arguments is void
	   ;;            and even when one or both arguments is deep
	   (and (or (perturbation-tagged-value? v1)
		    (bundle? v1)
		    (sensitivity-tagged-value? v1)
		    (reverse-tagged-value? v1)
		    (vlad-pair? v1))
		(some-bundlable? v1 v2)))
       (il:construct
	(bundle (vlad-cons v1 v2)) (il:car v (il:x)) (il:cdr v (il:x))))
      ((bundle-aggregates-match? v1 v2)
       (let ((v0 (bundle (vlad-cons v1 v2))))
	(il:construct*
	 v0
	 (map (lambda (il:slot3a il:slot3b v3a v3b)
	       (il:call (lookup-instance 'bundle (vlad-cons  v3a v3b))
			(il:construct (vlad-cons v3a v3b)
				      (il:slot3a v1 (il:car v (il:x)))
				      (il:slot3b v2 (il:cdr v (il:x))))))
	      (il:generate-slots v1)
	      (il:generate-slots v2)
	      (aggregate-value-values v1)
	      (aggregate-value-values v2)))))
      (else (il:panic "Arguments to bundle do not conform")))))
   (else (il:panic "Arguments to bundle do not conform")))))

(define (generate-sensitize instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H10
    (il:map-dispatch
     v
     (il:x)
     sensitize
     (lambda (il u) (il:call (lookup-instance 'sensitize u) il))))
   ((or (vlad-real? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (il:construct (sensitize v) (il:x)))
   ((closure? v)
    (il:construct* (sensitize v)
		   (map (lambda (il:slot1 v1)
			 (il:call (lookup-instance 'sensitize v1)
				  (il:slot1 v (il:x))))
			(il:generate-slots v)
			(aggregate-value-values v))))
   ;; In all cases, the result will be void so this case should never happen.
   (else (il:empty (sensitize v))))))

(define (generate-unsensitize instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H11
    (il:map-dispatch
     v
     (il:x)
     unsensitize
     (lambda (il u) (il:call (lookup-instance 'unsensitize u) il))))
   ((sensitivity-tagged-value? v)
    (il:sensitivity-tagged-value-primal v (il:x)))
   ((and (closure? v) (not (empty-abstract-value? (unsensitize v))))
    (il:construct* (unsensitize v)
		   (map (lambda (il:slot1 v1)
			 (il:call (lookup-instance 'unsensitize v1)
				  (il:slot1 v (il:x))))
			(il:generate-slots v)
			(aggregate-value-values v))))
   (else (il:panic "Argument to unsensitize is not a sensitivity value")))))

(define (generate-plus instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H12
    (il:map-dispatch
     v (il:x) plus (lambda (il u) (il:call (lookup-instance 'plus u) il))))
   ((vlad-pair? v)
    (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
     (cond
      ;; needs work: The following two don't check conformance.
      ((is-zero? v1) (il:cdr v (il:x)))
      ((is-zero? v2) (il:car v (il:x)))
      ((empty-abstract-value? v1)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v1)
       ;; widening case H13
       (il:map-dispatch
	v1
	(il:car v (il:x))
	(lambda (u1) (plus (vlad-cons u1 v2)))
	(lambda (il1 u1)
	 (il:call (lookup-instance 'plus (vlad-cons u1 v2))
		  (il:construct (vlad-cons u1 v2) il1 (il:cdr v (il:x)))))))
      ((empty-abstract-value? v2)
       (il:panic
	"A run-time error that was detected at compile time has occurred"))
      ((union? v2)
       ;; widening case H14
       ;; There is no widening case H15
       (il:map-dispatch
	v2
	(il:cdr v (il:x))
	(lambda (u2) (plus (vlad-cons v1 u2)))
	(lambda (il2 u2)
	 (il:call (lookup-instance 'plus (vlad-cons v1 u2))
		  (il:construct (vlad-cons v1 u2) (il:car v (il:x)) il2)))))
      ((or (and (vlad-empty-list? v1) (vlad-empty-list? v2))
	   (and (vlad-true? v1) (vlad-true? v2))
	   (and (vlad-false? v1) (vlad-false? v2))
	   (and (primitive-procedure? v1)
		(primitive-procedure? v2)
		(eq? v1 v2)))
       ;; In all cases, the result will be void so this case should never
       ;; happen.
       (il:empty (plus (vlad-cons v1 v2))))
      ((and (vlad-real? v1) (vlad-real? v2))
       (il:binary (if (void? v1) (il:constant v1) (il:car v (il:x)))
		  "+"
		  (if (void? v2) (il:constant v2) (il:cdr v (il:x)))))
      ((plus-aggregates-match? v1 v2)
       (let ((v0 (plus (vlad-cons v1 v2))))
	(il:construct*
	 v0
	 (map (lambda (il:slot3a il:slot3b v3 v3a v3b)
	       (il:call (lookup-instance 'plus (vlad-cons v3a v3b))
			(il:construct (vlad-cons v3a v3b)
				      (il:slot3a v1 (il:car v (il:x)))
				      (il:slot3b v2 (il:cdr v (il:x))))))
	      (il:generate-slots v1)
	      (il:generate-slots v2)
	      (aggregate-value-values v0)
	      (aggregate-value-values v1)
	      (aggregate-value-values v2)))))
      (else (il:panic "Arguments to plus do not conform")))))
   (else (il:panic "Arguments to plus do not conform")))))

(define (generate-*j instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond
   ((empty-abstract-value? v)
    (il:panic
     "A run-time error that was detected at compile time has occurred"))
   ((union? v)
    ;; widening case H16
    (il:map-dispatch
     v (il:x) *j (lambda (il u) (il:call (lookup-instance '*j u) il))))
   ((or (vlad-real? v)
	(perturbation-tagged-value? v)
	(bundle? v)
	(sensitivity-tagged-value? v)
	(reverse-tagged-value? v)
	(vlad-pair? v))
    (il:construct (*j v) (il:x)))
   ((or (nonrecursive-closure? v) (recursive-closure? v))
    (il:construct*
     (*j v)
     (map (lambda (il:slot1 v1)
	   (il:call (lookup-instance '*j v1) (il:slot1 v (il:x))))
	  (il:generate-slots v)
	  (aggregate-value-values v))))
   ;; In all cases, the result will be void so this case should never happen.
   (else (il:empty (*j v))))))

(define (generate-*j-inverse instance)
 (let ((v (primitive-procedure-instance-v instance)))
  (cond ((empty-abstract-value? v)
	 (il:panic
	  "A run-time error that was detected at compile time has occurred"))
	((union? v)
	 ;; widening case H17
	 (il:map-dispatch
	  v
	  (il:x)
	  *j-inverse
	  (lambda (il u) (il:call (lookup-instance '*j-inverse u) il))))
	((reverse-tagged-value? v) (il:reverse-tagged-value-primal v (il:x)))
	((and (closure? v) (not (empty-abstract-value? (*j-inverse v))))
	 (if (primitive-procedure? (*j-inverse v))
	     ;; In this case, the result will be void so this case should never
	     ;; happen.
	     (il:empty (*j-inverse v))
	     (il:construct* (*j-inverse v)
			    (map (lambda (il:slot1 v1)
				  (il:call (lookup-instance '*j-inverse v1)
					   (il:slot1 v (il:x))))
				 (il:generate-slots v)
				 (aggregate-value-values v)))))
	(else (il:panic "Argument to *j-inverse is not a reverse value")))))

(define (generate-function-instances! bs)
 (for-each
  (lambda (instance)
   (let ((v1 (function-instance-v1 instance))
	 (v2 (function-instance-v2 instance)))
    (set-instance-il!
     instance
     ;; widening case J
     (generate-destructure
      (closure-parameter v1)
      v2
      (il:x)
      (lambda (v-alist)
       ;; bar
       (abstract-eval1 (closure-body v1) (construct-environment v1 v-alist)))
      (lambda (v-alist)
       ;; bar
       (let ((vs (construct-environment v1 v-alist)))
	(generate-letrec-bindings
	 (closure-body v1)
	 vs
	 v1
	 (closure-variables v1)
	 (cond ((nonrecursive-closure? v1) '())
	       ((recursive-closure? v1)
		(vector->list (recursive-closure-procedure-variables v1)))
	       (else (internal-error)))
	 (generate-expression
	  (closure-body v1)
	  vs
	  v1
	  (closure-variables v1)
	  (cond ((nonrecursive-closure? v1) '())
		((recursive-closure? v1)
		 (vector->list (recursive-closure-procedure-variables v1)))
		(else (internal-error)))
	  bs))))))))
  *function-instances*))

(define (generate-widener-instances!)
 (for-each
  (lambda (instance)
   (let ((v1 (widener-instance-v1 instance))
	 (v2 (widener-instance-v2 instance)))
    (set-instance-il!
     instance
     (if (empty-abstract-value? v1)
	 (il:empty v2)
	 (cond
	  ;; See the note for this case in all-subwidener-instances!.
	  ((union? v1)
	   ;; widening case K1
	   (il:dispatch v2
			v1
			(il:x)
			(map (lambda (il:member1 u1)
			      (il:widen u1 v2 (il:member1 v1 (il:x))))
			     (il:generate-members v1)
			     (get-union-values v1))))
	  ;; See the notes for this case in all-subwidener-instances!.
	  ((union? v2)
	   (let ((u2 (find-if (lambda (u2) (abstract-value-subset? v1 u2))
			      (get-union-values v2))))
	    ;; widening case K2
	    (il:construct-union u2 v2 (il:widen v1 u2 (il:x)))))
	  ((scalar-value? v2)
	   (cond ((void? v2) (il:empty v2))
		 ;; widening case K3
		 ((real? v1) (il:constant v1))
		 (else (internal-error))))
	  ;; widening case K4
	  (else (il:construct*
		 v2
		 ;; This will only be done on conforming structures
		 ;; since the analysis is almost union free.
		 ;; needs work: To check conformance.
		 (map (lambda (il:slot1a v1a v2a)
		       (il:widen v1a v2a (il:slot1a v1 (il:x))))
		      (il:generate-slots v1)
		      (aggregate-value-values v1)
		      (aggregate-value-values v2)))))))))
  *widener-instances*))

;;; Top-level generator

(define (il:let*-vs il)
 (if (il:let? il) (cons (il:let-v il) (il:let*-vs (il:let-il2 il))) '()))

(define (il:let*-xs il)
 (if (il:let? il) (cons (il:let-x il) (il:let*-xs (il:let-il2 il))) '()))

(define (il:let*-il1s il)
 (if (il:let? il) (cons (il:let-il1 il) (il:let*-il1s (il:let-il2 il))) '()))

(define (il:let*-il2 il) (if (il:let? il) (il:let*-il2 (il:let-il2 il)) il))

(define (il:mv-let*-vss il)
 (if (il:mv-let? il)
     (cons (il:mv-let-vs il) (il:mv-let*-vss (il:mv-let-il2 il)))
     '()))

(define (il:mv-let*-xss il)
 (if (il:mv-let? il)
     (cons (il:mv-let-xs il) (il:mv-let*-xss (il:mv-let-il2 il)))
     '()))

(define (il:mv-let*-il1s il)
 (if (il:mv-let? il)
     (cons (il:mv-let-il1 il) (il:mv-let*-il1s (il:mv-let-il2 il)))
     '()))

(define (il:mv-let*-il2 il)
 (if (il:mv-let? il) (il:mv-let*-il2 (il:mv-let-il2 il)) il))

(define (externalize-il il p?)
 (let loop ((il il))
  (cond
   ((il:c? il) 'c)
   ((il:x? il) 'x)
   ((il:y? il) 'y)
   ((il:z? il) 'z)
   ((il:t? il) `(t ,(il:t-index il)))
   ((il:a? il) `(a ,(c:instance-name (il:a-instance il)) ,(il:a-index il)))
   ((il:r? il) `(r ,(c:instance-name (il:r-instance il)) ,(il:r-index il)))
   ((il:empty? il)
    (if p? `(empty ,(safe-externalize (il:empty-v il))) '(empty)))
   ((il:tag? il)
    (if p?
	`(tag ,(safe-externalize (il:tag-u il))
	      ,(safe-externalize (il:tag-v il)))
	'(tag)))
   ((il:constant? il) `(constant ,(il:constant-number il)))
   ((il:let? il)
    (let ((vs (il:let*-vs il))
	  (xs (il:let*-xs il))
	  (il1s (il:let*-il1s il))
	  (il2 (il:let*-il2 il)))
     (if p?
	 (if (= (length vs) 1)
	     `(let (((,(loop (first xs)) ,(safe-externalize (first vs)))
		     ,(loop (first il1s))))
	       ,(loop il2))
	     `(let* (,@(map (lambda (x v il1)
			     `((,(loop x) ,(safe-externalize v)) ,(loop il1)))
			    xs vs il1s))
	       ,(loop il2)))
	 (if (= (length vs) 1)
	     `(let ((,(loop (first xs)) ,(loop (first il1s)))) ,(loop il2))
	     `(let* (,@(map (lambda (x v il1) `(,(loop x) ,(loop il1)))
			    xs vs il1s))
	       ,(loop il2))))))
   ((il:dispatch? il)
    (if p?
	`(dispatch ,(safe-externalize (il:dispatch-v0 il))
		   (,(loop (il:dispatch-il il))
		    ,(safe-externalize (il:dispatch-v il)))
		   ,@(map loop (il:dispatch-ils il)))
	`(dispatch ,(loop (il:dispatch-il il))
		   ,@(map loop (il:dispatch-ils il)))))
   ((il:panic? il) `(panic ,(il:panic-string il)))
   ((il:closure-ref? il)
    (if p?
	`(closure-ref ,(safe-externalize (il:closure-ref-v il))
		      ,(loop (il:closure-ref-il il))
		      ,(variable-name (il:closure-ref-x il)))
	`(closure-ref ,(loop (il:closure-ref-il il))
		      ,(variable-name (il:closure-ref-x il)))))
   ((il:perturbation-tagged-value-primal? il)
    (if p?
	`(perturbation-tagged-value-primal
	  ,(safe-externalize (il:perturbation-tagged-value-primal-v il))
	  ,(loop (il:perturbation-tagged-value-primal-il il)))
	`(perturbation-tagged-value-primal
	  ,(loop (il:perturbation-tagged-value-primal-il il)))))
   ((il:bundle-primal? il)
    (if p?
	`(bundle-primal ,(safe-externalize (il:bundle-primal-v il))
			,(loop (il:bundle-primal-il il)))
	`(bundle-primal ,(loop (il:bundle-primal-il il)))))
   ((il:bundle-tangent? il)
    (if p?
	`(bundle-tangent ,(safe-externalize (il:bundle-tangent-v il))
			 ,(loop (il:bundle-tangent-il il)))
	`(bundle-tangent ,(loop (il:bundle-tangent-il il)))))
   ((il:sensitivity-tagged-value-primal? il)
    (if p?
	`(sensitivity-tagged-value-primal
	  ,(safe-externalize (il:sensitivity-tagged-value-primal-v il))
	  ,(loop (il:sensitivity-tagged-value-primal-il il)))
	`(sensitivity-tagged-value-primal
	  ,(loop (il:sensitivity-tagged-value-primal-il il)))))
   ((il:reverse-tagged-value-primal? il)
    (if p?
	`(reverse-tagged-value-primal
	  ,(safe-externalize (il:reverse-tagged-value-primal-v il))
	  ,(loop (il:reverse-tagged-value-primal-il il)))
	`(reverse-tagged-value-primal
	  ,(loop (il:reverse-tagged-value-primal-il il)))))
   ((il:car? il)
    (if p?
	`(car ,(safe-externalize (il:car-v il)) ,(loop (il:car-il il)))
	`(car ,(loop (il:car-il il)))))
   ((il:cdr? il)
    (if p?
	`(cdr ,(safe-externalize (il:cdr-v il)) ,(loop (il:cdr-il il)))
	`(cdr ,(loop (il:cdr-il il)))))
   ((il:union-ref? il)
    (if p?
	`(union-ref ,(safe-externalize (il:union-ref-v il))
		    ,(safe-externalize (il:union-ref-u il))
		    ,(loop (il:union-ref-il il)))
	`(union-ref ,(loop (il:union-ref-il il)))))
   ((il:construct*? il)
    (if p?
	`(construct ,(safe-externalize (il:construct*-v il))
		    ,@(map loop (il:construct*-ils il)))
	`(construct ,@(map loop (il:construct*-ils il)))))
   ((il:construct-union? il)
    (if p?
	`(construct-union ,(safe-externalize (il:construct-union-u il))
			  ,(safe-externalize (il:construct-union-v il))
			  ,(loop (il:construct-union-il il)))
	`(construct-union ,(loop (il:construct-union-il il)))))
   ((il:construct-union0? il)
    (if p?
	`(construct-union ,(safe-externalize (il:construct-union0-u il))
			  ,(safe-externalize (il:construct-union0-v il)))
	'(construct-union)))
   ((il:call*? il)
    `(call* ,(c:instance-name (il:call*-instance il))
	    ,@(map loop (il:call*-ils il))))
   ((il:binary? il)
    `(binary ,(loop (il:binary-il1 il))
	     ,(il:binary-string il)
	     ,(loop (il:binary-il2 il))))
   ((il:binary-boolean? il)
    `(binary-boolean ,(loop (il:binary-boolean-il1 il))
		     ,(il:binary-boolean-string il)
		     ,(loop (il:binary-boolean-il2 il))))
   ((il:mv-let? il)
    (let ((vss (il:mv-let*-vss il))
	  (xss (il:mv-let*-xss il))
	  (il1s (il:mv-let*-il1s il))
	  (il2 (il:mv-let*-il2 il)))
     (if p?
	 (if (= (length vss) 1)
	     `(mv-let
	       ((,(map (lambda (x v) (list (loop x) (safe-externalize v)))
		       (first xss)
		       (first vss))
		 ,(loop (first il1s))))
	       ,(loop il2))
	     `(mv-let*
	       (,@(map (lambda (xs vs il1)
			`(,(map (lambda (x v)
				 (list (loop x) (safe-externalize v)))
				xs
				vs)
			  ,(loop il1)))
		       xss
		       vss
		       il1s))
	       ,(loop il2)))
	 (if (= (length vss) 1)
	     `(mv-let
	       ((,(map loop (first xss)) ,(loop (first il1s)))) ,(loop il2))
	     `(mv-let*
	       (,@(map (lambda (xs il1) `(,(map loop xs) ,(loop il1)))
		       xss
		       il1s))
	       ,(loop il2))))))
   ((il:values*? il)
    (if p?
	`(values ,(safe-externalize (il:values*-v il))
		 ,@(map loop (il:values*-ils il)))
	`(values ,@(map loop (il:values*-ils il)))))
   ((variable? il) (c:variable-name il))
   (else (internal-error)))))

(define (generate-cons-expression-instances! tags v1 v2)
 (unless (empty-tags? tags)
  (case (first tags)
   ((perturbation)
    (all-unary-ad-subinstances! 'unperturb v1)
    (all-unary-ad-subinstances! 'unperturb v2)
    (all-unary-ad-subinstances!
     'perturb
     (tagged-vlad-cons
      (remove-tag 'perturbation tags) (unperturb v1) (unperturb v2)))
    (generate-cons-expression-instances!
     (remove-tag 'perturbation tags) (unperturb v1) (unperturb v2)))
   ((forward)
    (all-unary-ad-subinstances! 'primal v1)
    (all-unary-ad-subinstances! 'primal v2)
    (all-unary-ad-subinstances! 'tangent v1)
    (all-unary-ad-subinstances! 'tangent v2)
    (all-unary-ad-subinstances! 'unperturb (tangent v1))
    (all-unary-ad-subinstances! 'unperturb (tangent v2))
    (all-unary-ad-subinstances! 'perturb
				(tagged-vlad-cons (remove-tag 'forward tags)
						  (unperturb (tangent v1))
						  (unperturb (tangent v2))))
    (all-binary-ad-subinstances!
     'bundle
     (vlad-cons (tagged-vlad-cons
		 (remove-tag 'forward tags) (primal v1) (primal v2))
		(perturb (tagged-vlad-cons (remove-tag 'forward tags)
					   (unperturb (tangent v1))
					   (unperturb (tangent v2))))))
    (generate-cons-expression-instances!
     (remove-tag 'forward tags) (primal v1) (primal v2))
    (generate-cons-expression-instances! (remove-tag 'forward tags)
					 (unperturb (tangent v1))
					 (unperturb (tangent v2))))
   ((sensitivity)
    (all-unary-ad-subinstances! 'unsensitize v1)
    (all-unary-ad-subinstances! 'unsensitize v2)
    (all-unary-ad-subinstances!
     'sensitize
     (tagged-vlad-cons
      (remove-tag 'sensitivity tags) (unsensitize v1) (unsensitize v2)))
    (generate-cons-expression-instances!
     (remove-tag 'sensitivity tags) (unsensitize v1) (unsensitize v2)))
   ((reverse)
    (all-unary-ad-subinstances! '*j-inverse v1)
    (all-unary-ad-subinstances! '*j-inverse v2)
    (all-unary-ad-subinstances!
     '*j
     (tagged-vlad-cons
      (remove-tag 'reverse tags) (*j-inverse v1) (*j-inverse v2)))
    (generate-cons-expression-instances!
     (remove-tag 'reverse tags) (*j-inverse v1) (*j-inverse v2)))
   (else (internal-error)))))

(define (generate-car/cdr-instances! tags v)
 (cond
  ((empty-tags? tags)
   (when (union? v)
    (for-each (lambda (u)
	       ;; widening case M1
	       (all-subwidener-instances!
		(if (vlad-pair? u) (vlad-car u) (empty-abstract-value))
		(tagged-vlad-car tags v))
	       ;; widening case M2
	       (all-subwidener-instances!
		(if (vlad-pair? u) (vlad-cdr u) (empty-abstract-value))
		(tagged-vlad-cdr tags v)))
	      (get-union-values v))))
  (else
   (case (first tags)
    ((perturbation)
     (all-unary-ad-subinstances! 'unperturb v)
     (all-unary-ad-subinstances!
      'perturb (tagged-vlad-car (remove-tag 'perturbation tags) (unperturb v)))
     (all-unary-ad-subinstances!
      'perturb (tagged-vlad-cdr (remove-tag 'perturbation tags) (unperturb v)))
     (generate-car/cdr-instances!
      (remove-tag 'perturbation tags) (unperturb v)))
    ((forward)
     (all-unary-ad-subinstances! 'primal v)
     (all-unary-ad-subinstances! 'tangent v)
     (all-unary-ad-subinstances! 'unperturb (tangent v))
     (all-unary-ad-subinstances!
      'perturb
      (tagged-vlad-car (remove-tag 'forward tags) (unperturb (tangent v))))
     (all-unary-ad-subinstances!
      'perturb
      (tagged-vlad-cdr (remove-tag 'forward tags) (unperturb (tangent v))))
     (all-binary-ad-subinstances!
      'bundle
      (vlad-cons (tagged-vlad-car (remove-tag 'forward tags) (primal v))
		 (perturb (tagged-vlad-car (remove-tag 'forward tags)
					   (unperturb (tangent v))))))
     (all-binary-ad-subinstances!
      'bundle
      (vlad-cons (tagged-vlad-cdr (remove-tag 'forward tags) (primal v))
		 (perturb (tagged-vlad-cdr (remove-tag 'forward tags)
					   (unperturb (tangent v))))))
     (generate-car/cdr-instances! (remove-tag 'forward tags) (primal v))
     (generate-car/cdr-instances!
      (remove-tag 'forward tags) (unperturb (tangent v))))
    ((sensitivity)
     (all-unary-ad-subinstances! 'unsensitize v)
     (all-unary-ad-subinstances!
      'sensitize
      (tagged-vlad-car (remove-tag 'sensitivity tags) (unsensitize v)))
     (all-unary-ad-subinstances!
      'sensitize
      (tagged-vlad-cdr (remove-tag 'sensitivity tags) (unsensitize v)))
     (generate-car/cdr-instances!
      (remove-tag 'sensitivity tags) (unsensitize v)))
    ((reverse)
     (all-unary-ad-subinstances! '*j-inverse v)
     (all-unary-ad-subinstances!
      '*j (tagged-vlad-car (remove-tag 'reverse tags) (*j-inverse v)))
     (all-unary-ad-subinstances!
      '*j (tagged-vlad-cdr (remove-tag 'reverse tags) (*j-inverse v)))
     (generate-car/cdr-instances! (remove-tag 'reverse tags) (*j-inverse v)))
    (else (internal-error))))))

(define (generate-destructuring-instances! p v)
 ;; The assumption is that v doesn't violate the syntactic constraints.
 (let outer ((p p) (v v) (k (lambda () #f)))
  (cond
   ;; This case comes first to avoid the dispatch.
   ((variable-access-expression? p) (k))
   ;; widening case J
   ((union? v) (for-each-union (lambda (u) (outer p u k)) v))
   ((constant-expression? p)
    ;; This can widen when the constant expression value violates the
    ;; syntactic constraints (presumably pair depth limit).
    ;; widening case A
    (let ((v-prime
	   (widen-abstract-value
	    (concrete-value->abstract-value (constant-expression-value p)))))
     (when (abstract-value-nondisjoint? v-prime v) (k))))
   ((lambda-expression? p)
    (when (and (nonrecursive-closure? v)
	       (dereferenced-expression-eqv?
		p (nonrecursive-closure-lambda-expression v)))
     (let inner ((xs1 (parameter-variables p))
		 (xs2 (nonrecursive-closure-variables v))
		 (vs (get-nonrecursive-closure-values v))
		 (k k))
      (if (null? xs1)
	  (k)
	  (outer (allocate-variable-access-expression (first xs1))
		 (first vs)
		 (lambda () (inner (rest xs1) (rest xs2) (rest vs) k)))))))
   ((letrec-expression? p)
    (assert (and (variable-access-expression? (letrec-expression-body p))
		 (memp variable=?
		       (variable-access-expression-variable
			(letrec-expression-body p))
		       (letrec-expression-procedure-variables p))))
    (when (and (recursive-closure? v)
	       (= (recursive-closure-index v)
		  (positionp variable=?
			     (variable-access-expression-variable
			      (letrec-expression-body p))
			     (letrec-expression-procedure-variables p)))
	       (= (vector-length (recursive-closure-procedure-variables v))
		  (length (letrec-expression-procedure-variables p)))
	       (= (vector-length (recursive-closure-lambda-expressions v))
		  (length (letrec-expression-lambda-expressions p)))
	       (every dereferenced-expression-eqv?
		      (vector->list (recursive-closure-lambda-expressions v))
		      (letrec-expression-lambda-expressions p)))
     (let inner ((xs1 (parameter-variables p))
		 (xs2 (recursive-closure-variables v))
		 (vs (get-recursive-closure-values v))
		 (k k))
      (if (null? xs1)
	  (k)
	  (outer (allocate-variable-access-expression (first xs1))
		 (first vs)
		 (lambda () (inner (rest xs1) (rest xs2) (rest vs) k)))))))
   ((cons-expression? p)
    (generate-car/cdr-instances! (cons-expression-tags p) v)
    (outer (cons-expression-car p)
	   (tagged-vlad-car (cons-expression-tags p) v)
	   (lambda ()
	    (outer (cons-expression-cdr p)
		   (tagged-vlad-cdr (cons-expression-tags p) v)
		   k))))
   (else (internal-error)))))

(define (generate! e bs)
 (profile "~a generate! determine-void?!~%" (lambda () (determine-void?!)))
 (profile "~a generate! all-function-instances!~%"
	  (lambda () (all-function-instances!)))
 (profile "~a generate! all-widener-instances!~%"
	  (lambda () (all-widener-instances!)))
 (profile
  "~a generate! primitive-procedure-all-instances!~%"
  (lambda ()
   (for-each (lambda (b)
	      (unless (eq? (primitive-procedure-symbol (value-binding-value b))
			   'write)
	       ((primitive-procedure-all-instances! (value-binding-value b)))))
	     *value-bindings*)))
 (profile
  "~a generate! cons expressions~%"
  (lambda ()
   (for-each
    (lambda (e)
     (when (cons-expression? e)
      (for-each (lambda (b)
		 (generate-cons-expression-instances!
		  (cons-expression-tags e)
		  (abstract-eval1
		   (cons-expression-car e)
		   (restrict-environment (environment-binding-values b)
					 (cons-expression-car-indices e)))
		  (abstract-eval1
		   (cons-expression-cdr e)
		   (restrict-environment (environment-binding-values b)
					 (cons-expression-cdr-indices e)))))
		(environment-bindings e))))
    *expressions*)))
 (profile
  "~a generate! cons parameters~%"
  (lambda ()
   (for-each
    (lambda (instance)
     (let ((v1 (function-instance-v1 instance))
	   (v2 (function-instance-v2 instance)))
      (when (and (closure? v1)
		 (some-value-tags
		  (lambda (tags2) (prefix-tags? (value-tags v1) tags2)) v2))
       (generate-destructuring-instances! (closure-parameter v1) v2))))
    *function-instances*)
   (for-each
    (lambda (e)
     (when (and (application? e) (lambda-expression? (application-callee e)))
      (let ((p (lambda-expression-parameter (application-callee e)))
	    (tags1 (lambda-expression-tags (application-callee e))))
       (for-each
	(lambda (b)
	 (let* ((vs (environment-binding-values b))
		(v (abstract-eval1 (application-argument e)
				   (restrict-environment
				    vs (application-argument-indices e)))))
	  (when (some-value-tags (lambda (tags) (prefix-tags? tags1 tags)) v)
	   (generate-destructuring-instances! p v))))
	(environment-bindings e)))))
    *expressions*)))
 (for-each-indexed set-c:index! *variables*)
 (for-each-indexed set-c:index! *function-instances*)
 (for-each-indexed set-c:index! *widener-instances*)
 (profile "~a generate! all-nested-abstract-values~%"
	  (lambda () (set! *vs* (all-nested-abstract-values))))
 (profile "~a generate! determine-void?!~%" (lambda () (determine-void?!)))
 (set! *frozen?* #t)
 (for-each-indexed set-c:index! *vs*)
 (profile "~a generate! generate-function-instances!~%"
	  (lambda () (generate-function-instances! bs)))
 (profile "~a generate! generate-widener-instances!~%"
	  (lambda () (generate-widener-instances!)))
 (profile
  "~a generate! primitive-procedure-generate~%"
  (lambda ()
   (for-each
    (lambda (b)
     (unless (eq? (primitive-procedure-symbol (value-binding-value b)) 'write)
      (let ((generate (primitive-procedure-generate (value-binding-value b))))
       (for-each
	(lambda (instance) (set-instance-il! instance (generate instance)))
	(primitive-procedure-instances (value-binding-value b))))))
    *value-bindings*)))
 (profile
  "~a generate! main~%"
  (lambda ()
   (let ((vs (environment-binding-values (first (environment-bindings e)))))
    (set! *il*
	  (generate-letrec-bindings e
				    vs
				    ;; A placeholder.
				    (empty-abstract-value)
				    (free-variables e)
				    '()
				    (generate-expression e
							 vs
							 ;; A placeholder.
							 (empty-abstract-value)
							 (free-variables e)
							 '()
							 bs)))))))

;;; Inliner

(define (determine-call-site-counts!)
 (for-each
  (lambda (instance) (increment-call-site-counts! (instance-il instance)))
  (append *function-instances*
	  *widener-instances*
	  (map-reduce
	   append
	   '()
	   (lambda (b) (primitive-procedure-instances (value-binding-value b)))
	   *value-bindings*)))
 (increment-call-site-counts! *il*))

(define (increment-call-site-counts! il)
 (cond
  ((il:c? il) #f)
  ((il:x? il) #f)
  ((il:y? il) #f)
  ((il:z? il) #f)
  ((il:t? il) #f)
  ((il:a? il) #f)
  ((il:r? il) #f)
  ((il:empty? il) #f)
  ((il:tag? il) #f)
  ((il:constant? il) #f)
  ((il:let? il)
   (increment-call-site-counts! (il:let-il1 il))
   (increment-call-site-counts! (il:let-il2 il)))
  ((il:dispatch? il)
   (increment-call-site-counts! (il:dispatch-il il))
   (for-each increment-call-site-counts! (il:dispatch-ils il)))
  ((il:panic? il) il)
  ((il:closure-ref? il)
   (increment-call-site-counts! (il:closure-ref-il il)))
  ((il:perturbation-tagged-value-primal? il)
   (increment-call-site-counts! (il:perturbation-tagged-value-primal-il il)))
  ((il:bundle-primal? il)
   (increment-call-site-counts! (il:bundle-primal-il il)))
  ((il:bundle-tangent? il)
   (increment-call-site-counts! (il:bundle-tangent-il il)))
  ((il:sensitivity-tagged-value-primal? il)
   (increment-call-site-counts! (il:sensitivity-tagged-value-primal-il il)))
  ((il:reverse-tagged-value-primal? il)
   (increment-call-site-counts! (il:reverse-tagged-value-primal-il il)))
  ((il:car? il) (increment-call-site-counts! (il:car-il il)))
  ((il:cdr? il) (increment-call-site-counts! (il:cdr-il il)))
  ((il:union-ref? il)
   (increment-call-site-counts! (il:union-ref-il il)))
  ((il:construct*? il)
   (for-each increment-call-site-counts! (il:construct*-ils il)))
  ((il:construct-union? il)
   (increment-call-site-counts! (il:construct-union-il il)))
  ((il:construct-union0? il) #f)
  ((il:call*? il)
   (unless (string? (il:call*-instance il))
    (set-instance-number-of-call-sites!
     (il:call*-instance il)
     (+ (instance-number-of-call-sites (il:call*-instance il)) 1)))
   (for-each increment-call-site-counts! (il:call*-ils il)))
  ((il:binary? il)
   (increment-call-site-counts! (il:binary-il1 il))
   (increment-call-site-counts! (il:binary-il2 il)))
  ((il:binary-boolean? il)
   (increment-call-site-counts! (il:binary-boolean-il1 il))
   (increment-call-site-counts! (il:binary-boolean-il2 il)))
  ((il:mv-let? il)
   (increment-call-site-counts! (il:mv-let-il1 il))
   (increment-call-site-counts! (il:mv-let-il2 il)))
  ((il:values*? il) (for-each increment-call-site-counts! (il:values*-ils il)))
  ((variable? il) #f)
  (else (internal-error))))

(define (inline il)
 ;; Must be called pre-SRA.
 (profile
  "~a inline~%"
  (lambda ()
   (let loop ((il il))
    (cond ((il:c? il) il)
	  ((il:x? il) il)
	  ((il:y? il) il)
	  ((il:z? il) il)
	  ((il:t? il) il)
	  ((il:a? il) il)
	  ((il:r? il) il)
	  ((il:empty? il) il)
	  ((il:tag? il) il)
	  ((il:constant? il) il)
	  ((il:let? il)
	   (il:let (il:let-v il)
		   (il:let-x il)
		   (loop (il:let-il1 il))
		   (loop (il:let-il2 il))))
	  ((il:dispatch? il)
	   (il:dispatch (il:dispatch-v0 il)
			(il:dispatch-v il)
			(loop (il:dispatch-il il))
			(map loop (il:dispatch-ils il))))
	  ((il:panic? il) il)
	  ((il:closure-ref? il)
	   (il:closure-ref (il:closure-ref-v il)
			   (loop (il:closure-ref-il il))
			   (il:closure-ref-x il)))
	  ((il:perturbation-tagged-value-primal? il)
	   (il:perturbation-tagged-value-primal
	    (il:perturbation-tagged-value-primal-v il)
	    (loop (il:perturbation-tagged-value-primal-il il))))
	  ((il:bundle-primal? il)
	   (il:bundle-primal
	    (il:bundle-primal-v il) (loop (il:bundle-primal-il il))))
	  ((il:bundle-tangent? il)
	   (il:bundle-tangent
	    (il:bundle-tangent-v il) (loop (il:bundle-tangent-il il))))
	  ((il:sensitivity-tagged-value-primal? il)
	   (il:sensitivity-tagged-value-primal
	    (il:sensitivity-tagged-value-primal-v il)
	    (loop (il:sensitivity-tagged-value-primal-il il))))
	  ((il:reverse-tagged-value-primal? il)
	   (il:reverse-tagged-value-primal
	    (il:reverse-tagged-value-primal-v il)
	    (loop (il:reverse-tagged-value-primal-il il))))
	  ((il:car? il) (il:car (il:car-v il) (loop (il:car-il il))))
	  ((il:cdr? il) (il:cdr (il:cdr-v il) (loop (il:cdr-il il))))
	  ((il:union-ref? il)
	   (il:union-ref (il:union-ref-v il)
			 (il:union-ref-u il)
			 (loop (il:union-ref-il il))))
	  ((il:construct*? il)
	   (make-il:construct* (il:construct*-v il)
			       (map loop (il:construct*-ils il))))
	  ((il:construct-union? il)
	   (il:construct-union (il:construct-union-u il)
			       (il:construct-union-v il)
			       (loop (il:construct-union-il il))))
	  ((il:construct-union0? il)
	   (make-il:construct-union0 (il:construct-union0-u il)
				     (il:construct-union0-v il)))
	  ((il:call*? il)
	   (let ((instance (il:call*-instance il)))
	    (cond
	     ((and (not (string? instance)) (inline? instance))
	      (cond
	       ((function-instance? instance)
		(if (void? (function-instance-v1 instance))
		    (if (void? (function-instance-v2 instance))
			(loop (instance-il instance))
			(il:let (function-instance-v2 instance)
				(il:x)
				(loop (first (il:call*-ils il)))
				(loop (instance-il instance))))
		    (if (void? (function-instance-v2 instance))
			(il:let (function-instance-v1 instance)
				(il:c)
				(loop (first (il:call*-ils il)))
				(loop (instance-il instance)))
			;; We use il:z here to get the effect of a parallel let
			;; instead of a let*. I don't believe that
			;; (second (il:call*-ils il)) can contain a free
			;; reference to il:z.
			(il:let
			 (function-instance-v1 instance)
			 (il:z)
			 (loop (first (il:call*-ils il)))
			 (il:let (function-instance-v2 instance)
				 (il:x)
				 (loop (second (il:call*-ils il)))
				 (il:let (function-instance-v1 instance)
					 (il:c)
					 (il:z)
					 (loop (instance-il instance))))))))
	       ((widener-instance? instance)
		(if (void? (widener-instance-v1 instance))
		    (loop (instance-il instance))
		    (il:let (widener-instance-v1 instance)
			    (il:x)
			    (loop (first (il:call*-ils il)))
			    (loop (instance-il instance)))))
	       ((primitive-procedure-instance? instance)
		(if (void? (primitive-procedure-instance-v instance))
		    (loop (instance-il instance))
		    (il:let (primitive-procedure-instance-v instance)
			    (il:x)
			    (loop (first (il:call*-ils il)))
			    (loop (instance-il instance)))))
	       (else (internal-error))))
	     (else (make-il:call* (il:call*-instance il)
				  (map loop (il:call*-ils il)))))))
	  ((il:binary? il)
	   (il:binary (loop (il:binary-il1 il))
		      (il:binary-string il)
		      (loop (il:binary-il2 il))))
	  ((il:binary-boolean? il)
	   (il:binary-boolean (loop (il:binary-boolean-il1 il))
			      (il:binary-boolean-string il)
			      (loop (il:binary-boolean-il2 il))))
	  ((variable? il) il)
	  (else (internal-error)))))))

;;; Intermediate-language ANF converter

(define (il:replace il1 il2 il)
 (let loop ((il il))
  (cond ((eq? il il1) il2)
	((il:c? il) il)
	((il:x? il) il)
	((il:y? il) il)
	((il:z? il) il)
	((il:t? il) il)
	((il:a? il) il)
	((il:r? il) il)
	((il:empty? il) il)
	((il:tag? il) il)
	((il:constant? il) il)
	((il:let? il)
	 (il:let (il:let-v il)
		 (il:let-x il)
		 (loop (il:let-il1 il))
		 (if (eq? (il:let-x il) il1)
		     (il:let-il2 il)
		     (loop (il:let-il2 il)))))
	((il:dispatch? il)
	 (il:dispatch (il:dispatch-v0 il)
		      (il:dispatch-v il)
		      (loop (il:dispatch-il il))
		      (map loop (il:dispatch-ils il))))
	((il:panic? il) il)
	((il:closure-ref? il)
	 (il:closure-ref (il:closure-ref-v il)
			 (loop (il:closure-ref-il il))
			 (il:closure-ref-x il)))
	((il:perturbation-tagged-value-primal? il)
	 (il:perturbation-tagged-value-primal
	  (il:perturbation-tagged-value-primal-v il)
	  (loop (il:perturbation-tagged-value-primal-il il))))
	((il:bundle-primal? il)
	 (il:bundle-primal
	  (il:bundle-primal-v il) (loop (il:bundle-primal-il il))))
	((il:bundle-tangent? il)
	 (il:bundle-tangent
	  (il:bundle-tangent-v il) (loop (il:bundle-tangent-il il))))
	((il:sensitivity-tagged-value-primal? il)
	 (il:sensitivity-tagged-value-primal
	  (il:sensitivity-tagged-value-primal-v il)
	  (loop (il:sensitivity-tagged-value-primal-il il))))
	((il:reverse-tagged-value-primal? il)
	 (il:reverse-tagged-value-primal
	  (il:reverse-tagged-value-primal-v il)
	  (loop (il:reverse-tagged-value-primal-il il))))
	((il:car? il) (il:car (il:car-v il) (loop (il:car-il il))))
	((il:cdr? il) (il:cdr (il:cdr-v il) (loop (il:cdr-il il))))
	((il:union-ref? il)
	 (il:union-ref (il:union-ref-v il)
		       (il:union-ref-u il)
		       (loop (il:union-ref-il il))))
	((il:construct*? il)
	 (make-il:construct* (il:construct*-v il)
			     (map loop (il:construct*-ils il))))
	((il:construct-union? il)
	 (il:construct-union (il:construct-union-u il)
			     (il:construct-union-v il)
			     (loop (il:construct-union-il il))))
	((il:construct-union0? il)
	 (make-il:construct-union0 (il:construct-union0-u il)
				   (il:construct-union0-v il)))
	((il:call*? il)
	 (make-il:call* (il:call*-instance il) (map loop (il:call*-ils il))))
	((il:binary? il)
	 (il:binary (loop (il:binary-il1 il))
		    (il:binary-string il)
		    (loop (il:binary-il2 il))))
	((il:binary-boolean? il)
	 (il:binary-boolean (loop (il:binary-boolean-il1 il))
			    (il:binary-boolean-string il)
			    (loop (il:binary-boolean-il2 il))))
	((il:mv-let? il)
	 (il:mv-let (il:mv-let-vs il)
		    (il:mv-let-xs il)
		    (loop (il:mv-let-il1 il))
		    (if (memq il1 (il:mv-let-xs il))
			(il:mv-let-il2 il)
			(loop (il:mv-let-il2 il)))))
	((il:values*? il)
	 (il:values* (il:values*-v il) (map loop (il:values*-ils il))))
	((variable? il) il)
	(else (internal-error)))))

(define (il:copy-propagate il)
 ;; Because this doesn't descend into any other construct, it should only be
 ;; used on code in ANF (either pre- or post-SRA).
 (profile
  "~a il:copy-propagate~%"
  (lambda ()
   (let loop ((il il) (bs '()))
    (cond
     ((il:let? il)
      (let ((il1 (loop (il:let-il1 il) bs)))
       (if (or (il:c? il1)
	       (il:x? il1)
	       (il:y? il1)
	       (il:z? il1)
	       (il:t? il1)
	       (il:a? il1)
	       (il:r? il1)
	       (variable? il1))
	   (loop (il:let-il2 il) (cons (cons (il:let-x il) il1) bs))
	   (il:let (il:let-v il)
		   (il:let-x il)
		   il1
		   (loop (il:let-il2 il)
			 (cons (cons (il:let-x il) 'bound) bs))))))
     ((il:mv-let? il)
      (let ((il1 (loop (il:mv-let-il1 il) bs)))
       (assert
	(or (not (il:values*? il1))
	    (= (length (il:mv-let-xs il)) (length (il:values*-ils il1)))))
       (cond
	((il:values*? il1)
	 (loop (il:mv-let-il2 il)
	       (append (map cons (il:mv-let-xs il) (il:values*-ils il1)) bs)))
	((il:mv-let? il1)
	 (loop (il:sra-anf-convert
		(il:mv-let
		 (il:mv-let-vs il) (il:mv-let-xs il) il1 (il:mv-let-il2 il)))
	       bs))
	(else (il:mv-let (il:mv-let-vs il)
			 (il:mv-let-xs il)
			 il1
			 (loop (il:mv-let-il2 il)
			       (append (map (lambda (x) (cons x 'bound))
					    (il:mv-let-xs il))
				       bs)))))))
     ((il:dispatch? il)
      (il:dispatch (il:dispatch-v0 il)
		   (il:dispatch-v il)
		   (loop (il:dispatch-il il) bs)
		   (map (lambda (il) (loop il bs)) (il:dispatch-ils il))))
     ((or (il:c? il)
	  (il:x? il)
	  (il:y? il)
	  (il:z? il)
	  (il:t? il)
	  (il:a? il)
	  (il:r? il)
	  (variable? il))
      (let ((found? (assq il bs)))
       (if (and found? (not (eq? (cdr found?) 'bound))) (cdr found?) il)))
     ((il:empty? il) il)
     ((il:tag? il) il)
     ((il:constant? il) il)
     ((il:panic? il) il)
     ((il:closure-ref? il)
      (il:closure-ref (il:closure-ref-v il)
		      (loop (il:closure-ref-il il) bs)
		      (il:closure-ref-x il)))
     ((il:perturbation-tagged-value-primal? il)
      (il:perturbation-tagged-value-primal
       (il:perturbation-tagged-value-primal-v il)
       (loop (il:perturbation-tagged-value-primal-il il) bs)))
     ((il:bundle-primal? il)
      (il:bundle-primal
       (il:bundle-primal-v il) (loop (il:bundle-primal-il il) bs)))
     ((il:bundle-tangent? il)
      (il:bundle-tangent
       (il:bundle-tangent-v il) (loop (il:bundle-tangent-il il) bs)))
     ((il:sensitivity-tagged-value-primal? il)
      (il:sensitivity-tagged-value-primal
       (il:sensitivity-tagged-value-primal-v il)
       (loop (il:sensitivity-tagged-value-primal-il il) bs)))
     ((il:reverse-tagged-value-primal? il)
      (il:reverse-tagged-value-primal
       (il:reverse-tagged-value-primal-v il)
       (loop (il:reverse-tagged-value-primal-il il) bs)))
     ((il:car? il) (il:car (il:car-v il) (loop (il:car-il il) bs)))
     ((il:cdr? il) (il:cdr (il:cdr-v il) (loop (il:cdr-il il) bs)))
     ((il:union-ref? il)
      (il:union-ref
       (il:union-ref-v il) (il:union-ref-u il) (loop (il:union-ref-il il) bs)))
     ((il:construct*? il)
      (make-il:construct*
       (il:construct*-v il)
       (map (lambda (il) (loop il bs)) (il:construct*-ils il))))
     ((il:construct-union? il)
      (il:construct-union (il:construct-union-u il)
			  (il:construct-union-v il)
			  (loop (il:construct-union-il il) bs)))
     ((il:construct-union0? il) il)
     ((il:call*? il)
      (make-il:call* (il:call*-instance il)
		     (map (lambda (il) (loop il bs)) (il:call*-ils il))))
     ((il:binary? il)
      (il:binary (loop (il:binary-il1 il) bs)
		 (il:binary-string il)
		 (loop (il:binary-il2 il) bs)))
     ((il:binary-boolean? il)
      (il:binary-boolean (loop (il:binary-boolean-il1 il) bs)
			 (il:binary-boolean-string il)
			 (loop (il:binary-boolean-il2 il) bs)))
     ((il:values*? il)
      (il:values* (il:values*-v il)
		  (map (lambda (il) (loop il bs)) (il:values*-ils il))))
     (else (internal-error)))))))

(define (il:anf-convert il)
 ;; Must be called pre-SRA.
 (il:copy-propagate
  (profile
   "~a il:anf-convert~%"
   (lambda ()
    (let outer ((il il))
     (let ((result
	    ;; Returns (bindings il) where each binding is (v x il).
	    (let inner ((il il))
	     (cond
	      ((il:c? il) (list '() il))
	      ((il:x? il) (list '() il))
	      ((il:y? il) (list '() il))
	      ((il:z? il) (list '() il))
	      ((il:t? il) (list '() il))
	      ((il:a? il) (list '() il))
	      ((il:r? il) (list '() il))
	      ((il:empty? il)
	       (let ((t (il:t))) (list (list (list (il:empty-v il) t il)) t)))
	      ((il:tag? il)
	       (let ((t (il:t)))
		(list (list (list (make-tag (il:tag-v il)) t il)) t)))
	      ((il:constant? il)
	       (let ((t (il:t))) (list (list (list (abstract-real) t il)) t)))
	      ((il:let? il)
	       (let* ((result1 (inner (il:let-il1 il)))
		      (result2
		       (inner
			(il:replace
			 (il:let-x il) (second result1) (il:let-il2 il)))))
		(list (append (first result1) (first result2))
		      (second result2))))
	      ((il:dispatch? il)
	       (let* ((result (inner (il:dispatch-il il))) (t (il:t)))
		(list (append
		       (first result)
		       (list
			(list
			 (il:dispatch-v0 il)
			 t
			 (il:dispatch (il:dispatch-v0 il)
				      (il:dispatch-v il)
				      (second result)
				      (map outer (il:dispatch-ils il))))))
		      t)))
	      ((il:panic? il)
	       (let ((t (il:t)))
		(list (list (list (empty-abstract-value) t il)) t)))
	      ((il:closure-ref? il)
	       (let* ((result (inner (il:closure-ref-il il))) (t (il:t)))
		(list
		 (append
		  (first result)
		  (list
		   (list
		    (closure-ref (il:closure-ref-v il) (il:closure-ref-x il))
		    t
		    (il:closure-ref (il:closure-ref-v il)
				    (second result)
				    (il:closure-ref-x il)))))
		 t)))
	      ((il:perturbation-tagged-value-primal? il)
	       (let* ((result
		       (inner (il:perturbation-tagged-value-primal-il il)))
		      (t (il:t)))
		(list (append
		       (first result)
		       (list (list (get-perturbation-tagged-value-primal
				    (il:perturbation-tagged-value-primal-v il))
				   t
				   (il:perturbation-tagged-value-primal
				    (il:perturbation-tagged-value-primal-v il)
				    (second result)))))
		      t)))
	      ((il:bundle-primal? il)
	       (let* ((result (inner (il:bundle-primal-il il))) (t (il:t)))
		(list
		 (append
		  (first result)
		  (list (list (get-bundle-primal (il:bundle-primal-v il))
			      t
			      (il:bundle-primal (il:bundle-primal-v il)
						(second result)))))
		 t)))
	      ((il:bundle-tangent? il)
	       (let* ((result (inner (il:bundle-tangent-il il))) (t (il:t)))
		(list
		 (append
		  (first result)
		  (list (list (get-bundle-tangent (il:bundle-tangent-v il))
			      t
			      (il:bundle-tangent (il:bundle-tangent-v il)
						 (second result)))))
		 t)))
	      ((il:sensitivity-tagged-value-primal? il)
	       (let* ((result
		       (inner (il:sensitivity-tagged-value-primal-il il)))
		      (t (il:t)))
		(list
		 (append
		  (first result)
		  (list (list (get-sensitivity-tagged-value-primal
			       (il:sensitivity-tagged-value-primal-v il))
			      t
			      (il:sensitivity-tagged-value-primal
			       (il:sensitivity-tagged-value-primal-v il)
			       (second result)))))
		 t)))
	      ((il:reverse-tagged-value-primal? il)
	       (let* ((result (inner (il:reverse-tagged-value-primal-il il)))
		      (t (il:t)))
		(list
		 (append (first result)
			 (list (list (get-reverse-tagged-value-primal
				      (il:reverse-tagged-value-primal-v il))
				     t
				     (il:reverse-tagged-value-primal
				      (il:reverse-tagged-value-primal-v il)
				      (second result)))))
		 t)))
	      ((il:car? il)
	       (let* ((result (inner (il:car-il il))) (t (il:t)))
		(list
		 (append (first result)
			 (list (list (vlad-car (il:car-v il))
				     t
				     (il:car (il:car-v il) (second result)))))
		 t)))
	      ((il:cdr? il)
	       (let* ((result (inner (il:cdr-il il))) (t (il:t)))
		(list
		 (append (first result)
			 (list (list (vlad-cdr (il:cdr-v il))
				     t
				     (il:cdr (il:cdr-v il) (second result)))))
		 t)))
	      ((il:union-ref? il)
	       (let* ((result (inner (il:union-ref-il il))) (t (il:t)))
		(list (append (first result)
			      (list (list (il:union-ref-u il)
					  t
					  (il:union-ref (il:union-ref-v il)
							(il:union-ref-u il)
							(second result)))))
		      t)))
	      ((il:construct*? il)
	       (let* ((results (map inner (il:construct*-ils il))) (t (il:t)))
		(list (append
		       (reduce append (map first results) '())
		       (list (list (il:construct*-v il)
				   t
				   (make-il:construct* (il:construct*-v il)
						       (map second results)))))
		      t)))
	      ((il:construct-union? il)
	       (let* ((result (inner (il:construct-union-il il))) (t (il:t)))
		(list
		 (append
		  (first result)
		  (list (list (il:construct-union-v il)
			      t
			      (il:construct-union (il:construct-union-u il)
						  (il:construct-union-v il)
						  (second result)))))
		 t)))
	      ((il:construct-union0? il)
	       (let ((t (il:t)))
		(list (list (list (il:construct-union0-v il) t il)) t)))
	      ((il:call*? il)
	       (let* ((results (map inner (il:call*-ils il)))
		      (t (il:t))
		      (instance (il:call*-instance il)))
		(list
		 (append
		  (reduce append (map first results) '())
		  (list (list (instance-return-value instance)
			      t
			      (make-il:call* instance (map second results)))))
		 t)))
	      ((il:binary? il)
	       (let* ((result1 (inner (il:binary-il1 il)))
		      (result2 (inner (il:binary-il2 il)))
		      (t (il:t)))
		(list (append (first result1)
			      (first result2)
			      (list (list (abstract-real)
					  t
					  (il:binary (second result1)
						     (il:binary-string il)
						     (second result2)))))
		      t)))
	      ((il:binary-boolean? il)
	       (let* ((result1 (inner (il:binary-boolean-il1 il)))
		      (result2 (inner (il:binary-boolean-il2 il)))
		      (t (il:t)))
		(list
		 (append
		  (first result1)
		  (first result2)
		  (list (list (abstract-boolean)
			      t
			      (il:binary-boolean (second result1)
						 (il:binary-boolean-string il)
						 (second result2)))))
		 t)))
	      ((variable? il) (list '() il))
	      (else (internal-error))))))
      (let loop ((bindings (first result)))
       (if (null? bindings)
	   (second result)
	   (let ((il (loop (rest bindings))))
	    (if (and (il:values*? il)
		     (= (length (second (first bindings)))
			(length (il:values*-ils il)))
		     (every eq? (second (first bindings)) (il:values*-ils il))
		     (il:dispatch? (third (first bindings))))
		(third (first bindings))
		(il:let (first (first bindings))
			(second (first bindings))
			(third (first bindings))
			il)))))))))))

;;; SRA

(define (il:flatten v)
 (cond ((boxed? v) (list (il:t)))
       ((empty-abstract-value? v) '())
       ((union? v)
	(cons (il:t) (map-reduce append '() il:flatten (get-union-values v))))
       ((abstract-real? v) (list (il:t)))
       ((scalar-value? v) '())
       (else (map-reduce append '() il:flatten (aggregate-value-values v)))))

(define (il:split-flat xs ns)
 (cond ((null? ns)
	(assert (null? xs))
	'())
       (else
	(cons (sublist xs 0 (first ns))
	      (il:split-flat (sublist xs (first ns) (length xs)) (rest ns))))))

(define (il:get-closure-values v xs)
 (assert (= (number-of-slots v) (length xs)))
 (il:split-flat xs (map number-of-slots (closure-values v))))

(define (il:get-bundle-values v xs)
 (assert (= (number-of-slots v) (length xs)))
 (il:split-flat xs
		(list (number-of-slots (get-bundle-primal v))
		      (number-of-slots (get-bundle-tangent v)))))

(define (il:get-vlad-pair-values v xs)
 (assert (= (number-of-slots v) (length xs)))
 (il:split-flat xs
		(list (number-of-slots (vlad-car v))
		      (number-of-slots (vlad-cdr v)))))

(define (il:get-union-values v xs)
 (assert (and (= (number-of-slots v) (length xs))
	      (not (empty-abstract-value? v))))
 (rest (il:split-flat xs (cons 1 (map number-of-slots (get-union-values v))))))

(define (il:sra-anf-convert il)
 ;; Must be called post-SRA.
 (cond
  ((il:dispatch? il)
   (il:dispatch (il:dispatch-v0 il)
		(il:dispatch-v il)
		(il:dispatch-il il)
		(map il:sra-anf-convert (il:dispatch-ils il))))
  ((il:panic? il) il)
  ((il:mv-let? il)
   (let ((vs (il:mv-let-vs il))
	 (xs (il:mv-let-xs il))
	 (il1 (il:mv-let-il1 il)))
    (assert (and (= (length xs) (length vs)) (every il:t? xs)))
    (cond
     ((il:dispatch? il1)
      (il:mv-let vs
		 xs
		 (il:dispatch (il:dispatch-v0 il1)
			      (il:dispatch-v il1)
			      (il:dispatch-il il1)
			      (map il:sra-anf-convert (il:dispatch-ils il1)))
		 (il:sra-anf-convert (il:mv-let-il2 il))))
     ((or (il:closure-ref? il1)
	  (il:perturbation-tagged-value-primal? il1)
	  (il:bundle-primal? il1)
	  (il:bundle-tangent? il1)
	  (il:sensitivity-tagged-value-primal? il1)
	  (il:reverse-tagged-value-primal? il1)
	  (il:car? il1)
	  (il:cdr? il1)
	  (il:union-ref? il1)
	  (il:construct*? il1)
	  (il:construct-union? il1)
	  (il:construct-union0? il1)
	  (il:call*? il1)
	  (il:binary? il1)
	  (il:binary-boolean? il1)
	  (il:values*? il1))
      (il:mv-let vs xs il1 (il:sra-anf-convert (il:mv-let-il2 il))))
     ;; This is needed because il:sra might yield something that is not in
     ;; ANF.
     ((il:mv-let? il1)
      (let ((vs1 (il:mv-let-vs il1)) (xs1 (il:mv-let-xs il1)))
       (assert (and (= (length xs1) (length vs1)) (every il:t? xs1)))
       ;; This transformation is sound because at this point all of the il:t in
       ;; all of the mv-let-xs must be unique.
       (il:sra-anf-convert
	(il:mv-let vs1
		   xs1
		   (il:mv-let-il1 il1)
		   (il:mv-let vs xs (il:mv-let-il2 il1) (il:mv-let-il2 il))))))
     (else (internal-error)))))
  ((il:values*? il) il)
  (else (internal-error))))

(define (instance=? instance1 instance2)
 (or (and (function-instance? instance1)
	  (function-instance? instance2)
	  (abstract-value=? (function-instance-v1 instance1)
			    (function-instance-v1 instance2))
	  (abstract-value=? (function-instance-v2 instance1)
			    (function-instance-v2 instance2)))
     (and (widener-instance? instance1)
	  (widener-instance? instance2)
	  (abstract-value=? (widener-instance-v1 instance1)
			    (widener-instance-v1 instance2))
	  (abstract-value=? (widener-instance-v2 instance1)
			    (widener-instance-v2 instance2)))
     (and (primitive-procedure-instance? instance1)
	  (primitive-procedure-instance? instance2)
	  (eq? (primitive-procedure-instance-symbol instance1)
	       (primitive-procedure-instance-symbol instance2))
	  (abstract-value=? (primitive-procedure-instance-v instance1)
			    (primitive-procedure-instance-v instance2)))
     (and (string? instance1)
	  (string? instance2)
	  (string=? instance1 instance2))))

(define (il:=? il1 il2)
 (or (and (il:c? il1) (il:c? il2))
     (and (il:x? il1) (il:x? il2))
     (and (il:y? il1) (il:y? il2))
     (and (il:z? il1) (il:z? il2))
     (and (il:t? il1) (il:t? il2) (= (il:t-index il1) (il:t-index il2)))
     (and (il:a? il1)
	  (il:a? il2)
	  (instance=? (il:a-instance il1) (il:a-instance il2))
	  (= (il:a-index il1) (il:a-index il2)))
     (and (il:r? il1)
	  (il:r? il2)
	  (instance=? (il:r-instance il1) (il:r-instance il2))
	  (= (il:r-index il1) (il:r-index il2)))
     (and (il:empty? il1)
	  (il:empty? il2)
	  (abstract-value=? (il:empty-v il1) (il:empty-v il2)))
     (and (il:tag? il1)
	  (il:tag? il2)
	  (abstract-value=? (il:tag-u il1) (il:tag-u il2))
	  (abstract-value=? (il:tag-v il1) (il:tag-v il2)))
     (and (il:constant? il1)
	  (il:constant? il2)
	  (= (il:constant-number il1) (il:constant-number il2)))
     (and (il:let? il1)
	  (il:let? il2)
	  (abstract-value=? (il:let-v il1) (il:let-v il2))
	  (il:=? (il:let-x il1) (il:let-x il2))
	  (il:=? (il:let-il1 il1) (il:let-il1 il2))
	  (il:=? (il:let-il2 il1) (il:let-il2 il2)))
     (and (il:dispatch? il1)
	  (il:dispatch? il2)
	  (abstract-value=? (il:dispatch-v0 il1) (il:dispatch-v0 il2))
	  (abstract-value=? (il:dispatch-v il1) (il:dispatch-v il2))
	  (il:=? (il:dispatch-il il1) (il:dispatch-il il2))
	  (= (length (il:dispatch-ils il1)) (length (il:dispatch-ils il2)))
	  (every il:=? (il:dispatch-ils il1) (il:dispatch-ils il2)))
     (and (il:panic? il1)
	  (il:panic? il2)
	  (string=? (il:panic-string il1) (il:panic-string il2)))
     (and (il:closure-ref? il1)
	  (il:closure-ref? il2)
	  (abstract-value=? (il:closure-ref-v il1) (il:closure-ref-v il2))
	  (il:=? (il:closure-ref-il il1) (il:closure-ref-il il2))
	  (variable=? (il:closure-ref-x il1) (il:closure-ref-x il2)))
     (and (il:perturbation-tagged-value-primal? il1)
	  (il:perturbation-tagged-value-primal? il2)
	  (abstract-value=? (il:perturbation-tagged-value-primal-v il1)
			    (il:perturbation-tagged-value-primal-v il2))
	  (il:=? (il:perturbation-tagged-value-primal-il il1)
		 (il:perturbation-tagged-value-primal-il il2)))
     (and (il:bundle-primal? il1)
	  (il:bundle-primal? il2)
	  (abstract-value=? (il:bundle-primal-v il1)
			    (il:bundle-primal-v il2))
	  (il:=? (il:bundle-primal-il il1)
		 (il:bundle-primal-il il2)))
     (and (il:bundle-tangent? il1)
	  (il:bundle-tangent? il2)
	  (abstract-value=? (il:bundle-tangent-v il1)
			    (il:bundle-tangent-v il2))
	  (il:=? (il:bundle-tangent-il il1)
		 (il:bundle-tangent-il il2)))
     (and (il:sensitivity-tagged-value-primal? il1)
	  (il:sensitivity-tagged-value-primal? il2)
	  (abstract-value=? (il:sensitivity-tagged-value-primal-v il1)
			    (il:sensitivity-tagged-value-primal-v il2))
	  (il:=? (il:sensitivity-tagged-value-primal-il il1)
		 (il:sensitivity-tagged-value-primal-il il2)))
     (and (il:reverse-tagged-value-primal? il1)
	  (il:reverse-tagged-value-primal? il2)
	  (abstract-value=? (il:reverse-tagged-value-primal-v il1)
			    (il:reverse-tagged-value-primal-v il2))
	  (il:=? (il:reverse-tagged-value-primal-il il1)
		 (il:reverse-tagged-value-primal-il il2)))
     (and (il:car? il1)
	  (il:car? il2)
	  (abstract-value=? (il:car-v il1) (il:car-v il2))
	  (il:=? (il:car-il il1) (il:car-il il2)))
     (and (il:cdr? il1)
	  (il:cdr? il2)
	  (abstract-value=? (il:cdr-v il1) (il:cdr-v il2))
	  (il:=? (il:cdr-il il1) (il:cdr-il il2)))
     (and (il:union-ref? il1)
	  (il:union-ref? il2)
	  (abstract-value=? (il:union-ref-v il1) (il:union-ref-v il2))
	  (abstract-value=? (il:union-ref-u il1) (il:union-ref-u il2))
	  (il:=? (il:union-ref-il il1) (il:union-ref-il il2)))
     (and (il:construct*? il1)
	  (il:construct*? il2)
	  (abstract-value=? (il:construct*-v il1) (il:construct*-v il2))
	  (= (length (il:construct*-ils il1)) (length (il:construct*-ils il2)))
	  (every il:=? (il:construct*-ils il1) (il:construct*-ils il2)))
     (and (il:construct-union? il1)
	  (il:construct-union? il2)
	  (abstract-value=?
	   (il:construct-union-u il1) (il:construct-union-u il2))
	  (abstract-value=?
	   (il:construct-union-v il1) (il:construct-union-v il2))
	  (il:=? (il:construct-union-il il1) (il:construct-union-il il2)))
     (and (il:construct-union0? il1)
	  (il:construct-union0? il2)
	  (abstract-value=?
	   (il:construct-union0-u il1) (il:construct-union0-u il2))
	  (abstract-value=?
	   (il:construct-union0-v il1) (il:construct-union0-v il2)))
     (and (il:call*? il1)
	  (il:call*? il2)
	  (instance=? (il:call*-instance il1) (il:call*-instance il2))
	  (= (length (il:call*-ils il1)) (length (il:call*-ils il2)))
	  (every il:=? (il:call*-ils il1) (il:call*-ils il2)))
     (and (il:binary? il1)
	  (il:binary? il2)
	  (il:=? (il:binary-il1 il1) (il:binary-il1 il2))
	  (string=? (il:binary-string il1) (il:binary-string il2))
	  (il:=? (il:binary-il2 il1) (il:binary-il2 il2)))
     (and (il:binary-boolean? il1)
	  (il:binary-boolean? il2)
	  (il:=? (il:binary-boolean-il1 il1) (il:binary-boolean-il1 il2))
	  (string=? (il:binary-boolean-string il1)
		    (il:binary-boolean-string il2))
	  (il:=? (il:binary-boolean-il2 il1) (il:binary-boolean-il2 il2)))
     (and (il:mv-let? il1)
	  (il:mv-let? il2)
	  (= (length (il:mv-let-vs il1)) (length (il:mv-let-vs il2)))
	  (every abstract-value=? (il:mv-let-vs il1) (il:mv-let-vs il2))
	  (= (length (il:mv-let-xs il1)) (length (il:mv-let-xs il2)))
	  (every il:=? (il:mv-let-xs il1) (il:mv-let-xs il2))
	  (il:=? (il:mv-let-il1 il1) (il:mv-let-il1 il2))
	  (il:=? (il:mv-let-il2 il1) (il:mv-let-il2 il2)))
     (and (il:values*? il1)
	  (il:values*? il2)
	  (abstract-value=? (il:values*-v il1) (il:values*-v il2))
	  (= (length (il:values*-ils il1)) (length (il:values*-ils il2)))
	  (every il:=? (il:values*-ils il1) (il:values*-ils il2)))
     (and (variable? il1) (variable? il2) (variable=? il1 il2))))

(define (il:remove-trivial-dispatches il)
 ;; Must be called post-SRA.
 (profile
  "~a il:remove-trivial-dispatches~%"
  (lambda ()
   (let loop ((il il))
    (cond
     ((il:dispatch? il)
      (cond
       ((and
	 (tag? (il:dispatch-v il))
	 (abstract-value=? (tag-abstract-value (il:dispatch-v il))
			   (abstract-boolean))
	 (= (length (il:dispatch-ils il)) 2)
	 (il:values*? (first (il:dispatch-ils il)))
	 (= (length (il:values*-ils (first (il:dispatch-ils il)))) 1)
	 (il:tag? (first (il:values*-ils (first (il:dispatch-ils il)))))
	 (eq? (il:tag-u (first (il:values*-ils (first (il:dispatch-ils il)))))
	      #t)
	 (abstract-value=?
	  (il:tag-v (first (il:values*-ils (first (il:dispatch-ils il)))))
	  (abstract-boolean))
	 (il:values*? (second (il:dispatch-ils il)))
	 (= (length (il:values*-ils (second (il:dispatch-ils il)))) 1)
	 (il:tag? (first (il:values*-ils (second (il:dispatch-ils il)))))
	 (eq? (il:tag-u (first (il:values*-ils (second (il:dispatch-ils il)))))
	      #f)
	 (abstract-value=?
	  (il:tag-v (first (il:values*-ils (second (il:dispatch-ils il)))))
	  (abstract-boolean)))
	(il:values (il:dispatch-v il) (il:dispatch-il il)))
       ;; This might unsoundly remove code that might do I/O, panic, signal an
       ;; error, or not terminate.
       ((every (lambda (il1) (il:=? il1 (first (il:dispatch-ils il))))
	       (il:dispatch-ils il))
	(first (il:dispatch-ils il)))
       (else
	(il:dispatch (il:dispatch-v0 il)
		     (il:dispatch-v il)
		     (il:dispatch-il il)
		     (map loop (il:dispatch-ils il))))))
     ((il:panic? il) il)
     ((il:mv-let? il)
      (let ((vs (il:mv-let-vs il))
	    (xs (il:mv-let-xs il))
	    (il1 (il:mv-let-il1 il)))
       (assert (and (= (length xs) (length vs)) (every il:t? xs)))
       (cond
	((il:dispatch? il1)
	 ;; This might unsoundly remove code that might do I/O, panic, signal
	 ;; an error, or not terminate.
	 (if (and
	      (every (lambda (il2) (il:=? il2 (first (il:dispatch-ils il1))))
		     (il:dispatch-ils il1))
	      (il:panic? (first (il:dispatch-ils il1))))
	     (first (il:dispatch-ils il1))
	     (il:mv-let
	      vs
	      xs
	      (cond
	       ((and
		 (tag? (il:dispatch-v il1))
		 (abstract-value=? (tag-abstract-value (il:dispatch-v il1))
				   (abstract-boolean))
		 (= (length (il:dispatch-ils il1)) 2)
		 (il:values*? (first (il:dispatch-ils il1)))
		 (= (length (il:values*-ils (first (il:dispatch-ils il1)))) 1)
		 (il:tag?
		  (first (il:values*-ils (first (il:dispatch-ils il1)))))
		 (eq? (il:tag-u
		       (first (il:values*-ils (first (il:dispatch-ils il1)))))
		      #t)
		 (abstract-value=?
		  (il:tag-v
		   (first (il:values*-ils (first (il:dispatch-ils il1)))))
		  (abstract-boolean))
		 (il:values*? (second (il:dispatch-ils il1)))
		 (= (length (il:values*-ils (second (il:dispatch-ils il1)))) 1)
		 (il:tag?
		  (first (il:values*-ils (second (il:dispatch-ils il1)))))
		 (eq? (il:tag-u
		       (first (il:values*-ils (second (il:dispatch-ils il1)))))
		      #f)
		 (abstract-value=?
		  (il:tag-v
		   (first (il:values*-ils (second (il:dispatch-ils il1)))))
		  (abstract-boolean)))
		(il:values (il:dispatch-v il1) (il:dispatch-il il1)))
	       ;; This might unsoundly remove code that might do I/O, panic,
	       ;; signal an error, or not terminate.
	       ((every (lambda (il2) (il:=? il2 (first (il:dispatch-ils il1))))
		       (il:dispatch-ils il1))
		(first (il:dispatch-ils il1)))
	       (else (il:dispatch
		      (il:dispatch-v0 il1)
		      (il:dispatch-v il1)
		      (il:dispatch-il il1)
		      (map loop (il:dispatch-ils il1)))))
	      (loop (il:mv-let-il2 il)))))
	((or (il:closure-ref? il1)
	     (il:perturbation-tagged-value-primal? il1)
	     (il:bundle-primal? il1)
	     (il:bundle-tangent? il1)
	     (il:sensitivity-tagged-value-primal? il1)
	     (il:reverse-tagged-value-primal? il1)
	     (il:car? il1)
	     (il:cdr? il1)
	     (il:union-ref? il1)
	     (il:construct*? il1)
	     (il:construct-union? il1)
	     (il:construct-union0? il1)
	     (il:call*? il1)
	     (il:binary? il1)
	     (il:binary-boolean? il1)
	     (il:values*? il1))
	 (il:mv-let vs xs il1 (loop (il:mv-let-il2 il))))
	(else (internal-error)))))
     ((il:values*? il) il)
     (else (internal-error)))))))

(define (il:multiply-out-dispatches il)
 ;; Must be called post-SRA.
 ;; (mv-let ((x (dispatch p e1 ... en))) e) -~->
 ;; (dispatch p (mv-let ((x e1)) e) ... (mv-let ((x en)) e))
 (cond
  ((il:dispatch? il)
   (il:dispatch (il:dispatch-v0 il)
		(il:dispatch-v il)
		(il:dispatch-il il)
		(map il:multiply-out-dispatches (il:dispatch-ils il))))
  ((il:panic? il) il)
  ((il:mv-let? il)
   (let ((vs (il:mv-let-vs il))
	 (xs (il:mv-let-xs il))
	 (il1 (il:mv-let-il1 il)))
    (assert (and (= (length xs) (length vs)) (every il:t? xs)))
    (cond
     ((il:dispatch? il1)
      (il:dispatch
       (il:dispatch-v0 il1)
       (il:dispatch-v il1)
       (il:dispatch-il il1)
       (map (lambda (il2)
	     (if (il:panic? il2)
		 il2
		 (il:multiply-out-dispatches
		  (il:sra-anf-convert
		   (il:mv-let vs xs il2 (il:mv-let-il2 il))))))
	    (il:dispatch-ils il1))))
     ((or (il:closure-ref? il1)
	  (il:perturbation-tagged-value-primal? il1)
	  (il:bundle-primal? il1)
	  (il:bundle-tangent? il1)
	  (il:sensitivity-tagged-value-primal? il1)
	  (il:reverse-tagged-value-primal? il1)
	  (il:car? il1)
	  (il:cdr? il1)
	  (il:union-ref? il1)
	  (il:construct*? il1)
	  (il:construct-union? il1)
	  (il:construct-union0? il1)
	  (il:call*? il1)
	  (il:binary? il1)
	  (il:binary-boolean? il1)
	  (il:values*? il1))
      (il:mv-let vs xs il1 (il:multiply-out-dispatches (il:mv-let-il2 il))))
     (else (internal-error)))))
  ((il:values*? il) il)
  (else (internal-error))))

(define (il:multiplying-out-cost il)
 ;; Must be called post-SRA.
 (cond
  ((il:dispatch? il)
   (map-reduce + 0.0 il:multiplying-out-cost (il:dispatch-ils il)))
  ((il:panic? il) 0.0)
  ((il:mv-let? il)
   (let ((vs (il:mv-let-vs il))
	 (xs (il:mv-let-xs il))
	 (il1 (il:mv-let-il1 il)))
    (assert (and (= (length xs) (length vs)) (every il:t? xs)))
    (cond ((il:dispatch? il1)
	   (* (map-reduce + 0.0 il:multiplying-out-cost (il:dispatch-ils il1))
	      (il:multiplying-out-cost (il:mv-let-il2 il))))
	  ((or (il:closure-ref? il1)
	       (il:perturbation-tagged-value-primal? il1)
	       (il:bundle-primal? il1)
	       (il:bundle-tangent? il1)
	       (il:sensitivity-tagged-value-primal? il1)
	       (il:reverse-tagged-value-primal? il1)
	       (il:car? il1)
	       (il:cdr? il1)
	       (il:union-ref? il1)
	       (il:construct*? il1)
	       (il:construct-union? il1)
	       (il:construct-union0? il1)
	       (il:call*? il1)
	       (il:binary? il1)
	       (il:binary-boolean? il1)
	       (il:values*? il1))
	   (il:multiplying-out-cost (il:mv-let-il2 il)))
	  (else (internal-error)))))
  ((il:values*? il) 1.0)
  (else (internal-error))))

(define (il:maybe-multiply-out-dispatches il)
 (profile "~a il:maybe-multiply-out-dispatches~%"
	  (lambda ()
	   (if (or (not *il:multiply-out-dispatches-cost-limit*)
		   (<= (il:multiplying-out-cost il)
		       *il:multiply-out-dispatches-cost-limit*))
	       (il:multiply-out-dispatches il)
	       il))))

(define (il:sra il bs)
 (il:copy-propagate
  (il:maybe-multiply-out-dispatches
   (il:remove-trivial-dispatches
    (il:copy-propagate
     (il:sra-anf-convert
      (profile
       "~a il:sra~%"
       (lambda ()
	(let loop ((il il) (bs bs))
	 (define (lookup il) (let ((b (assq il bs))) (assert b) b))
	 (cond
	  ((il:let? il)
	   (let ((il1 (il:let-il1 il))
		 (b (list (il:let-x il)
			  (il:let-v il)
			  (slots (il:let-v il))
			  (il:flatten (il:let-v il)))))
	    (il:mv-let
	     (third b)
	     (fourth b)
	     (cond
	      ((il:c? il1)
	       (let ((b (lookup il1))) (il:values* (second b) (fourth b))))
	      ((il:x? il1)
	       (let ((b (lookup il1))) (il:values* (second b) (fourth b))))
	      ((il:t? il1)
	       (let ((b (lookup il1))) (il:values* (second b) (fourth b))))
	      ((il:empty? il1)
	       (il:values*
		(second b) (map (lambda (v) (il:empty v)) (third b))))
	      ((il:tag? il1) (il:values (second b) il1))
	      ((il:constant? il1) (il:values (second b) il1))
	      ((il:dispatch? il1)
	       (let ((b (lookup (il:dispatch-il il1))))
		(assert (or (not (boxed? (il:dispatch-v il1)))
			    (= (length (third b)) 1)))
		(il:dispatch
		 (il:dispatch-v0 il1)
		 (first (third b))
		 (first (fourth b))
		 (map (lambda (il) (loop il bs)) (il:dispatch-ils il1)))))
	      ((il:closure-ref? il1)
	       (let ((b (lookup (il:closure-ref-il il1))))
		(cond
		 ((boxed? (il:closure-ref-v il1))
		  (assert (= (length (third b)) 1))
		  (il:closure-ref (first (third b))
				  (first (fourth b))
				  (il:closure-ref-x il1)))
		 (else
		  (il:values*
		   (closure-ref (second b) (il:closure-ref-x il1))
		   (list-ref
		    (il:get-closure-values (second b) (fourth b))
		    (positionp
		     variable=?
		     (il:closure-ref-x il1)
		     (closure-variables (il:closure-ref-v il1)))))))))
	      ((il:perturbation-tagged-value-primal? il1)
	       (let ((b (lookup (il:perturbation-tagged-value-primal-il il1))))
		(cond ((boxed? (il:perturbation-tagged-value-primal-v il1))
		       (assert (= (length (third b)) 1))
		       (il:perturbation-tagged-value-primal
			(first (third b)) (first (fourth b))))
		      (else (il:values* (second b) (fourth b))))))
	      ((il:bundle-primal? il1)
	       (let ((b (lookup (il:bundle-primal-il il1))))
		(cond
		 ((boxed? (il:bundle-primal-v il1))
		  (assert (= (length (third b)) 1))
		  (il:bundle-primal (first (third b)) (first (fourth b))))
		 (else
		  (il:values*
		   (get-bundle-primal (second b))
		   (first (il:get-bundle-values (second b) (fourth b))))))))
	      ((il:bundle-tangent? il1)
	       (let ((b (lookup (il:bundle-tangent-il il1))))
		(cond
		 ((boxed? (il:bundle-tangent-v il1))
		  (assert (= (length (third b)) 1))
		  (il:bundle-tangent (first (third b)) (first (fourth b))))
		 (else
		  (il:values*
		   (get-bundle-tangent (second b))
		   (second (il:get-bundle-values (second b) (fourth b))))))))
	      ((il:sensitivity-tagged-value-primal? il1)
	       (let ((b (lookup (il:sensitivity-tagged-value-primal-il il1))))
		(cond ((boxed? (il:sensitivity-tagged-value-primal-v il1))
		       (assert (= (length (third b)) 1))
		       (il:sensitivity-tagged-value-primal
			(first (third b)) (first (fourth b))))
		      (else (il:values* (second b) (fourth b))))))
	      ((il:reverse-tagged-value-primal? il1)
	       (let ((b (lookup (il:reverse-tagged-value-primal-il il1))))
		(cond ((boxed? (il:reverse-tagged-value-primal-v il1))
		       (assert (= (length (third b)) 1))
		       (il:reverse-tagged-value-primal
			(first (third b)) (first (fourth b))))
		      (else (il:values* (second b) (fourth b))))))
	      ((il:car? il1)
	       (let ((b (lookup (il:car-il il1))))
		(cond ((boxed? (il:car-v il1))
		       (assert (= (length (third b)) 1))
		       (il:car (first (third b)) (first (fourth b))))
		      (else
		       (il:values*
			(vlad-car (second b))
			(first
			 (il:get-vlad-pair-values (second b) (fourth b))))))))
	      ((il:cdr? il1)
	       (let ((b (lookup (il:cdr-il il1))))
		(cond ((boxed? (il:cdr-v il1))
		       (assert (= (length (third b)) 1))
		       (il:cdr (first (third b)) (first (fourth b))))
		      (else
		       (il:values*
			(vlad-cdr (second b))
			(second
			 (il:get-vlad-pair-values (second b) (fourth b))))))))
	      ((il:union-ref? il1)
	       (let ((b (lookup (il:union-ref-il il1))))
		(cond
		 ((boxed? (il:union-ref-v il1))
		  (assert (= (length (third b)) 1))
		  (il:union-ref
		   (first (third b)) (il:union-ref-u il1) (first (fourth b))))
		 (else
		  (il:values*
		   (il:union-ref-u il1)
		   (list-ref
		    (il:get-union-values (second b) (fourth b))
		    (positionq (il:union-ref-u il1)
			       (get-union-values (il:union-ref-v il1)))))))))
	      ((il:construct*? il1)
	       (if (boxed? (il:construct*-v il1))
		   (make-il:construct*
		    (il:construct*-v il1)
		    (reduce append
			    (map (lambda (il) (fourth (lookup il)))
				 (il:construct*-ils il1))
			    '()))
		   (il:values* (il:construct*-v il1)
			       (reduce append
				       (map (lambda (il) (fourth (lookup il)))
					    (il:construct*-ils il1))
				       '()))))
	      ((il:construct-union? il1)
	       (if (boxed? (il:construct-union-v il1))
		   (il:construct-union
		    (il:construct-union-u il1)
		    (il:construct-union-v il1)
		    (il:values* (il:construct-union-u il1)
				(fourth (lookup (il:construct-union-il il1)))))
		   (il:values*
		    (il:construct-union-v il1)
		    (cons
		     (il:tag (il:construct-union-u il1)
			     (il:construct-union-v il1))
		     (reduce
		      append
		      (map
		       (lambda (u1)
			(if (abstract-value=? u1 (il:construct-union-u il1))
			    (fourth (lookup (il:construct-union-il il1)))
			    (map il:empty (slots u1))))
		       (get-union-values (il:construct-union-v il1)))
		      '())))))
	      ((il:construct-union0? il1)
	       (if (boxed? (il:construct-union0-v il1))
		   il1
		   (il:values*
		    (il:construct-union0-v il1)
		    (cons
		     (il:tag (il:construct-union0-u il1)
			     (il:construct-union0-v il1))
		     (reduce
		      append
		      (map
		       (lambda (u1)
			(if (abstract-value=? u1 (il:construct-union0-u il1))
			    '()
			    (map il:empty (slots u1))))
		       (get-union-values (il:construct-union0-v il1)))
		      '())))))
	      ((il:call*? il1)
	       (make-il:call* (il:call*-instance il1)
			      (reduce append
				      (map (lambda (il) (fourth (lookup il)))
					   (il:call*-ils il1))
				      '())))
	      ((il:binary? il1)
	       (il:binary (let ((b (lookup (il:binary-il1 il1))))
			   (assert (= (length (third b)) 1))
			   (first (fourth b)))
			  (il:binary-string il1)
			  (let ((b (lookup (il:binary-il2 il1))))
			   (assert (= (length (third b)) 1))
			   (first (fourth b)))))
	      ((il:binary-boolean? il1)
	       (il:binary-boolean
		(let ((b (lookup (il:binary-boolean-il1 il1))))
		 (assert (= (length (third b)) 1))
		 (first (fourth b)))
		(il:binary-boolean-string il1)
		(let ((b (lookup (il:binary-boolean-il2 il1))))
		 (assert (= (length (third b)) 1))
		 (first (fourth b)))))
	      (else (internal-error)))
	     (loop (il:let-il2 il) (cons b bs)))))
	  ((il:dispatch? il)
	   (let ((b (lookup (il:dispatch-il il))))
	    (assert (or (not (boxed? (il:dispatch-v il)))
			(= (length (third b)) 1)))
	    (il:dispatch
	     (il:dispatch-v0 il)
	     (first (third b))
	     (first (fourth b))
	     (map (lambda (il) (loop il bs)) (il:dispatch-ils il)))))
	  ((il:panic? il) il)
	  (else (let ((b (lookup il)))
		 (il:values* (second b) (fourth b))))))))))))))

;;; Primitive C syntax generators

(define (c:variable-name x) (string-append "x" (number->string (c:index x))))

(define (c:descr v) (string-append "descr" (number->string (c:index v))))

(define (c:bitmap v) (string-append "bitmap" (number->string (c:index v))))

(define (c:argument-variable-name instance i)
 (list "a" "_" (c:instance-name instance) "_" i))

(define (c:return-variable-name instance i)
 (list "r" "_" (c:instance-name instance) "_" i))

(define (c:null) "NULL")

;;; This uses per-union tags here instead of per-program tags.
(define (c:tag u v) (positionp abstract-value=? u (get-union-values v)))

(define (c:member-name v) (list "s" (c:index v)))

(define (c:sra-member-name i) (list "q" i))

(define (c:constructor-name v) (list "m" (c:index v)))

(define (c:unioner-name u v) (list "m" (c:index v) "_" (c:index u)))

(define (c:parenthesize . codes) (list "(" codes ")"))

(define (c:braces-around . codes)
 (if *sra?* (list "{" #\newline codes "}" #\newline) (list "{" codes "}")))

(define (c:no-newline-braces-around . codes)
 (if *sra?* (list "{" #\newline codes "}") (list "{" codes "}")))

(define (c:semicolon-after . codes)
 (if *sra?* (list codes ";" #\newline) (list codes ";")))

(define (c:newline-after . codes) (list codes #\newline))

(define (c:nonsra-newline-after . codes)
 (if *sra?* codes (list codes #\newline)))

(define (c:parameter code1 code2) (list code1 " " code2))

(define (c:pointer-declarator code) (list "*" code))

(define (c:function-declarator* code codes)
 (list
  code
  (c:parenthesize
   (let ((codes (removeq '() codes)))
    (cond
     ((null? codes) "void")
     ((null? (rest codes)) (first codes))
     (else
      (reduce (lambda (code1 code2) (list code1 "," code2)) codes '())))))))

(define (c:declaration code1 code2) (c:semicolon-after code1 " " code2))

(define (c:static-declaration code1 code2)
 (c:semicolon-after "static" " " code1 " " code2))

(define (c:init-declaration code1 code2 code3)
 (c:semicolon-after code1 " " code2 "=" code3))

(define (c:specifier v)
 (assert (not (void? v)))
 (cond ((and (not (union? v)) (abstract-real? v)) "double")
       ((tag? v) "int")
       (else (list "struct" " " (c:member-name v)))))

(define (c:conditional code1 code2 code3)
 (c:parenthesize code1 "?" code2 ":" code3))

(define (c:binary code1 code2 code3) (c:parenthesize (list code1 code2 code3)))

(define (c:subscript code1 code2) (list code1 "[" code2 "]"))

(define (c:slot v code1 code2)
 (if (void? v) 'error (c:binary code1 (if (boxed? v) "->" ".") code2)))

(define (c:sra-slot code i) (c:binary code "->" (c:sra-member-name i)))

(define (c:tag-slot v code)
 (assert (union? v))
 (c:slot v code "t"))

(define (c:let v code1 code2 code3)
 (c:statement-expression (c:specifier-init-declaration v "u" code2)
			 (c:specifier-init-declaration v code1 "u")
			 code3))

(define (c:unboxed-dispatch code codes)
 ;; This uses per-union tags here instead of per-program tags.
 ;; It would be better to use a switch but while there are conditional
 ;; expressions in C, there are no switch expressions. We could use the GNU C
 ;; statement expression extension. In the case of conditional expressions, we
 ;; could optimize the order (by profiling or static analysis). In the case of
 ;; a switch, could optimize the choice of which case becomes the default.
 (let loop ((codes codes) (i 0))
  (if (null? (rest codes))
      (first codes)
      (c:conditional
       (c:binary code "==" i) (first codes) (loop (rest codes) (+ i 1))))))

(define (c:null? code)
 (or (null? code)
     (and (pair? code) (c:null? (car code)) (c:null? (cdr code)))))

(define (c:dispatch-statement code codes)
 ;; This uses per-union tags here instead of per-program tags.
 ;; It would be better to use a switch but while there are conditional
 ;; expressions in C, there are no switch expressions. We could use the GNU C
 ;; statement expression extension. In the case of conditional expressions, we
 ;; could optimize the order (by profiling or static analysis). In the case of
 ;; a switch, could optimize the choice of which case becomes the default.
 (cond
  ((every c:null? codes) '())
  ((every (lambda (code) (equal? code (first codes))) codes) (first codes))
  (else (let loop ((codes codes) (i 0))
	 (if (null? (rest codes))
	     (first codes)
	     (c:if (c:binary code "==" i)
		   (c:braces-around (first codes))
		   (c:braces-around (loop (rest codes) (+ i 1)))))))))

(define (c:call* code codes)
 (list
  code
  (c:parenthesize
   (let ((codes (removeq '() codes)))
    (cond
     ((null? codes) '())
     ((null? (rest codes)) (first codes))
     (else
      (reduce (lambda (code1 code2) (list code1 "," code2)) codes '())))))))

(define (c:call code . codes) (c:call* code codes))

(define (c:panic code) (c:call "panic" (list "\"" code "\"")))

(define (c:closure-ref v code x)
 (if (void? (closure-ref v x)) '() (c:slot v code (c:variable-name x))))

(define (c:perturbation-tagged-value-primal v code)
 (if (void? (get-perturbation-tagged-value-primal v))
     '()
     (c:slot v code "p")))

(define (c:bundle-primal v code)
 (if (void? (get-bundle-primal v)) '() (c:slot v code "p")))

(define (c:bundle-tangent v code)
 (if (void? (get-bundle-tangent v)) '() (c:slot v code "t")))

(define (c:sensitivity-tagged-value-primal v code)
 (if (void? (get-sensitivity-tagged-value-primal v)) '() (c:slot v code "p")))

(define (c:reverse-tagged-value-primal v code)
 (if (void? (get-reverse-tagged-value-primal v)) '() (c:slot v code "p")))

(define (c:car v code) (if (void? (vlad-car v)) '() (c:slot v code "a")))

(define (c:cdr v code) (if (void? (vlad-cdr v)) '() (c:slot v code "d")))

(define (c:union-ref v u code)
 (assert (union? v))
 ;; The union is always unboxed.
 (if (void? u) '() (c:binary (c:slot v code "u") "." (c:member-name u))))

(define (c:sizeof code) (list "sizeof" (c:parenthesize code)))

(define (c:pointer-cast code1 code2)
 (list (c:parenthesize (list code1 " " "*")) code2))

(define (c:function-declaration p1? p2? p3? p4? code1 code2)
 (c:nonsra-newline-after
  (c:semicolon-after (if p1? (list "static" " ") '())
		     (if p2? (list "INLINE" " ") '())
		     (if p3? (list "NORETURN" " ") '())
		     code1
		     " "
		     (if p4? (c:pointer-declarator code2) code2))))

(define (c:assignment code1 code2) (c:semicolon-after code1 "=" code2))

(define (c:if code1 code2 code3)
 (list "if" (c:parenthesize code1) code2 " " "else" " " code3))

(define (c:return code) (c:semicolon-after "return" " " code))

(define (c:statement-function-definition p1? p2? p3? p4? code1 code2 code3)
 (c:nonsra-newline-after (if p1? (list "static" " ") '())
			 (if p2? (list "INLINE" " ") '())
			 (if p3? (list "NORETURN" " ") '())
			 code1
			 " "
			 (if p4? (c:pointer-declarator code2) code2)
			 (c:braces-around code3)))

(define (c:function-definition p1? p2? p3? p4? code1 code2 code3)
 (c:nonsra-newline-after (if p1? (list "static" " ") '())
			 (if p2? (list "INLINE" " ") '())
			 (if p3? (list "NORETURN" " ") '())
			 code1
			 " "
			 (if p4? (c:pointer-declarator code2) code2)
			 (c:braces-around (if p3? code3 (c:return code3)))))

(define (c:generate-slot-names v)
 (cond ((nonrecursive-closure? v)
	(map c:variable-name (nonrecursive-closure-variables v)))
       ((recursive-closure? v)
	(map c:variable-name (recursive-closure-variables v)))
       ((perturbation-tagged-value? v) '("p"))
       ((bundle? v) '("p" "t"))
       ((sensitivity-tagged-value? v) '("p"))
       ((reverse-tagged-value? v) '("p"))
       ((vlad-pair? v) '("a" "d"))
       (else (internal-error))))

(define (c:generate-member-names v) (map c:member-name (get-union-values v)))

(define (c:instance-name instance)
 (cond ((string? instance) instance)
       ((function-instance? instance)
	(string-append "f" (number->string (c:index instance))))
       ((widener-instance? instance)
	(string-append "w" (number->string (c:index instance))))
       ((primitive-procedure-instance? instance)
	(string-append (primitive-procedure-c:name
			(lookup-primitive-procedure
			 (primitive-procedure-instance-symbol instance)))
		       (number->string (c:index instance))))
       (else (internal-error))))

;;; Derived C syntax generators

(define (c:specifier-parameter v code)
 (if (void? v)
     '()
     (c:parameter (c:specifier v)
		  (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:function-declarator code . codes)
 (c:function-declarator* code codes))

(define (c:specifier-declaration v code)
 (if (void? v)
     '()
     (c:declaration (c:specifier v)
		    (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:static-specifier-declaration v code)
 (if (void? v)
     '()
     (c:static-declaration (c:specifier v)
			   (if (boxed? v) (c:pointer-declarator code) code))))

(define (c:specifier-init-declaration v code1 code2)
 (if (void? v)
     '()
     (c:init-declaration (c:specifier v)
			 (if (boxed? v) (c:pointer-declarator code1) code1)
			 code2)))

(define (c:dispatch v code codes)
 (assert (and (= (length (get-union-values v)) (length codes))
	      (>= (length (get-union-values v)) 2)))
 ;; The type tag is always unboxed.
 (c:unboxed-dispatch (c:tag-slot v code) codes))

(define (c:statement-expression . codes)
 (c:parenthesize (c:no-newline-braces-around (c:semicolon-after codes))))

(define (c:specifier-function-declaration p1? p2? p3? v code)
 (if (void? v)
     '()
     (c:function-declaration p1? p2? p3? (boxed? v) (c:specifier v) code)))

(define (c:specifier-function-definition p1? p2? p3? v code1 code2)
 (if (void? v)
     '()
     (c:function-definition
      p1? p2? p3? (boxed? v) (c:specifier v) code1 code2)))

(define (c:generate-slots v)
 (cond
  ((nonrecursive-closure? v)
   (map (lambda (x) (lambda (v code) (c:closure-ref v code x)))
	(nonrecursive-closure-variables v)))
  ((recursive-closure? v)
   (map (lambda (x) (lambda (v code) (c:closure-ref v code x)))
	(recursive-closure-variables v)))
  ((perturbation-tagged-value? v) (list c:perturbation-tagged-value-primal))
  ((bundle? v) (list c:bundle-primal c:bundle-tangent))
  ((sensitivity-tagged-value? v) (list c:sensitivity-tagged-value-primal))
  ((reverse-tagged-value? v) (list c:reverse-tagged-value-primal))
  ((vlad-pair? v) (list c:car c:cdr))
  (else (internal-error))))

(define (c:generate-members v)
 (map (lambda (u) (lambda (v code) (c:union-ref v u code)))
      (get-union-values v)))

;;; C-code generator

(define (c:generate-il v il)
 (cond
  ((il:c? il) "c")
  ((il:x? il) "x")
  ((il:y? il) "y")
  ((il:z? il) "z")
  ((il:t? il) (list "t" (il:t-index il)))
  ((il:a? il) (c:argument-variable-name (il:a-instance il) (il:a-index il)))
  ((il:r? il) (c:return-variable-name (il:r-instance il) (il:r-index il)))
  ((il:empty? il)
   (c:statement-expression (c:specifier-declaration (il:empty-v il) "r") "r"))
  ((il:tag? il) (c:tag (il:tag-u il) (il:tag-v il)))
  ;; This assumes that Scheme inexact numbers are printed as C doubles.
  ((il:constant? il) (exact->inexact (il:constant-number il)))
  ((il:let? il)
   (assert (not (void? (il:let-v il))))
   (c:let (il:let-v il)
	  (c:generate-il 'error (il:let-x il))
	  (c:generate-il (il:let-v il) (il:let-il1 il))
	  (c:generate-il v (il:let-il2 il))))
  ((il:dispatch? il)
   (c:dispatch (il:dispatch-v il)
	       (c:generate-il (il:dispatch-v il) (il:dispatch-il il))
	       (let ((v (il:dispatch-v0 il)))
		(map (lambda (il) (c:generate-il v il))
		     (il:dispatch-ils il)))))
  ((il:panic? il)
   (c:statement-expression
    ;; This is the whole reason for the v argument to c:generate-il.
    (c:specifier-declaration v "r")
    (c:semicolon-after (c:panic (il:panic-string il)))
    "r"))
  ((il:closure-ref? il)
   (c:closure-ref
    (il:closure-ref-v il)
    (c:generate-il (il:closure-ref-v il) (il:closure-ref-il il))
    (il:closure-ref-x il)))
  ((il:perturbation-tagged-value-primal? il)
   (c:perturbation-tagged-value-primal
    (il:perturbation-tagged-value-primal-v il)
    (c:generate-il (il:perturbation-tagged-value-primal-v il)
		   (il:perturbation-tagged-value-primal-il il))))
  ((il:bundle-primal? il)
   (c:bundle-primal (il:bundle-primal-v il)
		    (c:generate-il (il:bundle-primal-v il)
				   (il:bundle-primal-il il))))
  ((il:bundle-tangent? il)
   (c:bundle-tangent (il:bundle-tangent-v il)
		     (c:generate-il (il:bundle-tangent-v il)
				    (il:bundle-tangent-il il))))
  ((il:sensitivity-tagged-value-primal? il)
   (c:sensitivity-tagged-value-primal
    (il:sensitivity-tagged-value-primal-v il)
    (c:generate-il (il:sensitivity-tagged-value-primal-v il)
		   (il:sensitivity-tagged-value-primal-il il))))
  ((il:reverse-tagged-value-primal? il)
   (c:reverse-tagged-value-primal
    (il:reverse-tagged-value-primal-v il)
    (c:generate-il (il:reverse-tagged-value-primal-v il)
		   (il:reverse-tagged-value-primal-il il))))
  ((il:car? il)
   (c:car (il:car-v il) (c:generate-il (il:car-v il) (il:car-il il))))
  ((il:cdr? il)
   (c:cdr (il:cdr-v il) (c:generate-il (il:cdr-v il) (il:cdr-il il))))
  ((il:union-ref? il)
   (c:union-ref (il:union-ref-v il)
		(il:union-ref-u il)
		(c:generate-il (il:union-ref-v il) (il:union-ref-il il))))
  ((il:construct*? il)
   (assert (not (void? (il:construct*-v il))))
   (c:call* (c:constructor-name (il:construct*-v il))
	    (map c:generate-il
		 (remove-if void?
			    (aggregate-value-values (il:construct*-v il)))
		 (il:construct*-ils il))))
  ((il:construct-union? il)
   (assert (and (not (void? (il:construct-union-u il)))
		(not (void? (il:construct-union-v il)))))
   (c:call
    (c:unioner-name (il:construct-union-u il)
		    (il:construct-union-v il))
    (c:generate-il (il:construct-union-u il) (il:construct-union-il il))))
  ((il:construct-union0? il)
   (assert (and (void? (il:construct-union0-u il))
		(not (void? (il:construct-union0-v il)))))
   (c:call (c:unioner-name (il:construct-union0-u il)
			   (il:construct-union0-v il))))
  ((il:call*? il)
   (c:call* (c:instance-name (il:call*-instance il))
	    (map c:generate-il
		 (remove-if void?
			    (instance-argument-values (il:call*-instance il)))
		 (il:call*-ils il))))
  ((il:binary? il)
   (c:binary (c:generate-il (abstract-real) (il:binary-il1 il))
	     (il:binary-string il)
	     (c:generate-il (abstract-real) (il:binary-il2 il))))
  ((il:binary-boolean? il)
   (c:conditional (c:binary (c:generate-il (abstract-real)
					   (il:binary-boolean-il1 il))
			    (il:binary-boolean-string il)
			    (c:generate-il (abstract-real)
					   (il:binary-boolean-il2 il)))
		  (c:call (c:unioner-name (vlad-true) (abstract-boolean)))
		  (c:call (c:unioner-name (vlad-false) (abstract-boolean)))))
  ((variable? il) (c:variable-name il))
  (else (internal-error))))

(define (c:sra-generate-variable il)
 (assert (or (il:t? il) (il:a? il) (il:r? il)))
 (c:generate-il 'error il))

(define (c:sra-generate-variable-or-constant il)
 (assert (or (il:t? il) (il:a? il) (il:r? il) (il:constant? il)))
 (c:generate-il 'error il))

(define (c:sra-generate-variable-or-tag il)
 (assert (or (il:t? il) (il:a? il) (il:r? il) (il:tag? il)))
 (c:generate-il 'error il))

(define (c:sra-generate-variable-tag-or-constant il)
 (assert (or (il:t? il) (il:a? il) (il:r? il) (il:tag? il) (il:constant? il)))
 (c:generate-il 'error il))

(define (c:sra-generate-variable-empty-tag-or-constant il)
 (assert (or (il:t? il)
	     (il:a? il)
	     (il:r? il)
	     (il:empty? il)
	     (il:tag? il)
	     (il:constant? il)))
 (c:generate-il 'error il))

(define (singleton-return-value? instance)
 (if (and *alias?* (not (inline? instance)))
     (one (lambda (color) (not (color-pointer color))) (output-alias instance))
     (= (number-of-slots (instance-return-value instance)) 1)))

(define (singleton-return-variable-name instance)
 (c:return-variable-name
  instance
  (if (and *alias?* (not (inline? instance)))
      (color-index-of
       (list-ref (output-alias instance)
		 (position-if-not color-pointer (output-alias instance))))
      0)))

(define (singleton-return-value instance)
 (if (and *alias?* (not (inline? instance)))
     (list-ref (slots (instance-return-value instance))
	       (position-if-not color-pointer (output-alias instance)))
     (first (slots (instance-return-value instance)))))

(define (c:sra-generate-il il xs vs)
 (cond
  ((il:dispatch? il)
   (c:dispatch-statement
    (if (boxed? (il:dispatch-v il))
	(c:sra-slot (c:sra-generate-variable (il:dispatch-il il)) 0)
	(c:sra-generate-variable (il:dispatch-il il)))
    (map (lambda (il) (c:sra-generate-il il xs vs))
	 (il:dispatch-ils il))))
  ((il:panic? il) (c:semicolon-after (c:panic (il:panic-string il))))
  ((il:mv-let? il)
   ;; abstraction
   (list
    (let ((vs (il:mv-let-vs il))
	  (xs (il:mv-let-xs il))
	  (il1 (il:mv-let-il1 il)))
     (assert (= (length xs) (length vs)))
     (cond
      ((il:dispatch? il1)
       ;; abstraction
       (list (map (lambda (x v)
		   (c:specifier-declaration v (c:sra-generate-variable x)))
		  xs
		  vs)
	     (c:dispatch-statement
	      (if (boxed? (il:dispatch-v il1))
		  (c:sra-slot (c:sra-generate-variable (il:dispatch-il il1)) 0)
		  (c:sra-generate-variable (il:dispatch-il il1)))
	      (map (lambda (il) (c:sra-generate-il il xs vs))
		   (il:dispatch-ils il1)))))
      ((il:closure-ref? il1)
       (let ((offset
	      (reduce
	       +
	       (sublist
		(map number-of-slots (closure-values (il:closure-ref-v il1)))
		0
		(positionp variable=?
			   (il:closure-ref-x il1)
			   (closure-variables (il:closure-ref-v il1))))
	       0)))
	(map (lambda (x v i)
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:closure-ref-il il1))
			   (+ i offset))))
	     xs
	     vs
	     (enumerate (length vs)))))
      ((il:perturbation-tagged-value-primal? il1)
       (map (lambda (x v i)
	     (c:specifier-init-declaration
	      v
	      (c:sra-generate-variable x)
	      (c:sra-slot (c:sra-generate-variable
			   (il:perturbation-tagged-value-primal-il il1))
			  i)))
	    xs
	    vs
	    (enumerate (length vs))))
      ((il:bundle-primal? il1)
       (map (lambda (x v i)
	     (c:specifier-init-declaration
	      v
	      (c:sra-generate-variable x)
	      (c:sra-slot (c:sra-generate-variable (il:bundle-primal-il il1))
			  i)))
	    xs
	    vs
	    (enumerate (length vs))))
      ((il:bundle-tangent? il1)
       (let ((offset
	      (number-of-slots (get-bundle-primal (il:bundle-tangent-v il1)))))
	(map (lambda (x v i)
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:bundle-tangent-il il1))
			   (+ i offset))))
	     xs
	     vs
	     (enumerate (length vs)))))
      ((il:sensitivity-tagged-value-primal? il1)
       (map (lambda (x v i)
	     (c:specifier-init-declaration
	      v
	      (c:sra-generate-variable x)
	      (c:sra-slot (c:sra-generate-variable
			   (il:sensitivity-tagged-value-primal-il il1))
			  i)))
	    xs
	    vs
	    (enumerate (length vs))))
      ((il:reverse-tagged-value-primal? il1)
       (map (lambda (x v i)
	     (c:specifier-init-declaration
	      v
	      (c:sra-generate-variable x)
	      (c:sra-slot (c:sra-generate-variable
			   (il:reverse-tagged-value-primal-il il1))
			  i)))
	    xs
	    vs
	    (enumerate (length vs))))
      ((il:car? il1)
       (map (lambda (x v i)
	     (c:specifier-init-declaration
	      v
	      (c:sra-generate-variable x)
	      (c:sra-slot (c:sra-generate-variable (il:car-il il1)) i)))
	    xs
	    vs
	    (enumerate (length vs))))
      ((il:cdr? il1)
       (let ((offset (number-of-slots (vlad-car (il:cdr-v il1)))))
	(map (lambda (x v i)
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:cdr-il il1))
			   (+ i offset))))
	     xs
	     vs
	     (enumerate (length vs)))))
      ((il:union-ref? il1)
       (let ((offset
	      (+ (reduce
		  +
		  (sublist (map number-of-slots
				(get-union-values (il:union-ref-v il1)))
			   0
			   (c:tag (il:union-ref-u il1) (il:union-ref-v il1)))
		  0)
		 1)))
	(map (lambda (x v i)
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:union-ref-il il1))
			   (+ i offset))))
	     xs
	     vs
	     (enumerate (length vs)))))
      ((il:construct*? il1)
       (assert (= (length xs) 1))
       ;; abstraction
       (list
	(c:specifier-init-declaration
	 (first vs)
	 (c:sra-generate-variable (first xs))
	 (c:pointer-cast
	  (c:specifier (il:construct*-v il1))
	  ;; We don't check for out of memory.
	  (c:call "GC_malloc_explicitly_typed"
		  (c:sizeof (c:specifier (il:construct*-v il1)))
		  (c:descr (il:construct*-v il1)))))
	(map-indexed
	 (lambda (il i)
	  (if (il:empty? il)
	      '()
	      (c:assignment (c:sra-slot (c:sra-generate-variable (first xs)) i)
			    (c:sra-generate-variable-tag-or-constant il))))
	 (il:construct*-ils il1))))
      ((il:construct-union? il1)
       (assert (and (= (length xs) 1)
		    (il:values*? (il:construct-union-il il1))))
       ;; abstraction
       (list
	(c:specifier-init-declaration
	 (first vs)
	 (c:sra-generate-variable (first xs))
	 (c:pointer-cast
	  (c:specifier (il:construct-union-v il1))
	  ;; We don't check for out of memory.
	  (c:call "GC_malloc_explicitly_typed"
		  (c:sizeof (c:specifier (il:construct-union-v il1)))
		  (c:descr (il:construct-union-v il1)))))
	(c:assignment (c:sra-slot (c:sra-generate-variable (first xs)) 0)
		      (c:tag (il:construct-union-u il1)
			     (il:construct-union-v il1)))
	(let ((offset
	       (+ (reduce +
			  (sublist
			   (map number-of-slots
				(get-union-values (il:construct-union-v il1)))
			   0
			   (c:tag (il:construct-union-u il1)
				  (il:construct-union-v il1)))
			  0)
		  1)))
	 (map-indexed
	  (lambda (il i)
	   (if (il:empty? il)
	       '()
	       (c:assignment (c:sra-slot (c:sra-generate-variable (first xs))
					 (+ i offset))
			     (c:sra-generate-variable-tag-or-constant il))))
	  (il:values*-ils (il:construct-union-il il1))))))
      ((il:construct-union0? il1)
       (assert (= (length xs) 1))
       ;; abstraction
       (list (c:specifier-init-declaration
	      (first vs)
	      (c:sra-generate-variable (first xs))
	      (c:pointer-cast
	       (c:specifier (il:construct-union0-v il1))
	       ;; We don't check for out of memory.
	       (c:call "GC_malloc_explicitly_typed"
		       (c:sizeof (c:specifier (il:construct-union0-v il1)))
		       (c:descr (il:construct-union0-v il1)))))
	     (c:assignment (c:sra-slot (c:sra-generate-variable (first xs)) 0)
			   (c:tag (il:construct-union0-u il1)
				  (il:construct-union0-v il1)))))
      ((il:call*? il1)
       (cond
	((string? (il:call*-instance il1))
	 (assert (= (length xs) 1))
	 (c:specifier-init-declaration
	  (first vs)
	  (c:sra-generate-variable (first xs))
	  (c:call* (c:instance-name (il:call*-instance il1))
		   (map c:sra-generate-variable-empty-tag-or-constant
			(il:call*-ils il1)))))
	((singleton-return-value? (il:call*-instance il1))
	 (assert (and (= (length xs) 1) (= (length vs) 1)))
	 (c:specifier-init-declaration
	  (first vs)
	  (c:sra-generate-variable (first xs))
	  (c:call* (c:instance-name (il:call*-instance il1))
		   (map c:sra-generate-variable-empty-tag-or-constant
			(il:call*-ils il1)))))
	(else
	 ;; abstraction
	 (list (c:semicolon-after
		(c:call* (c:instance-name (il:call*-instance il1))
			 (map c:sra-generate-variable-empty-tag-or-constant
			      (il:call*-ils il1))))
	       (map (lambda (x v i)
		     (c:specifier-init-declaration
		      v
		      (c:sra-generate-variable x)
		      (c:return-variable-name (il:call*-instance il1) i)))
		    xs
		    vs
		    (enumerate (length vs)))
	       ;; black-holeing
	       (map (lambda (v i)
		     (if (or (tag? v) (abstract-real? v))
			 '()
			 (c:assignment
			  (c:return-variable-name (il:call*-instance il1) i)
			  (c:null))))
		    vs
		    (enumerate (length vs)))))))
      ((il:binary? il1)
       (assert (= (length xs) 1))
       (c:specifier-init-declaration
	(first vs)
	(c:sra-generate-variable (first xs))
	(c:binary (c:sra-generate-variable-or-constant (il:binary-il1 il1))
		  (il:binary-string il1)
		  (c:sra-generate-variable-or-constant (il:binary-il2 il1)))))
      ((il:binary-boolean? il1)
       (assert (= (length xs) 1))
       (c:specifier-init-declaration
	(first vs)
	(c:sra-generate-variable (first xs))
	(c:conditional
	 (c:binary
	  (c:sra-generate-variable-or-constant (il:binary-boolean-il1 il1))
	  (il:binary-boolean-string il1)
	  (c:sra-generate-variable-or-constant (il:binary-boolean-il2 il1)))
	 (c:tag (vlad-true) (abstract-boolean))
	 (c:tag (vlad-false) (abstract-boolean)))))
      (else (internal-error))))
    (c:sra-generate-il (il:mv-let-il2 il) xs vs)))
  ((il:values*? il)
   (map (lambda (x il)
	 (if (il:empty? il)
	     '()
	     (c:assignment (c:sra-generate-variable x)
			   (c:sra-generate-variable-tag-or-constant il))))
	xs
	(il:values*-ils il)))
  (else (internal-error))))

(define (c:assignment? c)
 (and (= (length c) 3)
      (equal? (second c) ";")
      (equal? (third c) #\newline)
      (= (length (first c)) 3)
      (equal? (second (first c)) "=")))

(define (c:remove-redundant-stores cs)
 (append (remove-if c:assignment? cs)
	 (map first
	      (transitive-equivalence-classesp
	       (lambda (c1 c2) (equal? (first (first c1)) (first (first c2))))
	       (remove-if-not c:assignment? cs)))))

(define (c:sra-alias-fill f v a ils top?)
 (c:remove-redundant-stores
  (let loop ((v v) (a a) (ils ils) (top? top?))
   (assert (and (or top? (compatible-alias? v a)) (= (length ils) (length a))))
   (cond
    ((void? v) '())
    ((abstract-real? v)
     (assert (= (length a) 1))
     (if (il:empty? (first ils))
	 '()
	 (list
	  (c:assignment (f (first a))
			(c:sra-generate-variable-or-constant (first ils))))))
    ((and (boxed? v) (not top?))
     (assert (= (length a) 1))
     (if (il:empty? (first ils))
	 '()
	 (list
	  (c:assignment (f (first a)) (c:sra-generate-variable (first ils))))))
    ((union? v)
     (assert (not (boxed? v)))
     (if (il:empty? (first ils))
	 '()
	 ;; abstraction
	 (cons
	  (c:assignment (f (first a))
			(c:sra-generate-variable-or-tag (first ils)))
	  (if (il:tag? (first ils))
	      (loop
	       (list-ref (get-union-values v)
			 (c:tag (il:tag-u (first ils)) (il:tag-v (first ils))))
	       (list-ref (get-union-alias-values v a)
			 (c:tag (il:tag-u (first ils)) (il:tag-v (first ils))))
	       (list-ref (il:get-union-values v ils)
			 (c:tag (il:tag-u (first ils)) (il:tag-v (first ils))))
	       #f)
	      (list (c:dispatch-statement
		     (c:sra-generate-variable-or-tag (first ils))
		     ;; abstraction
		     (map (lambda (v a ils) (c:sra-alias-fill f v a ils #f))
			  (get-union-values v)
			  (get-union-alias-values v a)
			  (il:get-union-values v ils))))))))
    (else
     ;; abstraction
     (map-reduce
      append
      '()
      (lambda (v a ils) (loop v a ils #f))
      (aggregate-value-values v)
      (cond ((nonrecursive-closure? v)
	     (split-alias
	      a (map number-of-slots (get-nonrecursive-closure-values v))))
	    ((recursive-closure? v)
	     (split-alias
	      a (map number-of-slots (get-recursive-closure-values v))))
	    ((perturbation-tagged-value? v) (list a))
	    ((bundle? v)
	     (split-alias a
			  (list (number-of-slots (get-bundle-primal v))
				(number-of-slots (get-bundle-tangent v)))))
	    ((sensitivity-tagged-value? v) (list a))
	    ((reverse-tagged-value? v) (list a))
	    ((vlad-pair? v)
	     (split-alias a
			  (list (number-of-slots (vlad-car v))
				(number-of-slots (vlad-cdr v)))))
	    (else (internal-error)))
      (cond ((nonrecursive-closure? v)
	     (il:split-flat
	      ils (map number-of-slots (get-nonrecursive-closure-values v))))
	    ((recursive-closure? v)
	     (il:split-flat
	      ils (map number-of-slots (get-recursive-closure-values v))))
	    ((perturbation-tagged-value? v) (list ils))
	    ((bundle? v)
	     (il:split-flat ils
			    (list (number-of-slots (get-bundle-primal v))
				  (number-of-slots (get-bundle-tangent v)))))
	    ((sensitivity-tagged-value? v) (list ils))
	    ((reverse-tagged-value? v) (list ils))
	    ((vlad-pair? v)
	     (il:split-flat ils
			    (list (number-of-slots (vlad-car v))
				  (number-of-slots (vlad-cdr v)))))
	    (else (internal-error)))))))))

(define (c:sra-alias-generate-il il xs vs)
 (define (map3 f xs vs a)
  (assert (= (length xs) (length a)))
  (map f xs vs a))
 (cond
  ((il:dispatch? il)
   (c:dispatch-statement
    (if (boxed? (il:dispatch-v il))
	(c:sra-slot (c:sra-generate-variable (il:dispatch-il il))
		    (color-index-of (first (alias (il:dispatch-v il)))))
	(c:sra-generate-variable (il:dispatch-il il)))
    (map (lambda (il) (c:sra-alias-generate-il il xs vs))
	 (il:dispatch-ils il))))
  ((il:panic? il) (c:semicolon-after (c:panic (il:panic-string il))))
  ((il:mv-let? il)
   ;; abstraction
   (list
    (let ((vs (il:mv-let-vs il))
	  (xs (il:mv-let-xs il))
	  (il1 (il:mv-let-il1 il)))
     (assert (= (length xs) (length vs)))
     (cond
      ((il:dispatch? il1)
       ;; abstraction
       (list
	(map (lambda (x v)
	      (c:specifier-declaration v (c:sra-generate-variable x)))
	     xs
	     vs)
	(c:dispatch-statement
	 (if (boxed? (il:dispatch-v il1))
	     (c:sra-slot (c:sra-generate-variable (il:dispatch-il il1))
			 (color-index-of (first (alias (il:dispatch-v il1)))))
	     (c:sra-generate-variable (il:dispatch-il il1)))
	 (map (lambda (il) (c:sra-alias-generate-il il xs vs))
	      (il:dispatch-ils il1)))))
      ((il:closure-ref? il1)
       (map3
	(lambda (x v color)
	 ;; This can result in copying, i.e., multiple x's can be assigned the
	 ;; same slot value.
	 (c:specifier-init-declaration
	  v
	  (c:sra-generate-variable x)
	  (c:sra-slot (c:sra-generate-variable (il:closure-ref-il il1))
		      (color-index-of color))))
	xs
	vs
	(list-ref (split-alias (alias (il:closure-ref-v il1))
			       (map number-of-slots
				    (closure-values (il:closure-ref-v il1))))
		  (positionp variable=?
			     (il:closure-ref-x il1)
			     (closure-variables (il:closure-ref-v il1))))))
      ((il:perturbation-tagged-value-primal? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable
			    (il:perturbation-tagged-value-primal-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (alias (il:perturbation-tagged-value-primal-v il1))))
      ((il:bundle-primal? il1)
       (map3
	(lambda (x v color)
	 ;; This can result in copying, i.e., multiple x's can be assigned the
	 ;; same slot value.
	 (c:specifier-init-declaration
	  v
	  (c:sra-generate-variable x)
	  (c:sra-slot (c:sra-generate-variable (il:bundle-primal-il il1))
		      (color-index-of color))))
	xs
	vs
	(first
	 (split-alias
	  (alias (il:bundle-primal-v il1))
	  (list
	   (number-of-slots (get-bundle-primal (il:bundle-primal-v il1)))
	   (number-of-slots (get-bundle-tangent (il:bundle-primal-v il1))))))))
      ((il:bundle-tangent? il1)
       (map3
	(lambda (x v color)
	 ;; This can result in copying, i.e., multiple x's can be assigned the
	 ;; same slot value.
	 (c:specifier-init-declaration
	  v
	  (c:sra-generate-variable x)
	  (c:sra-slot (c:sra-generate-variable (il:bundle-tangent-il il1))
		      (color-index-of color))))
	xs
	vs
	(second
	 (split-alias
	  (alias (il:bundle-tangent-v il1))
	  (list
	   (number-of-slots (get-bundle-primal (il:bundle-tangent-v il1)))
	   (number-of-slots
	    (get-bundle-tangent (il:bundle-tangent-v il1))))))))
      ((il:sensitivity-tagged-value-primal? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable
			    (il:sensitivity-tagged-value-primal-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (alias (il:sensitivity-tagged-value-primal-v il1))))
      ((il:reverse-tagged-value-primal? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable
			    (il:reverse-tagged-value-primal-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (alias (il:reverse-tagged-value-primal-v il1))))
      ((il:car? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:car-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (first
	      (split-alias
	       (alias (il:car-v il1))
	       (list (number-of-slots (vlad-car (il:car-v il1)))
		     (number-of-slots (vlad-cdr (il:car-v il1))))))))
      ((il:cdr? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:cdr-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (second
	      (split-alias
	       (alias (il:cdr-v il1))
	       (list (number-of-slots (vlad-car (il:cdr-v il1)))
		     (number-of-slots (vlad-cdr (il:cdr-v il1))))))))
      ((il:union-ref? il1)
       (map3 (lambda (x v color)
	      ;; This can result in copying, i.e., multiple x's can be assigned
	      ;; the same slot value.
	      (c:specifier-init-declaration
	       v
	       (c:sra-generate-variable x)
	       (c:sra-slot (c:sra-generate-variable (il:union-ref-il il1))
			   (color-index-of color))))
	     xs
	     vs
	     (list-ref
	      (rest (split-alias
		     (alias (il:union-ref-v il1))
		     (cons 1
			   (map number-of-slots
				(get-union-values (il:union-ref-v il1))))))
	      (c:tag (il:union-ref-u il1) (il:union-ref-v il1)))))
      ((il:construct*? il1)
       (assert (= (length xs) 1))
       ;; abstraction
       (list (c:specifier-init-declaration
	      (first vs)
	      (c:sra-generate-variable (first xs))
	      (c:pointer-cast
	       (c:specifier (il:construct*-v il1))
	       ;; We don't check for out of memory.
	       (c:call "GC_malloc_explicitly_typed"
		       (c:sizeof (c:specifier (il:construct*-v il1)))
		       (c:descr (il:construct*-v il1)))))
	     (c:sra-alias-fill
	      (lambda (color)
	       (c:sra-slot (c:sra-generate-variable (first xs))
			   (color-index-of color)))
	      (il:construct*-v il1)
	      (alias (il:construct*-v il1))
	      (il:construct*-ils il1)
	      #t)))
      ((il:construct-union? il1)
       (assert (and (= (length xs) 1)
		    (il:values*? (il:construct-union-il il1))))
       ;; abstraction
       (list (c:specifier-init-declaration
	      (first vs)
	      (c:sra-generate-variable (first xs))
	      (c:pointer-cast
	       (c:specifier (il:construct-union-v il1))
	       ;; We don't check for out of memory.
	       (c:call "GC_malloc_explicitly_typed"
		       (c:sizeof (c:specifier (il:construct-union-v il1)))
		       (c:descr (il:construct-union-v il1)))))
	     (c:assignment
	      (c:sra-slot (c:sra-generate-variable (first xs))
			  (color-index-of
			   (first (alias (il:construct-union-v il1)))))
	      (c:tag (il:construct-union-u il1) (il:construct-union-v il1)))
	     (c:sra-alias-fill
	      (lambda (color)
	       (c:sra-slot (c:sra-generate-variable (first xs))
			   (color-index-of color)))
	      (il:construct-union-u il1)
	      (list-ref
	       (rest (split-alias
		      (alias (il:construct-union-v il1))
		      (cons 1
			    (map number-of-slots
				 (get-union-values
				  (il:construct-union-v il1))))))
	       (c:tag (il:construct-union-u il1) (il:construct-union-v il1)))
	      (il:values*-ils (il:construct-union-il il1))
	      #f)))
      ((il:construct-union0? il1)
       (assert (= (length xs) 1))
       ;; abstraction
       (list (c:specifier-init-declaration
	      (first vs)
	      (c:sra-generate-variable (first xs))
	      (c:pointer-cast
	       (c:specifier (il:construct-union0-v il1))
	       ;; We don't check for out of memory.
	       (c:call "GC_malloc_explicitly_typed"
		       (c:sizeof (c:specifier (il:construct-union0-v il1)))
		       (c:descr (il:construct-union0-v il1)))))
	     (c:assignment
	      (c:sra-slot (c:sra-generate-variable (first xs))
			  (color-index-of
			   (first (alias (il:construct-union0-v il1)))))
	      (c:tag (il:construct-union0-u il1)
		     (il:construct-union0-v il1)))))
      ((il:call*? il1)
       (cond
	((string? (il:call*-instance il1))
	 (assert (= (length xs) 1))
	 (c:specifier-init-declaration
	  (first vs)
	  (c:sra-generate-variable (first xs))
	  (c:call* (c:instance-name (il:call*-instance il1))
		   (map c:sra-generate-variable-empty-tag-or-constant
			(il:call*-ils il1)))))
	((singleton-return-value? (il:call*-instance il1))
	 (cond
	  ((and *alias?* (not (inline? (il:call*-instance il1))))
	   (let* ((i (position-if
		      color-index-of
		      (output-alias (il:call*-instance il1))))
		  (code (c:generate-il (list-ref vs i) (il:t))))
	    ;; abstraction
	    (list
	     (let ((arguments (map (lambda (v color) (list v color (il:t)))
				   (map-reduce append
					       '()
					       slots
					       (instance-argument-values
						(il:call*-instance il1)))
				   (input-alias (il:call*-instance il1)))))
	      ;; abstraction
	      (list
	       (map (lambda (argument)
		     (if (color-pointer (second argument))
			 '()
			 (c:specifier-declaration
			  (first argument)
			  (c:sra-generate-variable (third argument)))))
		    arguments)
	       (map (lambda (v a ils)
		     (c:sra-alias-fill
		      (lambda (color)
		       (c:sra-generate-variable
			(third
			 (find-if (lambda (argument)
				   (and (not (color-pointer (second argument)))
					(color=? color (second argument))))
				  arguments))))
		      v
		      a
		      ils
		      #f))
		    (instance-argument-values (il:call*-instance il1))
		    (split-alias (input-alias (il:call*-instance il1))
				 (map number-of-slots
				      (instance-argument-values
				       (il:call*-instance il1))))
		    (il:split-flat (il:call*-ils il1)
				   (map number-of-slots
					(instance-argument-values
					 (il:call*-instance il1)))))
	       (c:specifier-init-declaration
		(list-ref vs i)
		code
		(c:call* (c:instance-name (il:call*-instance il1))
			 (map c:sra-generate-variable
			      (map third
				   (remove-if
				    (lambda (argument)
				     (color-pointer (second argument)))
				    arguments)))))))
	     (map3 (lambda (x v color)
		    ;; This can result in copying, i.e., multiple x's can
		    ;; be assigned the same temporary variable.
		    (c:specifier-init-declaration
		     v (c:sra-generate-variable x) code))
		   xs
		   vs
		   (output-alias (il:call*-instance il1))))))
	  (else
	   (assert (and (= (length xs) 1) (= (length vs) 1)))
	   (c:specifier-init-declaration
	    (first vs)
	    (c:sra-generate-variable (first xs))
	    (c:call* (c:instance-name (il:call*-instance il1))
		     (map c:sra-generate-variable-empty-tag-or-constant
			  (il:call*-ils il1)))))))
	(else
	 ;; abstraction
	 (list (if (and *alias?* (not (inline? (il:call*-instance il1))))
		   (let ((arguments
			  (map (lambda (v color) (list v color (il:t)))
			       (map-reduce append
					   '()
					   slots
					   (instance-argument-values
					    (il:call*-instance il1)))
			       (input-alias (il:call*-instance il1)))))
		    ;; abstraction
		    (list
		     (map (lambda (argument)
			   (if (color-pointer (second argument))
			       '()
			       (c:specifier-declaration
				(first argument)
				(c:sra-generate-variable (third argument)))))
			  arguments)
		     (map (lambda (v a ils)
			   (c:sra-alias-fill
			    (lambda (color)
			     (c:sra-generate-variable
			      (third
			       (find-if
				(lambda (argument)
				 (and (not (color-pointer (second argument)))
				      (color=? color (second argument))))
				arguments))))
			    v
			    a
			    ils
			    #f))
			  (instance-argument-values (il:call*-instance il1))
			  (split-alias (input-alias (il:call*-instance il1))
				       (map number-of-slots
					    (instance-argument-values
					     (il:call*-instance il1))))
			  (il:split-flat (il:call*-ils il1)
					 (map number-of-slots
					      (instance-argument-values
					       (il:call*-instance il1)))))
		     (c:semicolon-after
		      (c:call* (c:instance-name (il:call*-instance il1))
			       (map c:sra-generate-variable
				    (map third
					 (remove-if
					  (lambda (argument)
					   (color-pointer (second argument)))
					  arguments)))))))
		   (c:semicolon-after
		    (c:call* (c:instance-name (il:call*-instance il1))
			     (map c:sra-generate-variable-empty-tag-or-constant
				  (il:call*-ils il1)))))
	       (if (and *alias?* (not (inline? (il:call*-instance il1))))
		   (map3 (lambda (x v color)
			  ;; This can result in copying, i.e., multiple x's can
			  ;; be assigned the same return variable.
			  (c:specifier-init-declaration
			   v
			   (c:sra-generate-variable x)
			   (c:return-variable-name
			    (il:call*-instance il1)
			    (color-index-of color))))
			 xs
			 vs
			 (output-alias (il:call*-instance il1)))
		   (map (lambda (x v i)
			 (c:specifier-init-declaration
			  v
			  (c:sra-generate-variable x)
			  (c:return-variable-name
			   (il:call*-instance il1) i)))
			xs
			vs
			(enumerate (length vs))))
	       ;; black-holeing
	       (if (and *alias?* (not (inline? (il:call*-instance il1))))
		   (map
		    (lambda (v color)
		     (if (or (tag? v) (abstract-real? v) (color-pointer color))
			 '()
			 (c:assignment
			  (c:return-variable-name
			   (il:call*-instance il1) (color-index-of color))
			  (c:null))))
		    vs
		    (output-alias (il:call*-instance il1)))
		   (map
		    (lambda (v i)
		     (if (or (tag? v) (abstract-real? v))
			 '()
			 (c:assignment
			  (c:return-variable-name (il:call*-instance il1) i)
			  (c:null))))
		    vs
		    (enumerate (length vs))))))))
      ((il:binary? il1)
       (assert (= (length xs) 1))
       (c:specifier-init-declaration
	(first vs)
	(c:sra-generate-variable (first xs))
	(c:binary
	 (c:sra-generate-variable-or-constant (il:binary-il1 il1))
	 (il:binary-string il1)
	 (c:sra-generate-variable-or-constant (il:binary-il2 il1)))))
      ((il:binary-boolean? il1)
       (assert (= (length xs) 1))
       (c:specifier-init-declaration
	(first vs)
	(c:sra-generate-variable (first xs))
	(c:conditional (c:binary (c:sra-generate-variable-or-constant
				  (il:binary-boolean-il1 il1))
				 (il:binary-boolean-string il1)
				 (c:sra-generate-variable-or-constant
				  (il:binary-boolean-il2 il1)))
		       (c:tag (vlad-true) (abstract-boolean))
		       (c:tag (vlad-false) (abstract-boolean)))))
      (else (internal-error))))
    (c:sra-alias-generate-il (il:mv-let-il2 il) xs vs)))
  ((il:values*? il)
   (map (lambda (x il)
	 (if (il:empty? il)
	     '()
	     (c:assignment (c:sra-generate-variable x)
			   (c:sra-generate-variable-tag-or-constant il))))
	xs
	(il:values*-ils il)))
  (else (internal-error))))

(define (c:generate-struct-and-union-declarations vs)
 ;; abstraction
 (list
  ;; This generates forward declarations for the struct and union tags.
  ;; abstraction
  (map
   (lambda (v)
    (cond ((void? v) '())
	  ((union? v)
	   ;; abstraction
	   (list (if (every void? (get-union-values v))
		     '()
		     (c:nonsra-newline-after
		      (c:semicolon-after
		       ;; abstraction
		       *union* " " (list "u" (c:index v)))))
		 (c:nonsra-newline-after (c:semicolon-after (c:specifier v)))))
	  ((abstract-real? v) '())
	  (else (c:nonsra-newline-after (c:semicolon-after (c:specifier v))))))
   (remove-if-not boxed? vs))
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
		    (c:nonsra-newline-after
		     (c:semicolon-after *union*
					" "
					;; abstraction
					(list "u" (c:index v))
					(c:no-newline-braces-around
					 ;; abstraction
					 (map c:specifier-declaration
					      (get-union-values v)
					      (c:generate-member-names v))))))
		(c:nonsra-newline-after
		 (c:semicolon-after
		  (c:specifier v)
		  (c:no-newline-braces-around
		   ;; The type tag is always unboxed.
		   (c:declaration "int" "t")
		   (if (every void? (get-union-values v))
		       '()
		       ;; The union is always unboxed.
		       ;; abstraction
		       (c:declaration
			(list *union* " " (list "u" (c:index v)))
			"u")))))))
	      ((abstract-real? v) '())
	      (else (c:nonsra-newline-after
		     (c:semicolon-after (c:specifier v)
					(c:no-newline-braces-around
					 ;; abstraction
					 (map c:specifier-declaration
					      (aggregate-value-values v)
					      (c:generate-slot-names v))))))))
       vs)))

(define (c:sra-generate-struct-and-union-declarations vs)
 ;; abstraction
 (list
  ;; This generates forward declarations for the struct and union tags.
  ;; abstraction
  (map
   (lambda (v) (c:nonsra-newline-after (c:semicolon-after (c:specifier v))))
   (remove-if-not boxed? vs))
  ;; abstraction
  (map (lambda (v)
	(c:nonsra-newline-after
	 (c:semicolon-after
	  (c:specifier v)
	  (c:no-newline-braces-around
	   ;; abstraction
	   (map-indexed
	    (lambda (v i) (c:specifier-declaration v (c:sra-member-name i)))
	    (boxed-slots v))))))
       (remove-if-not boxed? vs))
  ;; abstraction
  (map (lambda (v) (c:static-declaration "GC_descr" (c:descr v)))
       (remove-if-not boxed? vs))))

(define (c:sra-alias-generate-struct-and-union-declarations vs)
 (define (map2 f vs a)
  (assert (= (length vs) (length a)))
  (map f vs a))
 ;; abstraction
 (list
  ;; This generates forward declarations for the struct and union tags.
  ;; abstraction
  (map
   (lambda (v) (c:nonsra-newline-after (c:semicolon-after (c:specifier v))))
   (remove-if-not boxed? vs))
  ;; abstraction
  (map (lambda (v)
	(c:nonsra-newline-after
	 (c:semicolon-after
	  (c:specifier v)
	  (c:no-newline-braces-around
	   ;; abstraction
	   (map (lambda (v color)
		 (if (color-pointer color)
		     '()
		     (c:specifier-declaration
		      v (c:sra-member-name (color-index-of color)))))
		(boxed-slots v)
		(alias v))))))
       (remove-if-not boxed? vs))
  ;; abstraction
  (map (lambda (v) (c:static-declaration "GC_descr" (c:descr v)))
       (remove-if-not boxed? vs))))

(define (c:generate-constructor-declarations vs)
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
					    (c:generate-slot-names v)))))))
      vs))

(define (c:generate-constructor-definitions vs)
 ;; abstraction
 (map
  (lambda (v)
   (cond
    ((void? v) '())
    ((union? v)
     ;; By fortuitous confluence, this will not generate constructor
     ;; definitions for the empty abstract value.
     ;; abstraction
     (map (lambda (c:member u)
	   (c:specifier-function-definition
	    #t #t #f v
	    (c:function-declarator (c:unioner-name u v)
				   (c:specifier-parameter u "x"))
	    (c:statement-expression
	     (if (boxed? v)
		 (c:specifier-init-declaration
		  v
		  "r"
		  (c:pointer-cast
		   (c:specifier v)
		   ;; We don't check for out of memory.
		   (c:call "GC_malloc" (c:sizeof (c:specifier v)))))
		 (c:specifier-declaration v "r"))
	     ;; The type tag is always unboxed.
	     (c:assignment (c:tag-slot v "r") (c:tag u v))
	     (if (void? u) '() (c:assignment (c:member v "r") "x"))
	     "r")))
	  (c:generate-members v)
	  (get-union-values v)))
    ((abstract-real? v) '())
    (else
     (c:specifier-function-definition
      #t #t #f v
      (c:function-declarator* (c:constructor-name v)
			      (map c:specifier-parameter
				   (aggregate-value-values v)
				   (c:generate-slot-names v)))
      (c:statement-expression
       (if (boxed? v)
	   (c:specifier-init-declaration
	    v
	    "r"
	    (c:pointer-cast (c:specifier v)
			    ;; We don't check for out of memory.
			    (c:call "GC_malloc" (c:sizeof (c:specifier v)))))
	   (c:specifier-declaration v "r"))
       ;; abstraction
       (map (lambda (c:slot1 code1 v1)
	     (if (void? v1) '() (c:assignment (c:slot1 v "r") code1)))
	    (c:generate-slots v)
	    (c:generate-slot-names v)
	    (aggregate-value-values v))
       "r")))))
  vs))

(define (if-function-instances2 v1 v2 v3)
 (cond
  ((union? v1)
   ;; widening case L1
   (map-reduce unionq
	       '()
	       (lambda (u1) (if-function-instances2 u1 v2 v3))
	       (get-union-values v1)))
  ((vlad-false? v1)
   (cond ((union? v3)
	  ;; widening case I
	  (map-reduce unionq
		      '()
		      (lambda (u3) (if-function-instances2 v1 v2 u3))
		      (get-union-values v3)))
	 ((closure? v3) (list (lookup-function-instance v3 (vlad-empty-list))))
	 (else '())))
  (else (cond ((union? v2)
	       ;; widening case I
	       (map-reduce unionq
			   '()
			   (lambda (u2) (if-function-instances2 v1 u2 v3))
			   (get-union-values v2)))
	      ((closure? v2)
	       (list (lookup-function-instance v2 (vlad-empty-list))))
	      (else '())))))

(define (if-function-instances1 v1 v23)
 (cond
  ((union? v23)
   ;; widening case L2
   (map-reduce unionq
	       '()
	       (lambda (u23) (if-function-instances1 v1 u23))
	       (get-union-values v23)))
  ((vlad-pair? v23) (if-function-instances2 v1 (vlad-car v23) (vlad-cdr v23)))
  (else '())))

(define (if-function-instances v)
 (cond ((union? v)
	;; widening case L3
	(map-reduce unionq
		    '()
		    (lambda (u) (if-function-instances u))
		    (get-union-values v)))
       ((vlad-pair? v) (if-function-instances1 (vlad-car v) (vlad-cdr v)))
       (else '())))

(define (instances-before-il il)
 (cond
  ((il:c? il) '())
  ((il:x? il) '())
  ((il:y? il) '())
  ((il:z? il) '())
  ((il:t? il) '())
  ((il:a? il) '())
  ((il:r? il) '())
  ((il:empty? il) '())
  ((il:tag? il) '())
  ((il:constant? il) '())
  ((il:let? il)
   (unionq (instances-before-il (il:let-il1 il))
	   (instances-before-il (il:let-il2 il))))
  ((il:dispatch? il)
   (unionq (instances-before-il (il:dispatch-il il))
	   (map-reduce unionq '() instances-before-il (il:dispatch-ils il))))
  ((il:panic? il) '())
  ((il:closure-ref? il) (instances-before-il (il:closure-ref-il il)))
  ((il:perturbation-tagged-value-primal? il)
   (instances-before-il (il:perturbation-tagged-value-primal-il il)))
  ((il:bundle-primal? il) (instances-before-il (il:bundle-primal-il il)))
  ((il:bundle-tangent? il) (instances-before-il (il:bundle-tangent-il il)))
  ((il:sensitivity-tagged-value-primal? il)
   (instances-before-il (il:sensitivity-tagged-value-primal-il il)))
  ((il:reverse-tagged-value-primal? il)
   (instances-before-il (il:reverse-tagged-value-primal-il il)))
  ((il:car? il) (instances-before-il (il:car-il il)))
  ((il:cdr? il) (instances-before-il (il:cdr-il il)))
  ((il:union-ref? il) (instances-before-il (il:union-ref-il il)))
  ((il:construct*? il)
   (map-reduce unionq '() instances-before-il (il:construct*-ils il)))
  ((il:construct-union? il) (instances-before-il (il:construct-union-il il)))
  ((il:construct-union0? il) '())
  ((il:call*? il)
   (if (or (function-instance? (il:call*-instance il))
	   (widener-instance? (il:call*-instance il))
	   (primitive-procedure-instance? (il:call*-instance il)))
       (adjoinq (il:call*-instance il)
		(map-reduce unionq '() instances-before-il (il:call*-ils il)))
       (map-reduce unionq '() instances-before-il (il:call*-ils il))))
  ((il:binary? il)
   (unionq (instances-before-il (il:binary-il1 il))
	   (instances-before-il (il:binary-il2 il))))
  ((il:binary-boolean? il)
   (unionq (instances-before-il (il:binary-boolean-il1 il))
	   (instances-before-il (il:binary-boolean-il2 il))))
  ((il:mv-let? il)
   (unionq (instances-before-il (il:mv-let-il1 il))
	   (instances-before-il (il:mv-let-il2 il))))
  ((il:values*? il)
   (map-reduce unionq '() instances-before-il (il:values*-ils il)))
  ((variable? il) '())
  (else (internal-error))))

(define (instances-before instance)
 (instances-before-il (instance-il instance)))

(define (c:generate e bs)
 (with-abstract
  (lambda ()
   (generate! e bs)
   (determine-call-site-counts!)
   (let* ((instances
	   ;; This topological sort is needed so that all INLINE definitions
	   ;; come before their uses as required by gcc.
	   (feedback-topological-sort
	    eq?
	    (lambda (instance p?)
	     (assert (or (function-instance? instance)
			 (widener-instance? instance)
			 (and (primitive-procedure-instance? instance)
			      (memq (primitive-procedure-instance-symbol
				     instance)
				    '(zero
				      perturb
				      unperturb
				      primal
				      tangent
				      bundle
				      sensitize
				      unsensitize
				      plus
				      *j
				      *j-inverse)))
			 p?))
	     (set-inline?! instance p?))
	    instance-flag?
	    set-instance-flag?!
	    instances-before
	    (lambda (instances)
	     (let ((instance
		    (or
		     (find-if
		      (lambda (instance)
		       (and
			(function-instance? instance)
			(recursive-closure? (function-instance-v1 instance))))
		      instances)
		     (find-if
		      (lambda (instance)
		       (and
			(function-instance? instance)
			(backpropagator? (function-instance-v1 instance))
			(some
			 (lambda (instance1)
			  (and (recursive-closure?
				(function-instance-v1 instance1))
			       (vlad-pair? (instance-return-value instance1))
			       (abstract-value=?
				(function-instance-v1 instance)
				(vlad-cdr (instance-return-value instance1)))))
			 *function-instances*)))
		      instances)
		     (find-if
		      (lambda (instance)
		       (and (function-instance? instance)
			    (backpropagator? (function-instance-v1 instance))
			    (every (lambda (x) (zero? (variable-anf-max x)))
				   (parameter-variables
				    (lambda-expression-parameter
				     (nonrecursive-closure-lambda-expression
				      (function-instance-v1 instance)))))))
		      instances)
		     (find-if
		      (lambda (instance)
		       (or (function-instance? instance)
			   (widener-instance? instance)
			   (and (primitive-procedure-instance? instance)
				(memq (primitive-procedure-instance-symbol
				       instance)
				      '(zero
					perturb
					unperturb
					primal
					tangent
					bundle
					sensitize
					unsensitize
					plus
					*j
					*j-inverse)))))
		      instances))))
	      (assert instance)
	      instance))
	    (append *function-instances*
		    *widener-instances*
		    (map-reduce
		     append
		     '()
		     (lambda (b)
		      (primitive-procedure-instances (value-binding-value b)))
		     *value-bindings*))))
	  (vs (feedback-topological-sort
	       abstract-value=?
	       (lambda (v p?)
		(assert (or (union? v) (not (scalar-value? v)) p?))
		(when (or (union? v) (not (scalar-value? v)))
		 (set-boxed?! v (not p?))))
	       abstract-value-flag?
	       set-abstract-value-flag?!
	       (lambda (v)
		(cond ((union? v) (get-union-values v))
		      ((scalar-value? v) '())
		      (else (aggregate-value-values v))))
	       (lambda (vs)
		;; This used to put (find-if union? vs) as the first disjunct
		;; but c:sra-generate did not. I don't know if it was correct
		;; for c:generate to have the union case but c:sra-generate
		;; not to. So I removed it from all.
		(or
		 (find-if
		  (lambda (v)
		   (and (backpropagator? v)
			(not
			 (every inline?
				(nonrecursive-closure-function-instances v)))))
		  vs)
		 (find-if
		  (lambda (v)
		   (and (backpropagator? v)
			(every
			 (lambda (x) (zero? (variable-anf-max x)))
			 (parameter-variables
			  (lambda-expression-parameter
			   (nonrecursive-closure-lambda-expression v))))))
		  vs)
		 (first vs)))
	       *vs*)))
    (when *number-of-call-sites*
     (for-each (lambda (instance)
		(when (> (instance-number-of-call-sites instance)
			 *number-of-call-sites*)
		 (set-inline?! instance #f)))
	       (append *function-instances* *widener-instances*)))
    (when *alias?* (determine-aliasing! e vs))
    (when *il?*
     (for-each
      (lambda (instance)
       (when (or (not *inline?*) (not (inline? instance)))
	(pp (externalize-il
	     ((if *anf-convert?* il:anf-convert identity)
	      ((if *inline?* inline identity) (instance-il instance)))
	     *abstract-values?*))
	(newline)))
      instances)
     (pp (externalize-il
	  ((if *anf-convert?* il:anf-convert identity)
	   ((if *inline?* inline identity) *il*))
	  *abstract-values?*))
     (newline))
    (list
     ;; sqrt exp log sin cos atan2
     (c:newline-after "#include <math.h>")
     ;; fputs fputc scanf printf
     (c:newline-after "#include <stdio.h>")
     ;; exit
     (c:newline-after "#include <stdlib.h>")
     ;; GC_malloc
     (c:newline-after "#include <gc/gc.h>")
     ;; NULL
     (c:newline-after "#include <unistd.h>")
     (c:newline-after "#define INLINE inline __attribute__ ((always_inline))")
     (c:newline-after "#define NORETURN __attribute__ ((noreturn))")
     (c:newline-after "GC_API __attribute__ ((malloc)) GC_PTR GC_malloc GC_PROTO((size_t size_in_bytes));")
     (c:generate-struct-and-union-declarations vs)
     (c:specifier-function-declaration
      #t #t #t (empty-abstract-value)
      (c:function-declarator
       "panic" (c:parameter "char" (c:pointer-declarator "x"))))
     (c:specifier-function-declaration
      #t #t #f (abstract-real) (c:function-declarator "read_real"))
     (c:specifier-function-declaration
      #t #t #f (abstract-real)
      (c:function-declarator
       "write_real" (c:specifier-parameter (abstract-real) "x")))
     (c:generate-constructor-declarations vs)
     (map
      (lambda (instance)
       (if (or (not *inline?*) (not (inline? instance)))
	   (c:specifier-function-declaration
	    #t (inline? instance) #f
	    (instance-return-value instance)
	    (c:function-declarator*
	     (c:instance-name instance)
	     (cond
	      ((function-instance? instance)
	       (list
		(c:specifier-parameter (function-instance-v1 instance) "c")
		(c:specifier-parameter (function-instance-v2 instance) "x")))
	      ((widener-instance? instance)
	       (list
		(c:specifier-parameter (widener-instance-v1 instance) "x")))
	      ((primitive-procedure-instance? instance)
	       (list (c:specifier-parameter
		      (primitive-procedure-instance-v instance) "x")))
	      (else (internal-error)))))
	   '()))
      instances)
     (c:function-declaration #f #f #f #f "int" (c:function-declarator "main"))
     (c:specifier-function-definition
      #t #t #t (empty-abstract-value)
      (c:function-declarator "panic"
			     (c:parameter "char" (c:pointer-declarator "x")))
      (list (c:semicolon-after (c:call "fputs" "x" "stderr"))
	    (c:semicolon-after (c:call "fputc" "'\\n'" "stderr"))
	    (c:semicolon-after (c:call "exit" "EXIT_FAILURE"))))
     (c:specifier-function-definition
      #t #t #f (abstract-real) (c:function-declarator "read_real")
      (c:statement-expression
       (c:specifier-declaration (abstract-real) "x")
       (c:semicolon-after (c:call "scanf" "\"%lf\"" "&x"))
       "x"))
     (c:specifier-function-definition
      #t #t #f (abstract-real)
      (c:function-declarator
       "write_real" (c:specifier-parameter (abstract-real) "x"))
      (c:statement-expression
       (c:semicolon-after (c:call "printf" "\"%.18lg\\n\"" "x")) "x"))
     (c:generate-constructor-definitions vs)
     (map
      (lambda (instance)
       (if (or (not *inline?*) (not (inline? instance)))
	   (c:specifier-function-definition
	    #t (inline? instance) #f
	    (instance-return-value instance)
	    (c:function-declarator*
	     (c:instance-name instance)
	     (cond
	      ((function-instance? instance)
	       (list
		(c:specifier-parameter (function-instance-v1 instance) "c")
		(c:specifier-parameter (function-instance-v2 instance) "x")))
	      ((widener-instance? instance)
	       (list
		(c:specifier-parameter (widener-instance-v1 instance) "x")))
	      ((primitive-procedure-instance? instance)
	       (list (c:specifier-parameter
		      (primitive-procedure-instance-v instance) "x")))
	      (else (internal-error))))
	    (c:generate-il
	     (instance-return-value instance)
	     ((if *anf-convert?* il:anf-convert identity)
	      ((if *inline?* inline identity) (instance-il instance)))))
	   '()))
      instances)
     (c:function-definition
      #f #f #f #f "int" (c:function-declarator "main")
      (c:statement-expression
       (if (void?
	    (abstract-eval1
	     e (environment-binding-values (first (environment-bindings e)))))
	   '()
	   (c:semicolon-after
	    (c:generate-il (empty-abstract-value)
			   ((if *anf-convert?* il:anf-convert identity)
			    ((if *inline?* inline identity) *il*)))))
       "0")))))))

(define (scan f l i)
 ;; belongs in QobiScheme
 (let loop ((l l) (c (list i)))
  (if (null? l) (reverse c) (loop (rest l) (cons (f (first c) (first l)) c)))))

(define (c:sra-generate e bs)
 (define (map2 f vs a)
  (assert (= (length vs) (length a)))
  (map f vs a))
 (with-abstract
  (lambda ()
   (profile "~a c:sra-generate generate!~%" (lambda () (generate! e bs)))
   (profile "~a c:sra-generate determine-call-site-counts!~%"
	    (lambda () (determine-call-site-counts!)))
   (let* ((instances
	   ;; This topological sort is needed so that all INLINE definitions
	   ;; come before their uses as required by gcc.
	   (profile
	    "~a c:sra-generate feedback-topological-sort instances~%"
	    (lambda ()
	     (feedback-topological-sort
	      eq?
	      (lambda (instance p?)
	       (assert (or (function-instance? instance)
			   (widener-instance? instance)
			   (and (primitive-procedure-instance? instance)
				(memq (primitive-procedure-instance-symbol
				       instance)
				      '(zero
					perturb
					unperturb
					primal
					tangent
					bundle
					sensitize
					unsensitize
					plus
					*j
					*j-inverse)))
			   p?))
	       (set-inline?! instance p?))
	      instance-flag?
	      set-instance-flag?!
	      instances-before
	      (lambda (instances)
	       (let ((instance
		      (or
		       (find-if
			(lambda (instance)
			 (and (function-instance? instance)
			      (recursive-closure?
			       (function-instance-v1 instance))))
			instances)
		       (find-if
			(lambda (instance)
			 (and
			  (function-instance? instance)
			  (backpropagator? (function-instance-v1 instance))
			  (some
			   (lambda (instance1)
			    (and
			     (recursive-closure?
			      (function-instance-v1 instance1))
			     (vlad-pair? (instance-return-value instance1))
			     (abstract-value=?
			      (function-instance-v1 instance)
			      (vlad-cdr (instance-return-value instance1)))))
			   *function-instances*)))
			instances)
		       (find-if
			(lambda (instance)
			 (and (function-instance? instance)
			      (backpropagator? (function-instance-v1 instance))
			      (every (lambda (x) (zero? (variable-anf-max x)))
				     (parameter-variables
				      (lambda-expression-parameter
				       (nonrecursive-closure-lambda-expression
					(function-instance-v1 instance)))))))
			instances)
		       (find-if
			(lambda (instance)
			 (or (function-instance? instance)
			     (widener-instance? instance)
			     (and (primitive-procedure-instance? instance)
				  (memq (primitive-procedure-instance-symbol
					 instance)
					'(zero
					  perturb
					  unperturb
					  primal
					  tangent
					  bundle
					  sensitize
					  unsensitize
					  plus
					  *j
					  *j-inverse)))))
			instances))))
		(assert instance)
		instance))
	      (append
	       *function-instances*
	       *widener-instances*
	       (map-reduce
		append
		'()
		(lambda (b)
		 (primitive-procedure-instances (value-binding-value b)))
		*value-bindings*))))))
	  (vs
	   (profile
	    "~a c:sra-generate feedback-topological-sort vs~%"
	    (lambda ()
	     (feedback-topological-sort
	      abstract-value=?
	      (lambda (v p?)
	       (assert (or (union? v) (not (scalar-value? v)) p?))
	       (when (or (union? v) (not (scalar-value? v)))
		(set-boxed?! v (not p?))))
	      abstract-value-flag?
	      set-abstract-value-flag?!
	      (lambda (v)
	       (cond ((union? v) (get-union-values v))
		     ((scalar-value? v) '())
		     (else (aggregate-value-values v))))
	      (lambda (vs)
	       ;; See note in c:generate.
	       (or
		(find-if
		 (lambda (v)
		  (and (backpropagator? v)
		       (not
			(every inline?
			       (nonrecursive-closure-function-instances v)))))
		 vs)
		(find-if
		 (lambda (v)
		  (and (backpropagator? v)
		       (every
			(lambda (x) (zero? (variable-anf-max x)))
			(parameter-variables
			 (lambda-expression-parameter
			  (nonrecursive-closure-lambda-expression v))))))
		 vs)
		(first vs)))
	      *vs*)))))
    ;; debugging
    (when #f
     (for-each
      (lambda (instance)
       (unless (inline? instance)
	(display (c:instance-name instance))
	(newline)
	(write (externalize (widener-instance-v1 instance)))
	(newline)
	(write (externalize (widener-instance-v2 instance)))
	(newline)
	(newline)))
      *widener-instances*))
    ;; debugging
    (when #f
     (for-each
      (lambda (v)
       (when (boxed? v)
	(display (c:member-name v))
	(newline)
	(write (externalize v))
	(newline)
	(newline)))
      *vs*))
    (when *number-of-call-sites*
     (for-each (lambda (instance)
		(when (> (instance-number-of-call-sites instance)
			 *number-of-call-sites*)
		 (set-inline?! instance #f)))
	       (append *function-instances* *widener-instances*)))
    (profile "~a c:sra-generate determine-aliasing!~%"
	     (lambda () (when *alias?* (determine-aliasing! e vs))))
    (let* ((sras
	    (map
	     (lambda (instance)
	      (if (and (or (not *inline?*) (not (inline? instance)))
		       (not (void? (instance-return-value instance))))
		  (il:sra
		   (il:anf-convert
		    ((if *inline?* inline identity) (instance-il instance)))
		   (if (and *alias?* (not (inline? instance)))
		       (map
			(lambda (x v a)
			 (list x
			       v
			       (slots v)
			       (map (lambda (color)
				     (il:a instance (color-index-of color)))
				    a)))
			(cond
			 ((function-instance? instance) (list (il:c) (il:x)))
			 ((widener-instance? instance) (list (il:x)))
			 ((primitive-procedure-instance? instance)
			  (list (il:x)))
			 (else (internal-error)))
			(instance-argument-values instance)
			(split-alias
			 (input-alias instance)
			 (map number-of-slots
			      (instance-argument-values instance))))
		       (map
			(lambda (x v offset)
			 (list
			  x
			  v
			  (slots v)
			  (map-n (lambda (i) (il:a instance (+ i offset)))
				 (number-of-slots v))))
			(cond
			 ((function-instance? instance) (list (il:c) (il:x)))
			 ((widener-instance? instance) (list (il:x)))
			 ((primitive-procedure-instance? instance)
			  (list (il:x)))
			 (else (internal-error)))
			(instance-argument-values instance)
			(but-last
			 (scan +
			       (map number-of-slots
				    (instance-argument-values instance))
			       0)))))
		  #f))
	     instances))
	   (sra
	    (if (void? (abstract-eval1 e
				       (environment-binding-values
					(first (environment-bindings e)))))
		'()
		(il:sra (il:anf-convert ((if *inline?* inline identity) *il*))
			'()))))
     (when *il?*
      (for-each (lambda (instance sra)
		 (when (and (or (not *inline?*) (not (inline? instance)))
			    (not (void? (instance-return-value instance))))
		  (write (c:instance-name instance))
		  (newline)
		  (pp (externalize-il sra *abstract-values?*))
		  (newline)))
		instances
		sras)
      (unless (void?
	       (abstract-eval1
		e
		(environment-binding-values (first (environment-bindings e)))))
       (write "main")
       (newline)
       (pp (externalize-il sra *abstract-values?*))
       (newline)))
     (list
      ;; sqrt exp log sin cos atan2
      (c:newline-after "#include <math.h>")
      ;; fputs fputc scanf printf
      (c:newline-after "#include <stdio.h>")
      ;; exit
      (c:newline-after "#include <stdlib.h>")
      ;; GC_malloc_explicitly_typed GC_descr GC_word GC_BITMAP_SIZE
      ;; GC_set_bit GC_WORD_OFFSET GC_make_descriptor GC_WORD_LEN
      (c:newline-after "#include <gc/gc_typed.h>")
      ;; NULL
      (c:newline-after "#include <unistd.h>")
      (c:newline-after "#define INLINE inline __attribute__ ((always_inline))")
      (c:newline-after "#define NORETURN __attribute__ ((noreturn))")
      (c:newline-after "GC_API __attribute__ ((malloc)) GC_PTR GC_malloc_explicitly_typed GC_PROTO((size_t size_in_bytes, GC_descr d));")
      ((if *alias?*
	   c:sra-alias-generate-struct-and-union-declarations
	   c:sra-generate-struct-and-union-declarations)
       vs)
      (c:function-declaration
       #t #t #t #f "void"
       (c:function-declarator
	"panic" (c:parameter "char" (c:pointer-declarator "x"))))
      (c:specifier-function-declaration
       #t #t #f (abstract-real) (c:function-declarator "read_real"))
      (c:specifier-function-declaration
       #t #t #f (abstract-real)
       (c:function-declarator
	"write_real" (c:specifier-parameter (abstract-real) "x")))
      (map
       (lambda (instance)
	(if (and (or (not *inline?*) (not (inline? instance)))
		 (not (void? (instance-return-value instance))))
	    (list
	     (c:function-declaration
	      #t (inline? instance) #f
	      (and (singleton-return-value? instance)
		   (boxed? (singleton-return-value instance)))
	      (if (singleton-return-value? instance)
		  (c:specifier (singleton-return-value instance))
		  "void")
	      (c:function-declarator*
	       (c:instance-name instance)
	       (if (and *alias?* (not (inline? instance)))
		   (map (lambda (v color)
			 (if (color-pointer color)
			     '()
			     (c:specifier-parameter
			      v
			      (c:argument-variable-name
			       instance (color-index-of color)))))
			(map-reduce
			 append '() slots (instance-argument-values instance))
			(input-alias instance))
		   (map-indexed
		    (lambda (v i)
		     (c:specifier-parameter
		      v (c:argument-variable-name instance i)))
		    (map-reduce
		     append '() slots (instance-argument-values instance))))))
	     (cond ((singleton-return-value? instance) '())
		   ((and *alias?* (not (inline? instance)))
		    (map2 (lambda (v color)
			   (if (color-pointer color)
			       '()
			       (c:nonsra-newline-after
				(c:static-specifier-declaration
				 v
				 (c:return-variable-name
				  instance (color-index-of color))))))
			  (slots (instance-return-value instance))
			  (output-alias instance)))
		   (else
		    (map-indexed (lambda (v i)
				  (c:nonsra-newline-after
				   (c:static-specifier-declaration
				    v (c:return-variable-name instance i))))
				 (slots (instance-return-value instance))))))
	    '()))
       instances)
      (c:function-declaration #f #f #f #f "int" (c:function-declarator "main"))
      (c:function-definition
       #t #t #t #f "void"
       (c:function-declarator "panic"
			      (c:parameter "char" (c:pointer-declarator "x")))
       (list (c:semicolon-after (c:call "fputs" "x" "stderr"))
	     (c:semicolon-after (c:call "fputc" "'\\n'" "stderr"))
	     (c:semicolon-after (c:call "exit" "EXIT_FAILURE"))))
      (c:specifier-function-definition
       #t #t #f (abstract-real) (c:function-declarator "read_real")
       (c:statement-expression
	(c:specifier-declaration (abstract-real) "x")
	(c:semicolon-after (c:call "scanf" "\"%lf\"" "&x"))
	"x"))
      (c:specifier-function-definition
       #t #t #f (abstract-real)
       (c:function-declarator
	"write_real" (c:specifier-parameter (abstract-real) "x"))
       (c:statement-expression
	(c:semicolon-after (c:call "printf" "\"%.18lg\\n\"" "x")) "x"))
      (map
       (lambda (instance sra)
	(if (and (or (not *inline?*) (not (inline? instance)))
		 (not (void? (instance-return-value instance))))
	    (c:statement-function-definition
	     #t (inline? instance) #f
	     (and (singleton-return-value? instance)
		  (boxed? (singleton-return-value instance)))
	     (if (singleton-return-value? instance)
		 (c:specifier (singleton-return-value instance))
		 "void")
	     (c:function-declarator*
	      (c:instance-name instance)
	      (if (and *alias?* (not (inline? instance)))
		  (map (lambda (v color)
			(if (color-pointer color)
			    '()
			    (c:specifier-parameter
			     v
			     (c:argument-variable-name
			      instance (color-index-of color)))))
		       (map-reduce
			append '() slots (instance-argument-values instance))
		       (input-alias instance))
		  (map-indexed
		   (lambda (v i)
		    (c:specifier-parameter
		     v (c:argument-variable-name instance i)))
		   (map-reduce
		    append '() slots (instance-argument-values instance)))))
	     ;; abstraction
	     (list
	      (if (singleton-return-value? instance)
		  (c:specifier-declaration
		   (singleton-return-value instance)
		   (singleton-return-variable-name instance))
		  '())
	      (if (and *alias?* (not (inline? instance)))
		  (let ((xs (map (lambda (v) (il:t))
				 (slots (instance-return-value instance)))))
		   ;; abstraction
		   (list
		    (map
		     (lambda (v x)
		      (c:specifier-declaration v (c:sra-generate-variable x)))
		     (slots (instance-return-value instance))
		     xs)
		    (c:sra-alias-generate-il
		     sra xs (slots (instance-return-value instance)))
		    (c:sra-alias-fill
		     (lambda (color)
		      (c:return-variable-name instance (color-index-of color)))
		     (instance-return-value instance)
		     (output-alias instance)
		     xs
		     #f)))
		  ((if *alias?* c:sra-alias-generate-il c:sra-generate-il)
		   sra
		   (map-n (lambda (i) (il:r instance i))
			  (number-of-slots (instance-return-value instance)))
		   (slots (instance-return-value instance))))
	      (if (singleton-return-value? instance)
		  (c:return (singleton-return-variable-name instance))
		  '())))
	    '()))
       instances
       sras)
      (c:statement-function-definition
       #f #f #f #f "int" (c:function-declarator "main")
       ;; abstraction
       (list
	;; abstraction
	(map (lambda (v)
	      ;; abstraction
	      (list
	       (c:init-declaration
		;; abstraction
		"GC_word"
		(c:subscript (c:bitmap v)
			     ;; abstraction
			     (c:call "GC_BITMAP_SIZE" (c:specifier v)))
		;; abstraction
		"{0}")
	       (if *alias?*
		   (map (lambda (u color)
			 (if (and (boxed? u) (not (color-pointer color)))
			     (c:semicolon-after
			      (c:call "GC_set_bit"
				      (c:bitmap v)
				      (c:call "GC_WORD_OFFSET"
					      (c:specifier v)
					      (c:sra-member-name
					       (color-index-of color)))))
			     '()))
			(boxed-slots v)
			(alias v))
		   (map-indexed (lambda (u i)
				 (if (boxed? u)
				     (c:semicolon-after
				      (c:call "GC_set_bit"
					      (c:bitmap v)
					      (c:call "GC_WORD_OFFSET"
						      (c:specifier v)
						      (c:sra-member-name i))))
				     '()))
				(boxed-slots v)))
	       (c:assignment (c:descr v)
			     (c:call "GC_make_descriptor"
				     (c:bitmap v)
				     (c:call "GC_WORD_LEN" (c:specifier v))))))
	     (remove-if-not boxed? vs))
	(if (void?
	     (abstract-eval1
	      e
	      (environment-binding-values (first (environment-bindings e)))))
	    '()
	    ((if *alias?* c:sra-alias-generate-il c:sra-generate-il)
	     sra '() '()))
	(c:return "0")))))))))

(define (c:generate-file code pathname)
 (call-with-output-file (replace-extension pathname "c")
  (lambda (output-port)
   (let loop ((code code))
    (cond ((char? code) (write-char code output-port))
	  ((string? code) (display code output-port))
	  ((number? code) (write code output-port))
	  ((pair? code) (loop (car code)) (loop (cdr code)))
	  ((null? code) #f)
	  (else (internal-error)))))))

;;; Primitives

(define (concrete-read-real v)
 (unless (vlad-empty-list? v)
  (run-time-error "Argument is not an equivalent value for '()" v))
 (let ((v (read)))
  (unless (real? v) (run-time-error "Value read is not real" v))
  v))

(define (concrete-unary f) (lambda (v) (f v)))

(define (concrete-ad f) f)

(define (concrete-unary-predicate f)
 (lambda (v) (if (f v) (vlad-true) (vlad-false))))

(define (concrete-unary-real f s)
 (lambda (v)
  (unless (vlad-real? v)
   (run-time-error (format #f "Argument to ~a is invalid" s) v))
  (f v)))

(define (concrete-unary-real-predicate f s)
 (lambda (v)
  (unless (vlad-real? v)
   (run-time-error (format #f "Argument to ~a is invalid" s) v))
  (if (f v) (vlad-true) (vlad-false))))

(define (concrete-binary-real f s)
 (lambda (v)
  (unless (vlad-pair? v)
   (run-time-error (format #f "Argument to ~a is invalid" s) v))
  (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
   (unless (and (vlad-real? v1) (vlad-real? v2))
    (run-time-error (format #f "Argument to ~a is invalid" s) v))
   (f v1 v2))))

(define (concrete-binary-real-predicate f s)
 (lambda (v)
  (unless (vlad-pair? v)
   (run-time-error (format #f "Argument to ~a is invalid" s) v))
  (let ((v1 (vlad-car v)) (v2 (vlad-cdr v)))
   (unless (and (vlad-real? v1) (vlad-real? v2))
    (run-time-error (format #f "Argument to ~a is invalid" s) v))
   (if (f v1 v2) (vlad-true) (vlad-false)))))

(define (concrete-if-procedure v)
 (unless (vlad-pair? v)
  (run-time-error "Argument to if-procedure is invalid" v))
 (let ((v23 (vlad-cdr v)))
  (unless (vlad-pair? v23)
   (run-time-error "Argument to if-procedure is invalid" v))
  (concrete-apply ((if (vlad-false? (vlad-car v)) vlad-cdr vlad-car) v23)
		  (vlad-empty-list))))

(define (abstract-read-real v)
 (if (vlad-empty-list? v)
     (abstract-real)
     (compile-time-warning
      "Argument might not be an equivalent value for '()" v)))

;;; needs work: The widening case is not annotated yet.
(define (abstract-unary f) (lambda (v) (map-union f v)))

(define (abstract-ad f) f)

;;; needs work: The widening case is not annotated yet.
(define (abstract-unary-predicate f)
 (lambda (v) (map-union (lambda (u) (if (f u) (vlad-true) (vlad-false))) v)))

;;; needs work: The widening case is not annotated yet.
(define (abstract-unary-real f s)
 (lambda (v)
  (map-union (lambda (u)
	      (if (vlad-real? u)
		  (if (real? u) (f u) (abstract-real))
		  (compile-time-warning
		   (format #f "Argument to ~a might be invalid" s) u)))
	     v)))

;;; needs work: The widening case is not annotated yet.
(define (abstract-unary-real-predicate f s)
 (lambda (v)
  (map-union
   (lambda (u)
    (if (vlad-real? u)
	(if (real? u) (if (f u) (vlad-true) (vlad-false)) (abstract-boolean))
	(compile-time-warning
	 (format #f "Argument to ~a might be invalid" s) u)))
   v)))

;;; needs work: The widening case is not annotated yet.
(define (abstract-binary-real f s)
 (lambda (v)
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
   v)))

;;; needs work: The widening case is not annotated yet.
(define (abstract-binary-real-predicate f s)
 (lambda (v)
  (map-union
   (lambda (u)
    (if (vlad-pair? u)
	(cross-union (lambda (u1 u2)
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
   v)))

(define (abstract-if-procedure2 v1 v2 v3)
 (cond
  ;; widening case L1
  ((union? v1) (map-union (lambda (u1) (abstract-if-procedure2 u1 v2 v3)) v1))
  ((vlad-false? v1) (abstract-apply v3 (vlad-empty-list)))
  (else (abstract-apply v2 (vlad-empty-list)))))

(define (abstract-if-procedure1 v1 v23)
 (cond
  ;; widening case L2
  ((union? v23) (map-union (lambda (u23) (abstract-if-procedure1 v1 u23)) v23))
  ((vlad-pair? v23) (abstract-if-procedure2 v1 (vlad-car v23) (vlad-cdr v23)))
  (else
   (compile-time-warning "Argument to if-procedure might be invalid" v23))))

(define (abstract-if-procedure v)
 (cond
  ;; widening case L3
  ((union? v) (map-union (lambda (u) (abstract-if-procedure u)) v))
  ((vlad-pair? v) (abstract-if-procedure1 (vlad-car v) (vlad-cdr v)))
  (else (compile-time-warning "Argument to if-procedure might be invalid" v))))

(define (define-primitive-procedure symbol
	 name
	 c:name
	 concrete
	 abstract
	 alias
	 all-instances!
	 generate
	 forward
	 reverse)
 (set! *value-bindings*
       (cons (make-value-binding (new-variable symbol)
				 (make-primitive-procedure symbol
							   name
							   c:name
							   concrete
							   abstract
							   alias
							   all-instances!
							   generate
							   forward
							   reverse
							   0
							   '()))
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
	    (let ((v (value-binding-value b)))
	     (let ((v-forward (evaluate-in-top-level-environment
			       (primitive-procedure-forward v))))
	      (set-primitive-procedure-forward! v v-forward)
	      (set-primal-cache! v-forward v)
	      (set-tangent-cache! v-forward (new-perturbation-tagged-value v)))
	     (let ((v-reverse (evaluate-in-top-level-environment
			       (primitive-procedure-reverse v))))
	      (set-primitive-procedure-reverse! v v-reverse)
	      (set-nonrecursive-closure-*j-inverse-cache! v-reverse v))))
	   *value-bindings*))

(define (initialize-basis!)
 ;; This is not a widening case.
 (set! *empty-abstract-value* (create-union '()))
 (when *interned?*
  (assert (not *frozen?*))
  (set! *unions* (cons (empty-abstract-value) *unions*))
  (set-union-canonize-cache! *empty-abstract-value* *empty-abstract-value*)
  (set-union-intern-cache! *empty-abstract-value* *empty-abstract-value*))
 ;; This is not a widening case.
 (set! *abstract-boolean* (new-union (list (vlad-true) (vlad-false))))
 (define-primitive-procedure '+
  "+"
  "add"
  (concrete-binary-real + "+")
  (abstract-binary-real + "+")
  (alias-binary-real + "+")
  (all-real*real-instances! '+)
  (generate-real*real-primitive (lambda (il1 il2) (il:binary il1 "+" il2)))
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
  "-"
  "minus"
  (concrete-binary-real - "-")
  (abstract-binary-real - "-")
  (alias-binary-real - "-")
  (all-real*real-instances! '-)
  (generate-real*real-primitive (lambda (il1 il2) (il:binary il1 "-" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (- x1 x2) (perturb (- x1-unperturbed x2-unperturbed)))))
  `(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (- x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons -
			     (cons (unsensitize (sensitivity y))
				   (- ,(if *imprecise-inexacts?* 0.0 0)
				      (unsensitize (sensitivity y)))))))))))
 (define-primitive-procedure '*
  "*"
  "times"
  (concrete-binary-real * "*")
  (abstract-binary-real * "*")
  (alias-binary-real * "*")
  (all-real*real-instances! '*)
  (generate-real*real-primitive (lambda (il1 il2) (il:binary il1 "*" il2)))
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
  "/"
  "divide"
  (concrete-binary-real / "/")
  (abstract-binary-real / "/")
  (alias-binary-real / "/")
  (all-real*real-instances! '/)
  (generate-real*real-primitive (lambda (il1 il2) (il:binary il1 "/" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (/ x1 x2)
	     (perturb (/ (- (* x2 x1-unperturbed) (* x1 x2-unperturbed))
			 (* x2 x2))))))
  `(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (/ x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons /
			     (cons (/ (unsensitize (sensitivity y)) x2)
				   (- ,(if *imprecise-inexacts?* 0.0 0)
				      (/ (* x1 (unsensitize (sensitivity y)))
					 (* x2 x2)))))))))))
 (define-primitive-procedure 'sqrt
  "sqrt"
  "sqrt"
  (concrete-unary-real sqrt "sqrt")
  (abstract-unary-real sqrt "sqrt")
  (alias-unary-real sqrt "sqrt")
  (all-real-instances! 'sqrt)
  (generate-real-primitive (lambda (il) (il:call "sqrt" il)))
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
  "exp"
  "exp"
  (concrete-unary-real exp "exp")
  (abstract-unary-real exp "exp")
  (alias-unary-real exp "exp")
  (all-real-instances! 'exp)
  (generate-real-primitive (lambda (il) (il:call "exp" il)))
  '(lambda ((forward x))
    (let* ((x (primal (forward x)))
	   ((perturbation x) (tangent (forward x)))
	   ;; debugging
	   (foo (exp x)))
     (bundle foo (perturb (* foo (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let* ((x (*j-inverse (reverse x)))
	   ;; debugging
	   (foo (exp x)))
     (cons (*j foo)
	   (lambda ((sensitivity y))
	    (sensitize (cons exp (* foo (unsensitize (sensitivity y))))))))))
 (define-primitive-procedure 'log
  "log"
  "log"
  (concrete-unary-real log "log")
  (abstract-unary-real log "log")
  (alias-unary-real log "log")
  (all-real-instances! 'log)
  (generate-real-primitive (lambda (il) (il:call "log" il)))
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (log x) (perturb (/ (unperturb (perturbation x)) x)))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (log x))
	   (lambda ((sensitivity y))
	    (sensitize (cons log (/ (unsensitize (sensitivity y)) x))))))))
 (define-primitive-procedure 'sin
  "sin"
  "sin"
  (concrete-unary-real sin "sin")
  (abstract-unary-real sin "sin")
  (alias-unary-real sin "sin")
  (all-real-instances! 'sin)
  (generate-real-primitive (lambda (il) (il:call "sin" il)))
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
  "cos"
  "cos"
  (concrete-unary-real cos "cos")
  (abstract-unary-real cos "cos")
  (alias-unary-real cos "cos")
  (all-real-instances! 'cos)
  (generate-real-primitive (lambda (il) (il:call "cos" il)))
  `(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (cos x)
	     (perturb (- ,(if *imprecise-inexacts?* 0.0 0)
			 (* (sin x) (unperturb (perturbation x))))))))
  `(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (cos x))
      (lambda ((sensitivity y))
       (sensitize (cons cos
			(- ,(if *imprecise-inexacts?* 0.0 0)
			   (* (sin x) (unsensitize (sensitivity y)))))))))))
 (define-primitive-procedure 'atan
  "atan"
  "atan"
  (concrete-binary-real atan "atan")
  (abstract-binary-real atan "atan")
  (alias-binary-real atan "atan")
  (all-real*real-instances! 'atan)
  (generate-real*real-primitive (lambda (il1 il2) (il:call "atan2" il1 il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  ((cons x1-unperturbed x2-unperturbed)
	   (unperturb (tangent (forward x)))))
     (bundle (atan x1 x2)
	     (perturb (/ (- (* x2 x1-unperturbed) (* x1 x2-unperturbed))
			 (+ (* x1 x1) (* x2 x2)))))))
  `(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (atan x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons atan
			     (cons (/ (* x2 (unsensitize (sensitivity y)))
				      (+ (* x1 x1) (* x2 x2)))
				   (- ,(if *imprecise-inexacts?* 0.0 0)
				      (/ (* x1 (unsensitize (sensitivity y)))
					 (+ (* x1 x1) (* x2 x2))))))))))))
 (define-primitive-procedure '=
  "="
  "eq"
  (concrete-binary-real-predicate = "=")
  (abstract-binary-real-predicate = "=")
  (alias-binary-real-predicate = "=")
  (all-real*real-instances! '=)
  (generate-real*real-primitive
   (lambda (il1 il2) (il:binary-boolean il1 "==" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons = (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '<
  "<"
  "lt"
  (concrete-binary-real-predicate < "<")
  (abstract-binary-real-predicate < "<")
  (alias-binary-real-predicate < "<")
  (all-real*real-instances! '<)
  (generate-real*real-primitive
   (lambda (il1 il2) (il:binary-boolean il1 "<" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (< x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (< x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons < (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '>
  ">"
  "gt"
  (concrete-binary-real-predicate > ">")
  (abstract-binary-real-predicate > ">")
  (alias-binary-real-predicate > ">")
  (all-real*real-instances! '>)
  (generate-real*real-primitive
   (lambda (il1 il2) (il:binary-boolean il1 ">" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (> x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (> x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons > (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '<=
  "<="
  "le"
  (concrete-binary-real-predicate <= "<=")
  (abstract-binary-real-predicate <= "<=")
  (alias-binary-real-predicate <= "<=")
  (all-real*real-instances! '<=)
  (generate-real*real-primitive
   (lambda (il1 il2) (il:binary-boolean il1 "<=" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (<= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (<= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons <= (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure '>=
  ">="
  "ge"
  (concrete-binary-real-predicate >= ">=")
  (abstract-binary-real-predicate >= ">=")
  (alias-binary-real-predicate >= ">=")
  (all-real*real-instances! '>=)
  (generate-real*real-primitive
   (lambda (il1 il2) (il:binary-boolean il1 ">=" il2)))
  '(lambda ((forward x))
    (let (((cons x1 x2) (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (>= x1 x2))))
  '(lambda ((reverse x))
    (let (((cons x1 x2) (*j-inverse (reverse x))))
     (cons (*j (>= x1 x2))
	   (lambda ((sensitivity y))
	    (sensitize (cons >= (cons (zero x1) (zero x2)))))))))
 (define-primitive-procedure 'zero?
  "zero?"
  "zerop"
  (concrete-unary-real-predicate zero? "zero?")
  (abstract-unary-real-predicate zero? "zero?")
  (alias-unary-real-predicate zero? "zero?")
  (all-real-instances! 'zero?)
  (generate-real-primitive (il:unary-boolean "=="))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (zero? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero? x))
	   (lambda ((sensitivity y)) (sensitize (cons zero? (zero x))))))))
 (define-primitive-procedure 'positive?
  "positive?"
  "positivep"
  (concrete-unary-real-predicate positive? "positive?")
  (abstract-unary-real-predicate positive? "positive?")
  (alias-unary-real-predicate positive? "positive?")
  (all-real-instances! 'positive?)
  (generate-real-primitive (il:unary-boolean ">"))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (positive? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (positive? x))
	   (lambda ((sensitivity y)) (sensitize (cons positive? (zero x))))))))
 (define-primitive-procedure 'negative?
  "negative?"
  "negativep"
  (concrete-unary-real-predicate negative? "negative?")
  (abstract-unary-real-predicate negative? "negative?")
  (alias-unary-real-predicate negative? "negative?")
  (all-real-instances! 'negative?)
  (generate-real-primitive (il:unary-boolean "<"))
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (negative? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (negative? x))
	   (lambda ((sensitivity y)) (sensitize (cons negative? (zero x))))))))
 (define-primitive-procedure 'null?
  "null?"
  "nullp"
  (concrete-unary-predicate vlad-empty-list?)
  (abstract-unary-predicate vlad-empty-list?)
  (alias-unary-predicate vlad-empty-list?)
  (all-type-instances! 'null?)
  (generate-type-predicate vlad-empty-list?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (null? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (null? x))
	   (lambda ((sensitivity y)) (sensitize (cons null? (zero x))))))))
 (define-primitive-procedure 'boolean?
  "boolean?"
  "booleanp"
  (concrete-unary-predicate vlad-boolean?)
  (abstract-unary-predicate vlad-boolean?)
  (alias-unary-predicate vlad-boolean?)
  (all-type-instances! 'boolean?)
  (generate-type-predicate vlad-boolean?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (boolean? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (boolean? x))
	   (lambda ((sensitivity y)) (sensitize (cons boolean? (zero x))))))))
 (define-primitive-procedure 'real?
  "real?"
  "realp"
  (concrete-unary-predicate vlad-real?)
  (abstract-unary-predicate vlad-real?)
  (alias-unary-predicate vlad-real?)
  (all-type-instances! 'real?)
  (generate-type-predicate vlad-real?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (real? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (real? x))
	   (lambda ((sensitivity y)) (sensitize (cons real? (zero x))))))))
 (define-primitive-procedure 'pair?
  "pair?"
  "pairp"
  (concrete-unary-predicate vlad-pair?)
  (abstract-unary-predicate vlad-pair?)
  (alias-unary-predicate vlad-pair?)
  (all-type-instances! 'pair?)
  (generate-type-predicate vlad-pair?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (pair? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (pair? x))
	   (lambda ((sensitivity y)) (sensitize (cons pair? (zero x))))))))
 (define-primitive-procedure 'procedure?
  ;; needs work: This should probably return #f for any transformed procedure.
  "procedure?"
  "procedurep"
  (concrete-unary-predicate vlad-procedure?)
  (abstract-unary-predicate vlad-procedure?)
  (alias-unary-predicate vlad-procedure?)
  (all-type-instances! 'procedure?)
  (generate-type-predicate vlad-procedure?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
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
  "perturbation?"
  "perturbatiop"
  (concrete-unary-predicate perturbation-value?)
  (abstract-unary-predicate perturbation-value?)
  (alias-unary-predicate perturbation-value?)
  (all-type-instances! 'perturbation?)
  (generate-type-predicate perturbation-value?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (perturbation? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (perturbation? x))
      (lambda ((sensitivity y)) (sensitize (cons perturbation? (zero x))))))))
 (define-primitive-procedure 'forward?
  "forward?"
  "forwardp"
  (concrete-unary-predicate forward-value?)
  (abstract-unary-predicate forward-value?)
  (alias-unary-predicate forward-value?)
  (all-type-instances! 'forward?)
  (generate-type-predicate forward-value?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (forward? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (forward? x))
	   (lambda ((sensitivity y)) (sensitize (cons forward? (zero x))))))))
 (define-primitive-procedure 'sensitivity?
  "sensitvity?"
  "sensitvityp"
  (concrete-unary-predicate sensitivity-value?)
  (abstract-unary-predicate sensitivity-value?)
  (alias-unary-predicate sensitivity-value?)
  (all-type-instances! 'sensitivity?)
  (generate-type-predicate sensitivity-value?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (sensitivity? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (sensitivity? x))
      (lambda ((sensitivity y)) (sensitize (cons sensitivity? (zero x))))))))
 (define-primitive-procedure 'reverse?
  "reverse?"
  "reversep"
  (concrete-unary-predicate reverse-value?)
  (abstract-unary-predicate reverse-value?)
  (alias-unary-predicate reverse-value?)
  (all-type-instances! 'reverse?)
  (generate-type-predicate reverse-value?)
  '(lambda ((forward x))
    (let ((x (primal (forward x)))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
     (j* (reverse? x))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (reverse? x))
	   (lambda ((sensitivity y)) (sensitize (cons reverse? (zero x))))))))
 (define-primitive-procedure 'if-procedure
  "if-procedure"
  "if_procedure"
  concrete-if-procedure
  abstract-if-procedure
  alias-if-procedure
  (all-instances! 'if-procedure)
  generate-if-procedure
  '(lambda ((forward x))
    (let (((cons* x1 x2 x3) (primal (forward x)))
	  ((cons* x1-unperturbed x2-unperturbed x3-unperturbed)
	   (unperturb (tangent (forward x))))
	  (j* (lambda (x) (bundle x (zero (perturb x))))))
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
  "read-real"
  "read_real"
  (concrete-unary concrete-read-real)
  (abstract-unary abstract-read-real)
  alias-read-real
  all-read-real-instances!
  generate-read-real
  `(lambda (',(j* (vlad-empty-list)))
    (bundle (read-real) (perturb ,(if *imprecise-inexacts?* 0.0 0))))
  `(lambda (',(*j (vlad-empty-list)))
    (cons (*j (read-real))
	  (lambda ((sensitivity y)) (sensitize (cons read-real '()))))))
 (define-primitive-procedure 'real
  "real"
  "real"
  (concrete-unary-real (lambda (v) v) "real")
  (abstract-unary-real (lambda (v) (abstract-real)) "real")
  alias-real
  (all-real-instances! 'real)
  generate-real
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
 (define-primitive-procedure 'write-real
  "write-real"
  "write_real"
  (concrete-unary-real
   (lambda (v)
    ((if *pp?* pp write) (externalize v))
    (newline)
    v)
   "write-real")
  (abstract-unary-real (lambda (v) v) "write-real")
  (alias-unary-real (lambda (v) v) "write-real")
  (all-real-instances! 'write-real)
  generate-write-real
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     ;; The unperturb composed with perturb could be optimized away.
     (bundle (write-real x) (perturb (unperturb (perturbation x))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (write-real x))
	   (lambda ((sensitivity y))
	    (sensitize (cons write-real (unsensitize (sensitivity y)))))))))
 (define-primitive-procedure 'write
  "write"
  "write"
  (concrete-unary (lambda (v)
		   ((if *pp?* pp write) (externalize v))
		   (newline)
		   v))
  (abstract-unary (lambda (v) v))
  (lambda (v a) (unimplemented "write"))
  (lambda () (unimplemented "write"))
  (lambda (instance) (unimplemented "write"))
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
  "zero"
  "zero"
  (concrete-ad zero)
  (abstract-ad zero)
  (alias-ad zero-alias)
  (all-unary-ad-instances! 'zero)
  generate-zero
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     ;; The unperturb-perturb could be optimized away.
     (bundle (zero x) (perturb (zero (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    (let ((x (*j-inverse (reverse x))))
     (cons (*j (zero x))
	   (lambda ((sensitivity y)) (sensitize (cons zero (zero x))))))))
 (define-primitive-procedure 'perturb
  "perturb"
  "perturb"
  (concrete-ad perturb)
  (abstract-ad perturb)
  (alias-ad perturb-alias)
  (all-unary-ad-instances! 'perturb)
  generate-perturb
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
  "unperturb"
  "unperturb"
  (concrete-ad unperturb)
  (abstract-ad unperturb)
  (alias-ad unperturb-alias)
  (all-unary-ad-instances! 'unperturb)
  generate-unperturb
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
  "primal"
  "primal"
  (concrete-ad primal)
  (abstract-ad primal)
  (alias-ad primal-alias)
  (all-unary-ad-instances! 'primal)
  generate-primal
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
  "tangent"
  "tangent"
  (concrete-ad tangent)
  (abstract-ad tangent)
  (alias-ad tangent-alias)
  (all-unary-ad-instances! 'tangent)
  generate-tangent
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
  "bundle"
  "bundle"
  (concrete-ad bundle)
  (abstract-ad bundle)
  (alias-ad bundle-alias1)
  (all-binary-ad-instances! 'bundle)
  generate-bundle
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
  "sensitize"
  "sensitize"
  (concrete-ad sensitize)
  (abstract-ad sensitize)
  (alias-ad sensitize-alias)
  (all-unary-ad-instances! 'sensitize)
  generate-sensitize
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
  "unsensitize"
  "unsensitize"
  (concrete-ad unsensitize)
  (abstract-ad unsensitize)
  (alias-ad unsensitize-alias)
  (all-unary-ad-instances! 'unsensitize)
  generate-unsensitize
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
  "plus"
  "plus"
  (concrete-ad plus)
  (abstract-ad plus)
  (alias-ad plus-alias)
  (all-binary-ad-instances! 'plus)
  generate-plus
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
  "*j"
  "starj"
  (concrete-ad *j)
  (abstract-ad *j)
  (alias-ad *j-alias)
  (all-unary-ad-instances! '*j)
  generate-*j
  '(lambda ((forward x))
    (let ((x (primal (forward x))) ((perturbation x) (tangent (forward x))))
     (bundle (*j x) (perturb (*j (unperturb (perturbation x)))))))
  '(lambda ((reverse x))
    ;; The *j-inverse composed with *j could be optimized away.
    (let ((x (*j-inverse (reverse x))))
     (cons
      (*j (*j x))
      ;; The argument must be called y-reverse so as not to confuse the tags.
      (lambda ((sensitivity y-reverse))
       (sensitize
	(cons *j (*j-inverse (unsensitize (sensitivity y-reverse))))))))))
 (define-primitive-procedure '*j-inverse
  "*j-inverse"
  "starj_inverse"
  (concrete-ad *j-inverse)
  (abstract-ad *j-inverse)
  (alias-ad *j-inverse-alias)
  (all-unary-ad-instances! '*j-inverse)
  generate-*j-inverse
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
