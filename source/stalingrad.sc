(MODULE STALINGRAD (WITH QOBISCHEME XLIB STALINGRADLIB-STUFF) (MAIN MAIN))
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
(include "stalingrad.sch")

(set! *program* "stalingrad")
(set! *panic?* #f)			;debugging

;;; Macros

;;; Structures

;;; Variables

;;; Parameters

;;; Procedures

;;; Commands

;;; Top Level

(define-command (main
		 (any-number
		  ("I"
		   include-path?
		   (include-path "include-directory" string-argument)))
		 (at-most-one ("no-assert" no-assert?))
		 (at-most-one ("wizard" wizard?))
		 (at-most-one ("interned" interned?))
		 (at-most-one ("flow-analysis" flow-analysis?)
			      ("flow-analysis-result" flow-analysis-result?)
			      ("compile" compile?))
		 (at-most-one
		  ("cc" cc? (cc "C-compiler" string-argument "gcc")))
		 (at-most-one ("c" disable-run-cc?))
		 (at-most-one ("k" keep-c?))
		 (any-number
		  ("copt" copt? (copts "C-compiler-options" string-argument)))
		 (at-most-one ("metered" metered?))
		 (at-most-one ("trace-primitive-procedures"
			       trace-primitive-procedures?))
		 (at-most-one ("trace-nonrecursive-closures"
			       trace-nonrecursive-closures?))
		 (at-most-one ("trace-recursive-closures"
			       trace-recursive-closures?))
		 (at-most-one ("trace-argument/result" trace-argument/result?))
		 (at-most-one ("unabbreviate-executably"
			       unabbreviate-executably?))
		 (at-most-one ("unabbreviate-transformed"
			       unabbreviate-transformed?))
		 (at-most-one ("unabbreviate-nonrecursive-closures"
			       unabbreviate-nonrecursive-closures?))
		 (at-most-one ("unabbreviate-recursive-closures"
			       unabbreviate-recursive-closures?))
		 (at-most-one ("level" level? (level "n" integer-argument #f)))
		 (at-most-one
		  ("length" length? (write-length "n" integer-argument #f)))
		 (at-most-one ("pp" pp?))
		 (at-most-one ("verbose"
			       verbose?
			       (verbose "n" integer-argument #f)))
		 (at-most-one ("imprecise-inexacts" imprecise-inexacts?))
		 (at-most-one ("no-warnings" no-warnings?))
		 (at-most-one ("all-limits"
			       all-limits?
			       (all-limits "n" integer-argument #f)))
		 (at-most-one ("no-real-width-limit" no-real-width-limit?)
			      ("real-width-limit"
			       real-width-limit?
			       (real-width-limit "n" integer-argument 1)))
		 (at-most-one
		  ("no-closure-width-limit" no-closure-width-limit?)
		  ("closure-width-limit"
		   closure-width-limit?
		   (closure-width-limit "n" integer-argument 1)))
		 (at-most-one ("no-perturbation-tagged-value-width-limit"
			       no-perturbation-tagged-value-width-limit?)
			      ("perturbation-tagged-value-width-limit"
			       perturbation-tagged-value-width-limit?
			       (perturbation-tagged-value-width-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-bundle-width-limit"
			       no-bundle-width-limit?)
			      ("bundle-width-limit"
			       bundle-width-limit?
			       (bundle-width-limit "n" integer-argument 1)))
		 (at-most-one ("no-sensitivity-tagged-value-width-limit"
			       no-sensitivity-tagged-value-width-limit?)
			      ("sensitivity-tagged-value-width-limit"
			       sensitivity-tagged-value-width-limit?
			       (sensitivity-tagged-value-width-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-reverse-tagged-value-width-limit"
			       no-reverse-tagged-value-width-limit?)
			      ("reverse-tagged-value-width-limit"
			       reverse-tagged-value-width-limit?
			       (reverse-tagged-value-width-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-pair-width-limit" no-pair-width-limit?)
			      ("pair-width-limit"
			       pair-width-limit?
			       (pair-width-limit "n" integer-argument 1)))
		 (at-most-one
		  ("no-closure-depth-limit" no-closure-depth-limit?)
		  ("closure-depth-limit"
		   closure-depth-limit?
		   (closure-depth-limit "n" integer-argument 1)))
		 (at-most-one
		  ("no-backpropagator-depth-limit"
		   no-backpropagator-depth-limit?)
		  ("backpropagator-depth-limit"
		   backpropagator-depth-limit?
		   (backpropagator-depth-limit "n" integer-argument 1)))
		 (at-most-one ("no-perturbation-tagged-value-depth-limit"
			       no-perturbation-tagged-value-depth-limit?)
			      ("perturbation-tagged-value-depth-limit"
			       perturbation-tagged-value-depth-limit?
			       (perturbation-tagged-value-depth-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-bundle-depth-limit"
			       no-bundle-depth-limit?)
			      ("bundle-depth-limit"
			       bundle-depth-limit?
			       (bundle-depth-limit "n" integer-argument 1)))
		 (at-most-one ("no-sensitivity-tagged-value-depth-limit"
			       no-sensitivity-tagged-value-depth-limit?)
			      ("sensitivity-tagged-value-depth-limit"
			       sensitivity-tagged-value-depth-limit?
			       (sensitivity-tagged-value-depth-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-reverse-tagged-value-depth-limit"
			       no-reverse-tagged-value-depth-limit?)
			      ("reverse-tagged-value-depth-limit"
			       reverse-tagged-value-depth-limit?
			       (reverse-tagged-value-depth-limit
				"n" integer-argument 1)))
		 (at-most-one ("no-pair-depth-limit" no-pair-depth-limit?)
			      ("pair-depth-limit"
			       pair-depth-limit?
			       (pair-depth-limit "n" integer-argument 1)))
		 (at-most-one ("no-order-limit" no-order-limit?)
			      ("order-limit"
			       order-limit?
			       (order-limit "n" integer-argument 1)))
		 (at-most-one ("widen-lists" widen-lists?))
		 (at-most-one ("alias" alias?))
		 (at-most-one ("inline" inline?))
		 (at-most-one ("number-of-call-sites"
			       number-of-call-sites?
			       (number-of-call-sites "n" integer-argument 1)))
		 (at-most-one ("anf-convert" anf-convert?))
		 (at-most-one ("sra" sra?))
		 (at-most-one ("il" il?))
		 (at-most-one ("no-multiply-out-dispatches-cost-limit"
			       no-multiply-out-dispatches-cost-limit?)
			      ("multiply-out-dispatches-cost-limit"
			       multiply-out-dispatches-cost-limit?
			       (multiply-out-dispatches-cost-limit
				"n"
				integer-argument
				1)))
		 (required (pathname "pathname" string-argument)))
 (when #f (initialize-time-buckets 39))	;debugging
 (when (and unabbreviate-executably? unabbreviate-nonrecursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-nonrecursive-closures"))
 (when (and unabbreviate-executably? unabbreviate-recursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-recursive-closures"))
 (when (and disable-run-cc? (not compile?))
  (compile-time-error "Can't specify -c without -compile"))
 (when (and keep-c? (not compile?))
  (compile-time-error "Can't specify -k without -compile"))
 (when (and cc? (not compile?))
  (compile-time-error "Can't specify -cc without -compile"))
 (when (and copt? (not compile?))
  (compile-time-error "Can't specify -copt without -compile"))
 (when (and copt? disable-run-cc?)
  (compile-time-error "Can't specify -copt with -c"))
 (when (and cc? disable-run-cc?)
  (compile-time-error "Can't specify -cc with -c"))
 (set! *include-path*
       (append '(".") include-path '("/usr/local/stalingrad/include")))
 (set! *assert?* (not (or no-assert? (getenv "STALINGRAD_NO_ASSERT"))))
 (set! *wizard?* wizard?)
 (set! *flow-analysis?* (or flow-analysis? flow-analysis-result? compile?))
 (set! *compile?* compile?)
 (set! *metered?* metered?)
 (set! *trace-primitive-procedures?* trace-primitive-procedures?)
 (set! *trace-nonrecursive-closures?* trace-nonrecursive-closures?)
 (set! *trace-recursive-closures?* trace-recursive-closures?)
 (set! *trace-argument/result?* trace-argument/result?)
 (set! *unabbreviate-executably?* unabbreviate-executably?)
 (set! *unabbreviate-transformed?* unabbreviate-transformed?)
 (set! *unabbreviate-nonrecursive-closures?*
       unabbreviate-nonrecursive-closures?)
 (set! *unabbreviate-recursive-closures?* unabbreviate-recursive-closures?)
 (set! *pp?* pp?)
 (set! *verbose* (if verbose? verbose #f))
 (set! *imprecise-inexacts?* imprecise-inexacts?)
 (set! *warnings?* (not no-warnings?))
 (set! *real-width-limit*
       (cond (real-width-limit? real-width-limit)
	     (no-real-width-limit? #f)
	     (else all-limits)))
 (set! *closure-width-limit*
       (cond (closure-width-limit? closure-width-limit)
	     (no-closure-width-limit? #f)
	     (else all-limits)))
 (set! *perturbation-tagged-value-width-limit*
       (cond (perturbation-tagged-value-width-limit?
	      perturbation-tagged-value-width-limit)
	     (no-perturbation-tagged-value-width-limit? #f)
	     (else all-limits)))
 (set! *bundle-width-limit*
       (cond (bundle-width-limit? bundle-width-limit)
	     (no-bundle-width-limit? #f)
	     (else all-limits)))
 (set! *sensitivity-tagged-value-width-limit*
       (cond (sensitivity-tagged-value-width-limit?
	      sensitivity-tagged-value-width-limit)
	     (no-sensitivity-tagged-value-width-limit? #f)
	     (else all-limits)))
 (set! *reverse-tagged-value-width-limit*
       (cond (reverse-tagged-value-width-limit?
	      reverse-tagged-value-width-limit)
	     (no-reverse-tagged-value-width-limit? #f)
	     (else all-limits)))
 (set! *pair-width-limit*
       (cond (pair-width-limit? pair-width-limit)
	     (no-pair-width-limit? #f)
	     (else all-limits)))
 (set! *closure-depth-limit*
       (cond (closure-depth-limit? closure-depth-limit)
	     (no-closure-depth-limit? #f)
	     (else all-limits)))
 (set! *backpropagator-depth-limit*
       (cond (backpropagator-depth-limit? backpropagator-depth-limit)
	     (no-backpropagator-depth-limit? #f)
	     (else all-limits)))
 (set! *perturbation-tagged-value-depth-limit*
       (cond (perturbation-tagged-value-depth-limit?
	      perturbation-tagged-value-depth-limit)
	     (no-perturbation-tagged-value-depth-limit? #f)
	     (else all-limits)))
 (set! *bundle-depth-limit*
       (cond (bundle-depth-limit? bundle-depth-limit)
	     (no-bundle-depth-limit? #f)
	     (else all-limits)))
 (set! *sensitivity-tagged-value-depth-limit*
       (cond (sensitivity-tagged-value-depth-limit?
	      sensitivity-tagged-value-depth-limit)
	     (no-sensitivity-tagged-value-depth-limit? #f)
	     (else all-limits)))
 (set! *reverse-tagged-value-depth-limit*
       (cond (reverse-tagged-value-depth-limit?
	      reverse-tagged-value-depth-limit)
	     (no-reverse-tagged-value-depth-limit? #f)
	     (else all-limits)))
 (set! *pair-depth-limit*
       (cond (pair-depth-limit? pair-depth-limit)
	     (no-pair-depth-limit? #f)
	     (else all-limits)))
 (set! *order-limit*
       (cond (order-limit? order-limit)
	     (no-order-limit? #f)
	     (else all-limits)))
 (set! *widen-lists?* widen-lists?)
 (set! *almost-union-free?*
       (and (not *real-width-limit*)
	    (not *closure-width-limit*)
	    (not *perturbation-tagged-value-width-limit*)
	    (not *bundle-width-limit*)
	    (not *sensitivity-tagged-value-width-limit*)
	    (not *reverse-tagged-value-width-limit*)
	    (not *pair-width-limit*)
	    (not *closure-depth-limit*)
	    (not *perturbation-tagged-value-depth-limit*)
	    (not *bundle-depth-limit*)
	    (not *sensitivity-tagged-value-depth-limit*)
	    (not *reverse-tagged-value-depth-limit*)
	    (not *pair-depth-limit*)))
 ;; Cannot rely on the with-* procedures since syntax-check-expression! and
 ;; parse need to have these set.
 (set! *canonized?* *flow-analysis?*)
 (set! *interned?* (or interned? *flow-analysis?*))
 (set! *alias?* (or alias? (getenv "STALINGRAD_ALIAS")))
 (set! *inline?* (or inline? (getenv "STALINGRAD_INLINE")))
 (set! *number-of-call-sites*
       (cond (number-of-call-sites? number-of-call-sites)
	     ((getenv "STALINGRAD_NUMBER_OF_CALL_SITES")
	      (getenv "STALINGRAD_NUMBER_OF_CALL_SITES"))
	     (else #f)))
 (set! *anf-convert?* (or anf-convert? (getenv "STALINGRAD_ANF_CONVERT")))
 (set! *sra?* (or sra? (getenv "STALINGRAD_SRA")))
 (set! *il?* (or il? (getenv "STALINGRAD_IL")))
 (set! *profile?* (getenv "STALINGRAD_PROFILE"))
 (set! *write-alias-pass?* (getenv "STALINGRAD_WRITE_ALIAS_PASS"))
 (set! *write-alias-final?* (getenv "STALINGRAD_WRITE_ALIAS_FINAL"))
 (set! *write-alias-verbose?* (getenv "STALINGRAD_WRITE_ALIAS_VERBOSE"))
 (set! *il:multiply-out-dispatches-cost-limit*
       (cond (no-multiply-out-dispatches-cost-limit? #f)
	     (multiply-out-dispatches-cost-limit?
	      multiply-out-dispatches-cost-limit)
	     (else 64)))
 (with-concrete (lambda () (initialize-basis!)))
 (let loop ((es (read-source pathname)) (ds '()))
  (unless (null? es)
   (if (definition? (first es))
       (loop (rest es) (cons (first es) ds))
       (let ((e (expand-definitions (reverse ds) (first es))))
	(syntax-check-expression! e)
	(let* ((result (parse e)) (e (first result)) (bs (second result)))
	 (cond
	  (flow-analysis?
	   ;; needs work: With the new formulation, can't run flow analysis
	   ;;             more than once.
	   (flow-analysis! e bs)
	   (with-abstract
	    (lambda ()
	     (let ((bs (environment-bindings e)))
	      (unless (= (length bs) 1) (internal-error))
	      (pp (externalize (environment-binding-value (first bs))))
	      (newline)
	      (pp (externalize-analysis))
	      (newline)))))
	  (flow-analysis-result?
	   ;; needs work: With the new formulation, can't run flow analysis
	   ;;             more than once.
	   (flow-analysis! e bs)
	   (with-abstract
	    (lambda ()
	     (let ((bs (environment-bindings e)))
	      (unless (= (length bs) 1) (internal-error))
	      (pp (externalize (environment-binding-value (first bs))))
	      (newline)))))
	  (compile?
	   ;; needs work: With the new formulation, can't run flow analysis
	   ;;             more than once.
	   (flow-analysis! e bs)
	   (generate! e)
	   (c:generate-file
	    (with-abstract
	     (lambda ()
	      (profile "~a generating C~%"
		       (lambda () ((if *sra?* c:sra-generate c:generate) e)))))
	    pathname)
	   (unless disable-run-cc?
	    (system (reduce (lambda (s1 s2) (string-append s1 " " s2))
			    `(,cc
			      "-o"
			      ,(strip-extension pathname)
			      ,(replace-extension pathname "c")
			      ,@(reverse copts)
			      "-lm"
			      "-lgc")
			    "")))
	   (unless (or disable-run-cc? keep-c?)
	    (rm (replace-extension pathname "c"))))
	  (else
	   (when metered?
	    (for-each (lambda (b)
		       (let ((v (value-binding-value b)))
			(when (primitive-procedure? v)
			 (set-primitive-procedure-meter! v 0))))
		      *value-bindings*))
	   (with-write-level
	    level
	    (lambda ()
	     (with-write-length
	      write-length
	      (lambda ()
	       ((if *pp?* pp write)
		(externalize
		 (with-concrete
		  (lambda ()
		   (concrete-eval e (map value-binding-value bs))))))))))
	   (newline)
	   (when metered?
	    (for-each (lambda (b)
		       (let ((v (value-binding-value b)))
			(when (and (primitive-procedure? v)
				   (not (zero? (primitive-procedure-meter v))))
			 (format #t "~a ~s~%"
				 (number->string-of-length
				  (primitive-procedure-meter v) 7)
				 (variable-name (value-binding-variable b))))))
		      (reverse *value-bindings*))))))
	(loop (rest es) ds)))))
 ;; debugging
 (when #f (print-time-buckets)))

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
