(MODULE STALINGRAD (WITH QOBISCHEME XLIB STALINGRADLIB-STUFF) (MAIN MAIN))
;;; LaHaShem HaAretz U'Mloah
;;; $Id$

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004, 2005, 2006, and 2007 Purdue University. All rights
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
;;;    National University of Ireland, Maynooth
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
		 (at-most-one ("flow-analysis" flow-analysis?)
			      ("flow-analysis-result" flow-analysis-result?)
			      ("compile" compile?))
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
		 (at-most-one
		  ("no-closure-depth-limit" no-closure-depth-limit?)
		  ("closure-depth-limit" closure-depth-limit?
					 (limit "n" integer-argument 1)))
		 (required (pathname "pathname" string-argument)))
 (when (and unabbreviate-executably? unabbreviate-nonrecursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-nonrecursive-closures"))
 (when (and unabbreviate-executably? unabbreviate-recursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-recursive-closures"))
 (set! *include-path*
       (append '(".") include-path '("/usr/local/stalingrad/include")))
 (set! *assert?* (not no-assert?))
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
 (set! *closure-depth-limit* (if no-closure-depth-limit? #f limit))
 (initialize-basis!)
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
	   (let* ((bs (expression-environment-bindings e)))
	    (unless (= (length bs) 1) (internal-error))
	    (pp (externalize (environment-binding-value (first bs))))
	    (newline)
	    (pp (externalize-analysis))
	    (newline)))
	  (flow-analysis-result?
	   ;; needs work: With the new formulation, can't run flow analysis
	   ;;             more than once.
	   (flow-analysis! e bs)
	   (let ((bs (expression-environment-bindings e)))
	    (unless (= (length bs) 1) (internal-error))
	    (pp (externalize (environment-binding-value (first bs))))
	    (newline)))
	  (compile?
	   ;; needs work: With the new formulation, can't run flow analysis
	   ;;             more than once.
	   (flow-analysis! e bs)
	   ;; needs work: to update call to generate
	   (generate-file (generate e 'needs-work bs) pathname)
	   ;; needs work: -c -k -cc -copt
	   (system (format #f "gcc -o ~a -Wall ~a -lm"
			   (strip-extension pathname)
			   (replace-extension pathname "c"))))
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
		 (concrete-eval e (map value-binding-value bs))))))))
	   (newline)
	   (when metered?
	    (for-each (lambda (b)
		       (let ((v (value-binding-value b)))
			(when (and (primitive-procedure? v)
				   (not (zero? (primitive-procedure-meter v))))
			 (format #t "~a ~s~%"
				 (number->string-of-length
				  (primitive-procedure-meter v) 7)
				 (value-binding-variable b)))))
		      (reverse *value-bindings*))))))
	(loop (rest es) ds))))))

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
