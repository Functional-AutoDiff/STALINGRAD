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
		 (at-most-one ("flow-analysis" flow-analysis?)
			      ("flow-analysis-result" flow-analysis-result?)
			      ("compile" compile?))
		 (at-most-one ("expression-equality-using-identity"
			       expression-equality-using-identity?)
			      ("expression-equality-using-structural"
			       expression-equality-using-structural?)
			      ("expression-equality-using-alpha"
			       expression-equality-using-alpha?))
		 (at-most-one ("ebs" ebs?))
		 (at-most-one ("from-ebs" from-ebs?))
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
		 (at-most-one ("verbose" verbose?))
		 (at-most-one ("imprecise-inexacts" imprecise-inexacts?))
		 (required (pathname "pathname" string-argument)))
 (when (and unabbreviate-executably? unabbreviate-nonrecursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-nonrecursive-closures"))
 (when (and unabbreviate-executably? unabbreviate-recursive-closures?)
  (compile-time-error "Can't specify both -unabbreviate-executably and -unabbreviate-recursive-closures"))
 (set! *include-path*
       (append '(".") include-path '("/usr/local/stalingrad/include")))
 (set! *flow-analysis?* (or flow-analysis? flow-analysis-result? compile?))
 (set! *compile?* compile?)
 (when expression-equality-using-identity?
  (set! *expression-equality* 'identity))
 (when expression-equality-using-structural?
  (set! *expression-equality* 'structural))
 (when expression-equality-using-alpha? (set! *expression-equality* 'alpha))
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
 (set! *verbose?* verbose?)
 (set! *imprecise-inexacts?* imprecise-inexacts?)
 (initialize-basis!)
 (let loop ((es (read-source pathname)) (ds '()))
  (unless (null? es)
   (if (definition? (first es))
       (loop (rest es) (cons (first es) ds))
       (let ((e (expand-definitions (reverse ds) (first es))))
	(syntax-check-expression! e)
	(let ((result (parse e)))
	 (cond
	  (flow-analysis?
	   (set! *run?* #f)
	   (if from-ebs?
	       (let* ((ebs (read-ebs-from-file pathname))
		      (bs (second ebs))
		      (bs1 (expression-binding-flow
			    (lookup-expression-binding (first ebs) bs))))
		(unless (= (length bs1) 1) (internal-error))
		(pp (externalize (environment-binding-value (first bs1))))
		(newline)
		(pp (externalize-analysis bs))
		(newline))
	       (let* ((bs (flow-analysis (first result) (second result)))
		      (bs1 (expression-binding-flow
			    (lookup-expression-binding (first result) bs))))
		(unless (= (length bs1) 1) (internal-error))
		(pp (externalize (environment-binding-value (first bs1))))
		(newline)
		(pp (externalize-analysis bs))
		(newline))))
	  (flow-analysis-result?
	   (set! *run?* #f)
	   (if from-ebs?
	       (let* ((ebs (read-ebs-from-file pathname))
		      (bs (expression-binding-flow
			   (lookup-expression-binding
			    (first ebs) (second ebs)))))
		(unless (= (length bs) 1) (internal-error))
		(pp (externalize (environment-binding-value (first bs))))
		(newline))
	       (let ((bs (expression-binding-flow
			  (lookup-expression-binding
			   (first result)
			   (flow-analysis (first result) (second result))))))
		(unless (= (length bs) 1) (internal-error))
		(pp (externalize (environment-binding-value (first bs))))
		(newline))))
	  (compile?
	   (set! *run?* #f)
	   (if from-ebs?
	       (let ((ebs (read-ebs-from-file pathname)))
		(generate-file
		 (generate (first ebs) (second ebs) (second result))
		 pathname)
		;; needs work: -c -k -cc -copt
		(system (format #f "gcc -o ~a -Wall ~a -lm"
				(strip-extension pathname)
				(replace-extension pathname "c"))))
	       (let ((bs (flow-analysis (first result) (second result))))
		;; needs work: This overwrites the code file and the ebs file
		;;             for all but the last top-level expression. And
		;;             it fails to delete those files if there is no
		;;             top-level expression.
		(when ebs?
		 (write-ebs-to-file (list (first result) bs) pathname))
		(generate-file
		 (generate (first result) bs (second result)) pathname)
		;; needs work: -c -k -cc -copt
		(system (format #f "gcc -o ~a -Wall ~a -lm"
				(strip-extension pathname)
				(replace-extension pathname "c"))))))
	  (else
	   (set! *run?* #t)
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
		 (evaluate (first result)
			   'unspecified
			   (list->vector
			    (map value-binding-value (second result))))))))))
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
