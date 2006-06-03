(MODULE STALINGRAD (WITH QOBISCHEME XLIB STALINGRADLIB-STUFF) (MAIN MAIN))
;;; LaHaShem HaAretz U'Mloah

;;; Stalingrad 0.1 - AD for VLAD, a functional language.
;;; Copyright 2004 and 2005 Purdue University. All rights reserved.

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
;;;    http://www-bcl.cs.nuim.ie/~barak/

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
		 (at-most-one ("letrec-as-y" letrec-as-y?))
		 (at-most-one ("flow-analysis" flow-analysis?))
		 (at-most-one ("undecorated" undecorated?))
		 (at-most-one ("metered" metered?))
		 (at-most-one ("show-access-indices" show-access-indices?))
		 (at-most-one
		  ("trace-primitive-procedures" trace-primitive-procedures?))
		 (at-most-one ("trace-nonrecursive-closures"
			       trace-nonrecursive-closures?))
		 (at-most-one
		  ("trace-recursive-closures" trace-recursive-closures?))
		 (at-most-one ("trace-argument/result" trace-argument/result?))
		 (at-most-one
		  ("unabbreviate-executably" unabbreviate-executably?)
		  ("unabbreviate-nicely" unabbreviate-nicely?))
		 (at-most-one ("unabbreviate-transformed"
			       unabbreviate-transformed?))
		 (at-most-one ("unabbreviate-nonrecursive-closures"
			       unabbreviate-nonrecursive-closures?))
		 (at-most-one ("unabbreviate-recursive-closures"
			       unabbreviate-recursive-closures?))
		 (at-most-one ("not-anal" not-anal?))
		 (at-most-one ("level" level? (level "n" integer-argument #f)))
		 (at-most-one
		  ("length" length? (length "n" integer-argument #f)))
		 (at-most-one ("pp" pp?))
		 (at-most-one ("memoized" memoized?))
		 (at-most-one ("church" church?))
		 (at-most-one ("cfa0" cfa0?))
		 (at-most-one
		  ("l1" l1? (l1 "flow-size-limit" integer-argument #f)))
		 (at-most-one
		  ("l2" l2? (l2 "concrete-real-abstract-value-limit"
				integer-argument #f)))
		 (at-most-one
		  ("l3" l3? (l3 "identical-nonrec-closure-abstract-value-limit"
				integer-argument #f)))
		 (at-most-one
		  ("l4" l4? (l4 "identical-rec-closure-abstract-value-limit"
				integer-argument #f)))
		 (at-most-one
		  ("l5" l5? (l5 "nonrec-closure-nesting-depth-limit"
				integer-argument #f)))
		 (at-most-one ("no-anf" no-anf?))
		 (at-most-one ("single-real" single-real?))
		 (at-most-one ("track-flow-analysis" track-flow-analysis?))
		 (at-most-one ("exclude-prior-values" exclude-prior-values?))
		 (at-most-one ("bypass-expand-defs" bypass-expand-defs?))
		 (at-most-one ("x" x? (x "variable" string-argument #f)))
		 (required (pathname "pathname" string-argument)))
 (when (and unabbreviate-executably? unabbreviate-nonrecursive-closures?)
  (panic "Can't specify both -unabbreviate-executably and -unabbreviate-nonrecursive-closures"))
 (when (and unabbreviate-executably? unabbreviate-recursive-closures?)
  (panic "Can't specify both -unabbreviate-executably and -unabbreviate-recursive-closures"))
 (set! *letrec-as-y?* letrec-as-y?)
 (set! *church?* church?)
 (set! *cfa0?* cfa0?)
 (when l1? (set! *l1* l1))
 (when l2? (set! *l2* l2))
 (when l3? (set! *l3* l3))
 (when l4? (set! *l4* l4))
 (when l5? (set! *l5* l5))
 (when no-anf? (set! *anf-convert?* (not no-anf?)))
 (set! *allow-only-single-concrete-real?* single-real?)
 (set! *track-flow-analysis?* track-flow-analysis?)
 (set! *include-prior-values?* (not exclude-prior-values?))
 (initialize-basis!)
 (set! *include-path*
       (append '(".") include-path '("/usr/local/stalingrad/include")))
 (set! *metered?* metered?)
 (set! *show-access-indices?* show-access-indices?)
 (set! *trace-primitive-procedures?* trace-primitive-procedures?)
 (set! *trace-nonrecursive-closures?* trace-nonrecursive-closures?)
 (set! *trace-recursive-closures?* trace-recursive-closures?)
 (set! *trace-argument/result?* trace-argument/result?)
 (set! *unabbreviate-executably?* unabbreviate-executably?)
 (set! *unabbreviate-nicely?* unabbreviate-nicely?)
 (set! *unabbreviate-transformed?* unabbreviate-transformed?)
 (set! *unabbreviate-nonrecursive-closures?*
       unabbreviate-nonrecursive-closures?)
 (set! *unabbreviate-recursive-closures?* unabbreviate-recursive-closures?)
 (set! *anal?* (not not-anal?))
 (set! *pp?* pp?)
 (when x? (set! *x* (read-from-string x)))
 (set! *memoized?* memoized?)
 (let loop ((es (read-source pathname)) (ds '()))
  (unless (null? es)
   (if (definition? (first es))
       (loop (rest es) (cons (first es) ds))
       (let ((e (if bypass-expand-defs?
		    (first es)
		    (expand-definitions (reverse ds) (first es)))))
	(syntax-check-expression! e)
	(let ((result (parse e)))
	 (when undecorated?
	  (pp (abstract->concrete (first result)))
	  (newline))
	 (cond
	  (flow-analysis?
	   (pp (externalize-abstract-analysis
		(flow-analysis (first result) (second result))))
	   (newline))
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
	      length
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
