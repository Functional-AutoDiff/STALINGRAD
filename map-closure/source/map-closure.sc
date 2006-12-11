(MODULE MAP-CLOSURE (WITH QOBISCHEME XLIB MAP-CLOSURELIB-STUFF) (MAIN MAIN))
;;; LaHaShem HaAretz U'Mloah
;;; $Id$

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
(include "map-closure.sch")

(set! *program* "map-closure")
(set! *panic?* #t)

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
		 (at-most-one ("undecorated" undecorated?))
		 (at-most-one ("cps-converted" cps-converted?))
		 (at-most-one ("closure-converted" closure-converted?))
		 (at-most-one ("metered" metered?))
		 (at-most-one ("show-access-indices" show-access-indices?))
		 (at-most-one
		  ("trace-primitive-procedures" trace-primitive-procedures?))
		 (at-most-one ("trace-closures" trace-closures?))
		 (at-most-one ("trace-argument/result" trace-argument/result?))
		 (at-most-one
		  ("unabbreviate-executably" unabbreviate-executably?))
		 (at-most-one ("unabbreviate-closures" unabbreviate-closures?))
		 (at-most-one ("level" level? (level "n" integer-argument #f)))
		 (at-most-one
		  ("length" length? (length "n" integer-argument #f)))
		 (at-most-one ("pp" pp?))
		 (required (pathname "pathname" string-argument)))
 (when (and unabbreviate-executably? unabbreviate-closures?)
  (panic "Can't specify both -unabbreviate-executably and -unabbreviate-closures"))
 (initialize-basis!)
 (set! *include-path*
       (append '(".") include-path '("/usr/local/map-closure/include")))
 (set! *cps-converted?* cps-converted?)
 (set! *closure-converted?* closure-converted?)
 (set! *metered?* metered?)
 (set! *show-access-indices?* show-access-indices?)
 (set! *trace-primitive-procedures?* trace-primitive-procedures?)
 (set! *trace-closures?* trace-closures?)
 (set! *trace-argument/result?* trace-argument/result?)
 (set! *unabbreviate-executably?* unabbreviate-executably?)
 (set! *unabbreviate-closures?* unabbreviate-closures?)
 (set! *pp?* pp?)
 (let loop ((es (read-source pathname)) (ds '()))
  (unless (null? es)
   (if (definition? (first es))
       (loop (rest es) (cons (first es) ds))
       (let ((e (expand-definitions (reverse ds) (first es))))
	(syntax-check-expression! e)
	(let ((result (parse e)))
	 (when undecorated?
	  (pp (abstract->concrete (first result)))
	  (newline))
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
			 (list->vector (second result)))))))))
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
		    (reverse *value-bindings*))))
	(loop (rest es) ds))))))

;;; Tam V'Nishlam Shevah L'El Borei Olam

;;; Local Variables:
;;; lisp-body-indent: 1
;;; End:
