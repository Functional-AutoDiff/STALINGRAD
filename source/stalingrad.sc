(MODULE STALINGRAD (WITH QOBISCHEME XLIB STALINGRADLIB-STUFF) (MAIN MAIN))
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
(include "stalingrad.sch")

(set! *program* "stalingrad")
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
		 (at-most-one ("evaluated" evaluated?))
		 (at-most-one ("show-access-indices" show-access-indices?))
		 (at-most-one
		  ("last"n-last? (n-last "n" integer-argument 10)))
		 (at-most-one
		  ("trace" trace?)
		  ("trace-closures-by-argument" trace-closures-by-argument?)
		  ("trace-closures-by-body" trace-closures-by-body?))
		 (at-most-one ("trace-argument/result" trace-argument/result?))
		 (at-most-one ("unabbreviate-recursive-closures"
			       unabbreviate-recursive-closures?))
		 (required (pathname "pathname" string-argument)))
 (initialize-basis!)
 (set! *include-path*
       (append '(".") include-path '("/usr/local/stalingrad/include")))
 (set! *show-access-indices?* show-access-indices?)
 (set! *n-last* n-last)
 (cond (trace? (set! *trace* #t))
       (trace-closures-by-argument? (set! *trace* 'argument))
       (trace-closures-by-body? (set! *trace* 'body)))
 (set! *trace-argument/result?* *trace-argument/result?*)
 (set! *unabbreviate-recursive-closures?* *unabbreviate-recursive-closures?*)
 (let ((es (read-source pathname)))
  (unless (null? es)
   (let ((e (expand-definitions (but-last es) (last es))))
    (syntax-check-expression! e)
    (let ((result (concrete->abstract-expression e)))
     (when undecorated?
      (pp (abstract->concrete (first result)))
      (newline))
     (when evaluated?
      (pp (externalize (evaluate (first result) #f (second result))))
      (newline)))))))

;;; Tam V'Nishlam Shevah L'El Borei Olam
