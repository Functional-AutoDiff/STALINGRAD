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

(define-command (main (at-most-one ("undecorated" undecorated?))
		      (at-most-one ("decorated" decorated?))
		      (at-most-one ("evaluated" evaluated?))
		      (required (pathname "pathname" string-argument)))
 (intialize-basis!)
 (call-with-input-file (default-extension pathname "sc")
  (lambda (input-port)
   (let loop ()
    (let ((e (read input-port)))
     (unless (eof-object? e)
      (syntax-check-expression! e)
      (let ((e (concrete->abstract-expression e)))
       (when undecorated?
	(pp (abstract->undecorated-concrete-expression e))
	(newline))
       (when decorated?
	(pp (abstract->decorated-concrete-expression e))
	(newline))
       (when evaluated?
	(write (evaluate e))
	(newline)))
      (loop)))))))

;;; Tam V'Nishlam Shevah L'El Borei Olam
