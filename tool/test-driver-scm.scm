(declare (usual-integrations))

;;; Pulling in dependencies

(load-option 'synchronous-subprocess)

(define (self-relatively thunk)
  (if (current-eval-unit #f)
      (with-working-directory-pathname
       (directory-namestring (current-load-pathname))
       thunk)
      (thunk)))

;;; File system manipulations

(define my-pathname (self-relatively working-directory-pathname))
(define test-directory "test-runs/last/")
(define stalingrad-command
  (string-append (->namestring my-pathname) "../source/stalingrad -scmh 1000 -I "
		 (->namestring my-pathname) "../examples/automatic/ "))

(define (read-all)
  (let loop ((results '())
	     (form (read)))
    (if (eof-object? form)
	(reverse results)
	(loop (cons form results) (read)))))

(define (read-forms filename)
  (with-input-from-file filename read-all))

(define (write-forms forms basename)
  (define (dispatched-write form)
    (if (exact-string? form)
	(write-string (exact-string form))
	(begin (pp form)
	       (newline))))
  (with-output-to-file (string-append test-directory basename ".vlad")
    (lambda ()
      (for-each dispatched-write forms))))

(load-option 'regular-expression)

(define (shell-command-output basename command #!optional input)
  (define (doit)
    (if (or (default-object? input) (equal? input ""))
	(with-output-to-string
	  (lambda ()
	    (run-shell-command command)))
	(let ((input-file-name (string-append test-directory basename ".input")))
	  (with-output-to-file input-file-name
	    (lambda ()
	      (display input)
	      (newline)))
	  (with-output-to-string
	    (lambda ()
	      (run-shell-command (string-append command " < " input-file-name)))))))
  (let ((answer (doit)))
    (cond ((or (re-string-search-forward "bash: line [0-9]+:[0-9 ]*Killed" answer)
	       (re-string-search-forward "bash: line [0-9]+:[0-9 ]*Aborted" answer))
	   (display answer)
	   (newline)
	   (error "Subprocess reports being terminated"))
	  (else
	   answer))))

(define (write-makefile directory)
  (with-working-directory-pathname directory
   (lambda ()
     (with-output-to-file "Makefile"
       (lambda ()
	 (display
"EXPECTATIONS=$(wildcard *.expect)
FAILURE_REPORTS=$(EXPECTATIONS:.expect=.fail)

all: $(FAILURE_REPORTS)

%.fail: %.expect
	-../../tool/one-test $*

.PHONY: all
"))))))

;;; Special syntax

(define ((tagged-list? tag) thing)
  (and (pair? thing)
       (eq? tag (car thing))))

(define multiform? (tagged-list? 'multiform))
(define multi-forms cdr)

(define exact-string? (tagged-list? 'exact-string))
(define exact-string cadr)

(define error? (tagged-list? 'error))
(define error-message cadr)

(define alternate-behaviors? (tagged-list? 'or))
(define behavior-alternatives cdr)

(define with-input? (tagged-list? 'with-inputs))
(define input-forms cadr)
(define answer-form caddr)

;;; Checking that answers are as expected

(define (matches? expected reaction)
  (define (structure-matches? expected gotten)
    (cond ((number? expected)
	   ;; TODO I really should get the numerics right here.
	   (< (abs (- expected gotten)) 1e-10))
	  ((pair? expected)
	   (and (pair? gotten)
		(structure-matches? (car expected) (car gotten))
		(structure-matches? (cdr expected) (cdr gotten))))
	  (else
	   (equal? expected gotten))))
  (cond ((error? expected)
	 (re-string-search-forward (error-message expected) reaction))
	((alternate-behaviors? expected)
	 (any (lambda (alternate)
		(matches? alternate reaction))
	      (behavior-alternatives expected)))
	(else
	 (let ((result (with-input-from-string reaction read-all)))
	   (if (multiform? expected)
	       (structure-matches? (multi-forms expected) result)
	       (and (= 1 (length result))
		    (structure-matches? expected (car result))))))))

(define (frobnicate string)
  ;; It appears that the latest binary of Stalingrad I have access
  ;; to emits an interesting message on startup.
  (string-tail
   string
   (string-length "***** INITIALIZEVAR Duplicately defined symbol GENSYM
")))

;;;; Expectations

;;; An expectation object defines a situation that a VLAD
;;; implementation may be subjected to, and expectations for how it
;;; should react to that situation.  For example, executing said
;;; implementation on a file containing certain forms.  When
;;; originally parsed from a file, an expectation will be
;;; implementation-agnostic, but each implementation can specialize
;;; the expectation to itself.  These specialized expectations can be
;;; serialized and then deserialized and executed by a standalone,
;;; parallel-safe process.

(define-structure
  (expectation
   (safe-accessors #t)
   (constructor %make-expectation)
   (print-procedure
    (simple-unparser-method 'expected
     (lambda (expectation)
       (expectation->list expectation)))))
  name
  implementation
  forms
  inputs
  answer)

(define (update-expectation-name expectation new-name)
  (%make-expectation
   new-name
   (expectation-implementation expectation)
   (expectation-forms expectation)
   (expectation-inputs expectation)
   (expectation-answer expectation)))

(define (make-expectation test-forms answer)
  (define the-input (if (with-input? answer)
			(input-forms answer)
			'()))
  (define the-answer (if (with-input? answer)
			 (answer-form answer)
			 answer))
  (%make-expectation #f #f test-forms the-input the-answer))

(define (expectation->list expectation)
  (list (expectation-name expectation)
	(if (implementation? (expectation-implementation expectation))
	    (implementation-name (expectation-implementation expectation))
	    #f)
	(expectation-forms expectation)
	(expectation-inputs expectation)
	(expectation-answer expectation)))

(define (list->expectation lst)
  (%make-expectation
   (car lst) (deserialize-implementation (cadr lst))
   (caddr lst) (cadddr lst) (car (cddddr lst))))

(define (deserialize-implementation name)
  (demand-assq name (map (lambda (impl)
			   (cons (implementation-name impl) impl))
			 implementations)))

(define (demand-assq item alist)
  (let ((answer (assq item alist)))
    (if answer (cdr answer) (error "Not found" item))))

(define-structure rejection
  expectation
  reason)

(define (rejection->list rejection)
  (cons (rejection-reason rejection)
	(expectation->list (rejection-expectation rejection))))

(define (rejection-name rejection)
  (expectation-name (rejection-expectation rejection)))

;;;; Implementations

;;; An implementation object contains all the information I need in
;;; order to test a given expectation against the corresponding
;;; implementation of VLAD.  There are two interesting parts to this:
;;; one is a PREPARER procedure, which specializes an
;;; implementation-agnostic expectation for this implementation (that
;;; is, accounts for programmatically account-for-able differences in
;;; the language being implemented, with the possibility or completely
;;; rejecting an expectation that cannot usefully test this
;;; implementation).  The other is a DISCREPANCY procedure, which
;;; actually executes an already-specialized expectation in this
;;; implementation, and reports any discrepancies between what
;;; happened and what was expected.  Finally, an implementation object
;;; also has a NAME which is used for serializations.

(define-structure (implementation safe-accessors)
  name
  preparer
  discrepancy)

;;; Stalingrad used as an interpreter
(define (stalingrad-interpreter)

  ;;; Stalingrad the interpreter is currently the gold standard
  ;;; definition of the VLAD language, so not much needs to be done to
  ;;; prepare an expectation for running with it.
  (define (prepare expectation)
    (%make-expectation
     (string-append "interpret-" (expectation-name expectation))
     the-interpreter
     (expectation-forms expectation)
     (expectation-inputs expectation)
     (expectation-answer expectation)))

  ;;; Checking whether the interpreter behaved as expected
  (define (discrepancy expectation)
    (let* ((forms (expectation-forms expectation))
	   (expected (expectation-answer expectation))
	   (inputs (expectation-inputs expectation))
	   (input-report-slot (if (null? inputs) '() `(on ,inputs)))
	   (reaction (reaction-to
		      forms inputs (expectation-name expectation))))
      (if (matches? expected reaction)
	  #f
	  `( interpreting ,forms
	     ,@input-report-slot
	     produced ,reaction
	     expected ,expected))))

  (define (reaction-to forms inputs basename)
    (write-forms forms basename)
    (let ((input-string (with-output-to-string
			  (lambda () (for-each pp inputs)))))
      (frobnicate
       (shell-command-output basename
	(string-append stalingrad-command test-directory basename ".vlad")
	input-string))))

  (define the-interpreter
    (make-implementation 'stalingrad-interpreter prepare discrepancy))

  the-interpreter)

;;; Stalingrad used as a compiler

(define (stalingrad-compiler)

  ;;; Varying the expectations for compilation

  ;;; The compiler has some differences from and restrictions relative
  ;;; the interpreter.  Expectations are written with the interpreter in
  ;;; mind, and need to be adjusted for the compiler.  There are three
  ;;; ways to get a compilable expectation out of an interpreted one,
  ;;; depending on whether and how the return value of the expression being
  ;;; tested can be checked in the compiled program.  Also, some tests
  ;;; cannot usefully be converted to testing the compiler at all.

  ;;; The three ways to adapt interpretation to compilation are as
  ;;; follows.  If the interpreted program is expected to write only
  ;;; real numbers and return a real number, it can be converted to a
  ;;; compiled program simply by wrapping the final expression in
  ;;; (write-real (real ...)) to force the compiled program to print
  ;;; the answer.  This option is checked with WRITABLE-EXPECTATION?
  ;;; and the transformation implemented with WRITING-VALUE-VERSION.

  ;;; If the interpreted program is expected to write only real
  ;;; numbers and return a list structure containing real numbers and
  ;;; booleans, then the compiled program can be modified to compute
  ;;; that answer, and then recursively traverse it, checking that the
  ;;; shape is right and printing out the real numbers inside.  To
  ;;; check that the shape is right, the shape needs to be fed in as a
  ;;; quoted constant into the compiled program.  This check is done
  ;;; by CAREFULLY-WRITABLE-EXPECTATION?, and the transformation
  ;;; effected by CAREFULLY-WRITING-VERSION.

  ;;; Finally, as a stopgap measure, if the interpreted program is
  ;;; expected to write some nonzero quantity of real numbers, but
  ;;; return some other structure, a partial test of the compiled
  ;;; program can be arranged by simply ignoring the expectation of
  ;;; the returned structure and observing only the printouts.  This
  ;;; possibility is checked by IGNORABLE-EXPECTATION?, and this
  ;;; transformation effected by IGNORING-VALUE-VERSION.

  ;;; Failing all that, the expectation will be rejected.  Explicitly,
  ;;; any expectation that contains an exact string to be reproduced
  ;;; will rejected, because such cannot be effectively adjusted; any
  ;;; expectation that expects any outputs in addition to the return
  ;;; value that are not real numbers will be rejected, because it is
  ;;; impossible to track down the places where those outputs would
  ;;; occur and replace them with real-only outputs; and any
  ;;; expectation that expects only a return value, but whose return
  ;;; value cannot be serialized conveniently into real numbers within
  ;;; the program under test will be rejected as well.

  (define (prepare expectation)
    (define (reject reason)
      (make-rejection
       (%make-expectation
	(string-append "compile-" (expectation-name expectation))
	the-compiler
	(expectation-forms expectation)
	(expectation-inputs expectation)
	(expectation-answer expectation))
       reason))
    (let ((expect (expectation-answer expectation)))
      (cond ((any exact-string? (expectation-forms expectation))
	     (reject "Not compiling exact string expectation"))
	    ((and (multiform? expect)
		  (not (every number? (except-last-pair (multi-forms expect)))))
	     (reject "Not compiling expectation that depends on internal write"))
	    ((writable-expectation? expect)
	     (writing-value-version expectation))
	    ((carefully-writable-expectation? expect)
	     (carefully-writing-version expectation))
	    ((ignorable-expectation? expect)
	     (ignoring-value-version expectation))
	    (else
	     (reject
	      "Not compiling expectation with single non-writable answer")))))

  (define (writable-expectation? expect)
    (or (number? expect)
	(error? expect)
	(and (multiform? expect)
	     (every number? (multi-forms expect)))
	(and (alternate-behaviors? expect)
	     (every writable-expectation? (behavior-alternatives expect)))))

  (define (writing-value-version expectation)
    (define (writing-value forms)
      (append (except-last-pair forms)
	      `((write-real (real ,(car (last-pair forms)))))))
    (%make-expectation
     (string-append "compile-" (expectation-name expectation))
     the-compiler
     (writing-value (expectation-forms expectation))
     (expectation-inputs expectation)
     (expectation-answer expectation)))

  (define (carefully-writable-expectation? expect)
    (define (carefully-writable-form? expect-form)
      (or (number? expect-form)
	  (null? expect-form)
	  (boolean? expect-form)
	  (and (pair? expect-form)
	       (carefully-writable-form? (car expect-form))
	       (carefully-writable-form? (cdr expect-form)))))
    (or (carefully-writable-form? expect)
	(and (multiform? expect)
	     (every number? (except-last-pair (multi-forms expect)))
	     (carefully-writable-form?
	      (car (last-pair (multi-forms expect)))))))

  (define (carefully-writing-version expectation)
    (define careful-write
      (let ((bogon (- (random 1.) 1001)))
	`(define (carefully-write-shaped-object shape object)
	   (let ((fail (lambda () (write-real (real ,bogon)))))
	     (letrec ((loop
		       (lambda (shape object)
			 (cond ((and (real? shape) (real? object))
				(write-real (real object)))
			       ((and (pair? shape) (pair? object))
				(let (((cons shape-car shape-cdr) shape)
				      ((cons object-car object-cdr) object))
				  (let ((x (loop shape-car object-car)))
				    (cons x (loop shape-cdr object-cdr)))))
			       ((and (null? shape) (null? object))
				'())
			       ((and (boolean? shape) (boolean? object))
				(if (and shape object)
				    (real 1)
				    (if (or shape object)
					(fail)
					(real 0))))
			       (else
				(fail))))))
	       (loop shape object))))))
    (define (carefully-written-expected-return-value expect)
      `(multiform
	,@(let loop ((expect expect))
	    (cond ((number? expect) `(,expect))
		  ((pair? expect) `(,@(loop (car expect)) ,@(loop (cdr expect))))
		  ((boolean? expect) '())
		  ((null? expect) '())))))
    (define (zero-out expect)
      (cond ((number? expect) 0)
	    ((pair? expect)
	     (cons (zero-out (car expect)) (zero-out (cdr expect))))
	    ((boolean? expect) expect)
	    ((null? expect) '())))
    (define (get-final-answer answer)
      (if (multiform? answer)
	  (car (last-pair (multi-forms answer)))
	  answer))
    (let ((final-answer (get-final-answer (expectation-answer expectation))))
      (define (carefully-writing-value forms)
	(append (except-last-pair forms)
		(list careful-write
		      `(carefully-write-shaped-object ',(zero-out final-answer)
			,(car (last-pair forms))))))
      (define (carefully-written-answer expect)
	(cond ((multiform? expect)
	       `(multiform ,@(except-last-pair (multi-forms expect))
			   ,@(multi-forms
			      (carefully-written-expected-return-value
			       final-answer))))
	      (else (carefully-written-expected-return-value final-answer))))
      (%make-expectation
       (string-append "compile-" (expectation-name expectation))
       the-compiler
       (carefully-writing-value (expectation-forms expectation))
       (expectation-inputs expectation)
       (carefully-written-answer (expectation-answer expectation)))))

  (define (ignorable-expectation? expect)
    (or (and (multiform? expect)
	     (every number? (except-last-pair (multi-forms expect))))
	(and (alternate-behaviors? expect)
	     (every ignorable-expectation? (behavior-alternatives expect)))))

  (define (ignoring-value-version expectation)
    (define (ignoring-value expect)
      (cond ((multiform? expect)
	     `(multiform ,@(except-last-pair (multi-forms expect))))
	    ((error? expect) expect)
	    (else (error "Can't ignore the only expectation"))))
    (%make-expectation
     (string-append "compile-" (expectation-name expectation))
     the-compiler
     (expectation-forms expectation)
     (expectation-inputs expectation)
     (ignoring-value (expectation-answer expectation))))

  ;;; Checking whether the compiler behaved as expected

  (define (discrepancy expectation)
    (define (error-possible? expected)
      (or (error? expected)
	  (and (alternate-behaviors? expected)
	       (any error-possible? expected))))
    (let* ((name (expectation-name expectation))
	   (expected (expectation-answer expectation))
	   (forms (expectation-forms expectation))
	   (inputs (expectation-inputs expectation))
	   (input-report-slot (if (null? inputs) '() `(on ,inputs)))
	   (compiler-reaction (compilation-reaction-to forms name)))
      (if (equal? "" compiler-reaction)
	  (let ((run-reaction (execution-reaction inputs name)))
	    (if (matches? expected run-reaction)
		#f
		`( running ,forms
			   ,@input-report-slot
			   produced ,run-reaction
			   expected ,expected)))
	  (if (error-possible? expected)
	      (if (matches? expected compiler-reaction)
		  #f
		  `( compiling ,forms
			       produced ,compiler-reaction
			       expected ,expected))
	      `( compiling ,forms
			   produced ,compiler-reaction)))))

  (define (compilation-reaction-to forms basename)
    (write-forms forms basename)
    (frobnicate
     (shell-command-output basename
      (string-append
       stalingrad-command
       ;; -imprecise-inexacts causes some "Warning: Arguments to bundle
       ;; might not conform" that's confusing the test suite.
       "-compile -k -imprecise-inexacts -no-warnings "
       test-directory
       basename
       ".vlad"))))

  (define (execution-reaction forms basename)
    (let ((input-string (with-output-to-string
			  (lambda () (for-each pp forms)))))
      (shell-command-output basename (string-append "./" test-directory basename)
			    input-string)))

  (define the-compiler
    (make-implementation 'stalingrad-compiler prepare discrepancy))

  the-compiler)

(define (slad)
  (define (prepare expectation)
    (%make-expectation
     (string-append "slad-" (expectation-name expectation))
     slad-interpreter
     (expectation-forms expectation)
     (expectation-inputs expectation)
     (strip-perturbation-tags (expectation-answer expectation))))

  (define (strip-perturbation-tags form)
    (cond ((and (pair? form)
		(eq? (car form) 'perturbation)
		(= 2 (length form)))
	   (strip-perturbation-tags (cadr form)))
	  ((pair? form)
	   (cons (strip-perturbation-tags (car form))
		 (strip-perturbation-tags (cdr form))))
	  (else
	   form)))

  (define (discrepancy expectation)
    (let* ((forms (expectation-forms expectation))
	   (expected (expectation-answer expectation))
	   (inputs (expectation-inputs expectation))
	   (input-report-slot (if (null? inputs) '() `(on ,inputs)))
	   (reaction (reaction-to
		      forms inputs (expectation-name expectation))))
      (if (matches? expected reaction)
	  #f
	  `( interpreting ,forms
	     ,@input-report-slot
	     produced ,reaction
	     expected ,expected))))

  (define slad-command (string-append (->namestring my-pathname)
				      "../../BCL-AD/slad/slad "))

  (define (reaction-to forms inputs basename)
    (write-forms forms basename)
    (let ((input-string (with-output-to-string
			  (lambda () (for-each pp inputs)))))
      (shell-command-output basename
       (string-append slad-command test-directory basename ".vlad")
       input-string)))

  (define slad-interpreter
    (make-implementation 'slad-interpreter prepare discrepancy))

  slad-interpreter)

(define (vl)
  (define (prepare expectation)
    (%make-expectation
     (string-append "vl-" (expectation-name expectation))
     vl-compiler
     (expectation-forms expectation)
     (expectation-inputs expectation)
     (expectation-answer expectation)))

  (define (discrepancy expectation)
    (let* ((forms (expectation-forms expectation))
	   (expected (expectation-answer expectation))
	   (inputs (expectation-inputs expectation))
	   (input-report-slot (if (null? inputs) '() `(on ,inputs)))
	   (reaction (reaction-to
		      forms inputs (expectation-name expectation))))
      (if (matches? expected reaction)
	  #f
	  `( running ,forms
	     ,@input-report-slot
	     produced ,reaction
	     expected ,expected))))

  (define vl-command (string-append (->namestring my-pathname)
				      "../../BCL-AD/vl/vl "))

  (define (reaction-to forms inputs basename)
    (write-forms forms basename)
    (let ((input-string (with-output-to-string
			  (lambda () (for-each pp inputs)))))
      (shell-command-output basename
       (string-append vl-command test-directory basename ".vlad")
       input-string)))

  (define vl-compiler
    (make-implementation 'vl-compiler prepare discrepancy))

  vl-compiler)

;;;; General treatment of discrepancies

(define (discrepancy expectation)
  ((implementation-discrepancy
    (expectation-implementation expectation))
   expectation))

(define (report-discrepancy discrepancy)
  (for-each
   (lambda (discrepancy-elt)
     (cond ((memq discrepancy-elt '(compiling interpreting produced expected))
	    (display (string-capitalize (symbol->string discrepancy-elt)))
	    (newline))
	   ((string? discrepancy-elt)
	    (display discrepancy-elt))
	   (else (pp discrepancy-elt))))
   discrepancy))

(define (report-if-discrepancy expectation)
  (let ((maybe-trouble (discrepancy expectation)))
    (if maybe-trouble
	(report-discrepancy maybe-trouble)
	'ok)))

;;;; Parsing expectations from files of examples

;;; The procedure SHARED-DEFINITIONS-EXPECTATIONS parses a file that
;;; could be a VLAD program (except for special testing directives, if
;;; any).  Definitions and includes appearing at the top level of the
;;; file are taken to be shared by all following non-definition
;;; expressions, but each non-definition expression produces its own
;;; expectation.
(define (shared-definitions-expectations forms)
  (define (definition? form)
    (and (pair? form)
	 (or (eq? (car form) 'define)
	     (eq? (car form) 'include))))
  (let loop ((answers '())
	     (forms forms)
	     (definitions '()))
    (define (expect answer)
      (cons (make-expectation
	     (let ((query-forms (if (multiform? (car forms))
				    (multi-forms (car forms))
				    (list (car forms)))))
	       (append (reverse definitions) query-forms)) answer)
	    answers))
    (cond ((null? forms)
	   (reverse answers))
	  ((definition? (car forms))
	   (loop answers (cdr forms) (cons (car forms) definitions)))
	  ((null? (cdr forms))
	   (reverse (expect #t)))
	  ((eq? '===> (cadr forms))
	   (loop (expect (caddr forms)) (cdddr forms) definitions))
	  (else
	   (loop (expect #t) (cdr forms) definitions)))))

(define (file-basename filename)
  (->namestring (pathname-new-type filename #f)))

(define (expectations-named basename expectations)
  (define (integer-log number base)
    (if (< number base)
	0
	(+ 1 (integer-log (quotient number base) base))))
  (define (pad string length pad-str)
    (if (>= (string-length string) length)
	string
	(pad (string-append pad-str string) length pad-str)))
  (let* ((count (length expectations))
	 (index-length (+ 1 (integer-log count 10))))
    (define (number->uniform-string index)
       (pad (number->string index) index-length "0"))
    (map (lambda (expectation index)
	   (update-expectation-name
	    expectation
	    (string-append basename "-" (number->uniform-string index))))
	 expectations
	 (iota count 1))))

(define (file->expectations filename)
  (if (file-exists? filename)
      (let* ((expectations (shared-definitions-expectations (read-forms filename)))
	     (named-expectations (expectations-named
				  (file-basename filename)
				  expectations)))
	(append-map
	 (lambda (impl)
	   (filter-map (implementation-preparer impl) named-expectations))
	 implementations))
      (begin
	(warn "File of examples not found" filename)
	'())))

;;;; Definitions of expectation sets

(define implementations
  (list (stalingrad-interpreter)
	(stalingrad-compiler)
	;(slad)
	;(vl)
	))

(define (fast-expectations)
  (with-working-directory-pathname my-pathname
   (lambda ()
     (with-working-directory-pathname
      "../examples/automatic/"
      (lambda ()
	(append-map file->expectations
	 '("one-offs.vlad"
	   "addition.vlad"
	   "basics.vlad"
	   "bug-a.vlad"
	   "bug-b.vlad"
	   "bug-c.vlad"
	   "bug0.vlad"
	   "bug1.vlad"
	   "bug2.vlad"
	   "bug3.vlad"
	   "bug4.vlad"
	   "even-odd.vlad"
	   "example-fast.vlad"
	   "factorial.vlad"
	   "list-of-unknown-length.vlad"
	   "marble.vlad"
	   "multiply.vlad"
	   "prefix.vlad"
	   "secant.vlad"
	   "sqrt.vlad"
	   "typology.vlad")))))))

(define (slow-expectations)
  (with-working-directory-pathname
   my-pathname
   (lambda ()
     (with-working-directory-pathname
      "../examples/automatic/"
      (lambda ()
	(append-map file->expectations
	 '("backprop-F.vlad"
	   "backprop-R.vlad"
	   "dn.vlad"
	   "double-agent.vlad"
	   "example-full.vlad"
	   "hessian.vlad"
	   "particle.vlad"
	   "probabilistic-lambda-calculus.vlad"
	   "probabilistic-prolog.vlad"
	   "saddle.vlad"
	   "series.vlad"
	   "slow-sqrt.vlad"
	   "triple.vlad")))))))

(define (all-expectations)
  (append (fast-expectations) (slow-expectations)))

;;;; Entry points

;;; Saving expectations to disk

(define (save-expectation expectation)
  (if (expectation? expectation)
      (with-output-to-file
	  (string-append test-directory (expectation-name expectation) ".expect")
	(lambda ()
	  (pp (expectation->list expectation))))
      (with-output-to-file
	  (string-append test-directory (rejection-name expectation) ".reject")
	(lambda ()
	  (pp (rejection->list expectation))))))

(define (record-expectations! expectations)
  (write-makefile test-directory)
  (for-each save-expectation expectations)
  (flush-output)
  (%exit 0))

;;; Running an expectation loaded from standard input

(define (read-and-try-expectation!)
  (set! test-directory "./") ;; This entry point is called from the directory where its data is
  (report-if-discrepancy (list->expectation (read)))
  (flush-output)
  (%exit 0))
