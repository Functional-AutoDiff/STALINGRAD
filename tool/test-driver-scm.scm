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
		 (->namestring my-pathname) "../examples/ "))

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

(define (shell-command-output command #!optional input)
  ;; It seems the micro-optimization of not bothering with an empty
  ;; input port actually makes a big difference to the speed of the
  ;; fast test suite.
  (if (or (default-object? input) (equal? input ""))
      (with-output-to-string
	(lambda ()
	  (run-shell-command command)))
      (with-output-to-string
	(lambda ()
	  (run-shell-command command 'input (open-input-string input))))))

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

(define with-input? (tagged-list? 'with-inputs))
(define input-forms cadr)
(define answer-form caddr)

;;; Checking that answers are as expected

(define (matches? expected reaction)
  (define (structure-matches? expected gotten)
    (if (number? expected)
	;; TODO I really should put this in the recursive case
	;; too (and get the numerics right).
	(< (abs (- expected gotten)) 1e-10)
	(equal? expected gotten)))
  (if (error? expected)
      (re-string-search-forward (error-message expected) reaction)
      (let ((result (with-input-from-string reaction read-all)))
	(if (multiform? expected)
	    (structure-matches? (multi-forms expected) result)
	    (and (= 1 (length result))
		 (structure-matches? expected (car result)))))))

(define (frobnicate string)
  ;; It appears that the latest binary of Stalingrad I have access
  ;; to emits an interesting message on startup.
  (string-tail
   string
   (string-length "***** INITIALIZEVAR Duplicately defined symbol MAP-REDUCE
***** INITIALIZEVAR Duplicately defined symbol GENSYM
")))

;;;; Expectations

;;; An expectation object defines a situation that a VLAD
;;; implementation may be subjected to, and expectations for how it
;;; should react to that situation.  For example, executing it on a
;;; file containing certain forms.  An expectation object can be
;;; turned into a test in the test-manager/ framework's sense, testing
;;; whether the Stalingrad interpreter or the Stalingrad compiler
;;; produce the expected results.

(define-structure
  (expectation
   (safe-accessors #t)
   (constructor %make-expectation)
   (print-procedure
    (simple-unparser-method 'expected
     (lambda (expectation)
       (expectation->list expectation)))))
  name
  compile?
  forms
  inputs
  answer)

(define (update-expectation-name expectation new-name)
  (%make-expectation
   new-name
   (expectation-compile? expectation)
   (expectation-forms expectation)
   (expectation-inputs expectation)
   (expectation-answer expectation)))

(define (make-expectation test answer)
  (define test-forms (if (multiform? test)
			 (multi-forms test)
			 (list test)))
  (define the-input (if (with-input? answer)
			(input-forms answer)
			'()))
  (define the-answer (if (with-input? answer)
			 (answer-form answer)
			 answer))
  (%make-expectation #f #f test-forms the-input the-answer))

(define (expectation->list expectation)
  (list (expectation-name expectation)
	(expectation-compile? expectation)
	(expectation-forms expectation)
	(expectation-inputs expectation)
	(expectation-answer expectation)))

(define (list->expectation lst)
  (%make-expectation (car lst) (cadr lst) (caddr lst) (cadddr lst) (car (cddddr lst))))

;;; Varying the expectations for compilation

;;; The compiler has some differences from and restrictions relative
;;; the interpreter.  Expectations are written with the interpreter in
;;; mind, and need to be adjusted for the compiler.  There are two
;;; ways to get a compilable expectation out of an interpreted one,
;;; depending on whether the return value of the expression being
;;; tested can be checked in the compiled program.  Also, some tests
;;; cannot usefully be converted to testing the compiler at all.

(define (writing-value-version expectation)
  (define (writing-value forms)
    (append (except-last-pair forms)
	    `((write-real (real ,(car (last-pair forms)))))))
  (%make-expectation
   (expectation-name expectation)
   #t
   (writing-value (expectation-forms expectation))
   (expectation-inputs expectation)
   (expectation-answer expectation)))

(define (ignoring-value-version expectation)
  (define (ignoring-value expect)
    (cond ((multiform? expect)
	   `(multiform ,@(except-last-pair (multi-forms expect))))
	  ((error? expect) expect)
	  (else (error "Can't ignore the only expectation"))))
  (%make-expectation
   (expectation-name expectation)
   #t
   (expectation-forms expectation)
   (expectation-inputs expectation)
   (ignoring-value (expectation-answer expectation))))

(define (compiling-version expectation)
  (if (any exact-string? (expectation-forms expectation))
      #f
      (let ((expect (expectation-answer expectation)))
	(cond ((or (number? expect)
		   (error? expect)
		   (and (multiform? expect)
			(every number? (multi-forms expect))))
	       (writing-value-version expectation))
	      ((and (multiform? expect)
		    (every number? (except-last-pair (multi-forms expect))))
	       (ignoring-value-version expectation))
	      (else
	       #f)))))

;;; Checking whether the interpreter behaved as expected

(define (interpretation-discrepancy expectation)
  (let* ((forms (expectation-forms expectation))
	 (expected (expectation-answer expectation))
	 (inputs (expectation-inputs expectation))
	 (input-report-slot (if (null? inputs) '() `(on ,inputs)))
	 (reaction (interpreter-reaction-to forms inputs (expectation-name expectation))))
    (if (matches? expected reaction)
	#f
	`(interpreting ,forms ,@input-report-slot produced ,reaction expected ,expected))))

(define (interpreter-reaction-to forms inputs basename)
  (write-forms forms basename)
  (let ((input-string (with-output-to-string
			(lambda () (for-each pp inputs)))))
    (frobnicate
     (shell-command-output
      (string-append stalingrad-command test-directory basename ".vlad")
      input-string))))

;;; Checking whether the compiler behaved as expected

(define (compilation-discrepancy expectation)
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
	      `(running ,forms ,@input-report-slot produced ,run-reaction expected ,expected)))
	(if (error? expected)
	    (if (matches? expected compiler-reaction)
		#f
		`(compiling ,forms produced ,compiler-reaction expected ,expected))
	    `(compiling ,forms produced ,compiler-reaction)))))

(define (compilation-reaction-to forms basename)
  (write-forms forms basename)
  (frobnicate
   (shell-command-output
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
    (shell-command-output (string-append "./" test-directory basename) input-string)))

;;; Detecting discrepancies in general

(define (discrepancy expectation)
  (if (expectation-compile? expectation)
      (compilation-discrepancy expectation)
      (interpretation-discrepancy expectation)))

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

;;; The procedure INDEPENDENT-EXPECTATIONS parses a file explicitly of
;;; tests.  Every form in the file is taken to be separate (though
;;; small bundles of forms can be denoted with the (multiform ...)
;;; construct) and produces its own expectation.
(define (independent-expectations forms)
  (let loop ((answers '())
	     (forms forms))
    (cond ((null? forms)
	   (reverse answers))
	  ((null? (cdr forms))
	   (reverse (cons (make-expectation (car forms) #t) answers)))
	  ((eq? '===> (cadr forms))
	   (loop (cons (make-expectation (car forms) (caddr forms)) answers)
		 (cdddr forms)))
	  (else
	   (loop (cons (make-expectation (car forms) #t) answers)
		 (cdr forms))))))

;;; The procedure SHARED-DEFINITIONS-EXPECTATIONS parses a file that
;;; could be a VLAD program.  Definitions and includes appearing at
;;; the top level of the file are taken to be shared by all following
;;; non-definition expressions, but each non-definition expression
;;; produces its own expectation.
(define (shared-definitions-expectations forms)
  (define (definition? form)
    (and (pair? form)
	 (or (eq? (car form) 'define)
	     (eq? (car form) 'include))))
  (let loop ((answers '())
	     (forms forms)
	     (definitions '()))
    (define (expect answer)
      (cons (make-expectation `(multiform ,@(reverse definitions) ,(car forms)) answer)
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

;;;; Parsing data files into expectations

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

(define ((file->expectations parse) filename)
  (if (file-exists? filename)
      (let ((expectations (parse (read-forms filename))))
	(append
	 (expectations-named
	  (file-basename filename)
	  expectations)
	 (expectations-named
	  (string-append "compile-" (file-basename filename))
	  (filter-map compiling-version expectations))))
      (begin
	(warn "File of examples not found" filename)
	'())))

(define (fast-expectations)
  (with-working-directory-pathname my-pathname
   (lambda ()
     (with-working-directory-pathname
      "../examples/"
      (lambda ()
	(append
	 ((file->expectations independent-expectations) "one-offs.vlad")
	 (append-map
	  (file->expectations shared-definitions-expectations)
	  '("addition.vlad"
	    "list-of-unknown-length.vlad"
	    "even-odd.vlad"
	    "example-forward.vlad"
	    "factorial.vlad"
	    "bug-a.vlad"
	    "bug-b.vlad"
	    "bug-c.vlad"
	    "bug0.vlad"
	    "bug1.vlad"
	    "bug2.vlad"
	    "bug3.vlad"
	    "bug4.vlad"
	    "marble.vlad"
	    "prefix.vlad"
	    "secant.vlad"
	    "sqrt.vlad"
	    ))))))))

(define (slow-expectations)
  (with-working-directory-pathname
   my-pathname
   (lambda ()
     (with-working-directory-pathname
      "../examples/"
      (lambda ()
	(append-map
	 (file->expectations shared-definitions-expectations)
	 '("example.vlad"
	   "double-agent.vlad"
	   "hessian.vlad"
	   "saddle.vlad"
	   "triple.vlad"
	   "dn.vlad"
	   "series.vlad"
	   "slow-sqrt.vlad"
	   )))))))

(define (all-expectations)
  (append (fast-expectations) (slow-expectations)))

;;;; Entry points

;;; Saving expectations to disk

(define (save-expectation expectation)
  (with-output-to-file
      (string-append test-directory (expectation-name expectation) ".expect")
    (lambda ()
      (pp (expectation->list expectation)))))

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
