(declare (usual-integrations))

;;; Pulling in dependencies

(load-option 'synchronous-subprocess)

(define (self-relatively thunk)
  (if (current-eval-unit #f)
      (with-working-directory-pathname
       (directory-namestring (current-load-pathname))
       thunk)
      (thunk)))

(define (load-relative filename)
  (self-relatively (lambda () (load filename))))

;;; File system manipulations

(define (ensure-directory filename)
  (if (file-exists? filename)
      (if (file-directory? filename)
	  'ok
	  (error "Exists and is not a directory" filename))
      (make-directory filename)))

(define my-pathname (self-relatively working-directory-pathname))
(define test-directory "test-runs/")
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
    (if (and (pair? form) (eq? (car form) 'exact-string))
	(write-string (cadr form))
	(begin (pp form)
	       (newline))))
  (with-output-to-file (string-append test-directory basename ".vlad")
    (lambda ()
      (for-each dispatched-write forms))))

(define (shell-command-output command)
  (with-output-to-string
    (lambda ()
      (run-shell-command command))))

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
	-../tool/one-test $*

.PHONY: all
"))))))

;;; Checking that answers are as expected

(define (matches? expected reaction)
  (if (and (pair? expected)
	   (eq? (car expected) 'error))
      (re-string-search-forward (cadr expected) reaction)
      (let ((result (with-input-from-string reaction read-all)))
	(cond ((and (pair? expected)
		    (eq? (car expected) 'multiform))
	       (equal? (cdr expected) result))
	      ((and (number? expected) (inexact? expected))
	       ;; TODO I really should put this in the recursive case
	       ;; too (and get the numerics right).
	       (< (abs (- expected (car result))) 1e-10))
	      (else
	       (and (= 1 (length result))
		    (equal? expected (car result))))))))

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
  answer)

(define (%compiling-version expectation)
  (%make-expectation
   (expectation-name expectation) #t
   (expectation-forms expectation) (expectation-answer expectation)))

(define (update-expectation-name expectation new-name)
  (%make-expectation
   new-name
   (expectation-compile? expectation)
   (expectation-forms expectation)
   (expectation-answer expectation)))

(define (make-expectation test answer)
  (if (and (pair? test) (eq? (car test) 'multiform))
      (%make-expectation #f #f (cdr test) answer)
      (%make-expectation #f #f (list test) answer)))

(define (expectation->list expectation)
  (list (expectation-name expectation)
	(expectation-compile? expectation)
	(expectation-forms expectation)
	(expectation-answer expectation)))

(define (list->expectation lst)
  (%make-expectation (car lst) (cadr lst) (caddr lst) (cadddr lst)))

;;; Checking whether the interpreter behaved as expected

(define (interpretation-discrepancy expectation)
  (let* ((forms (expectation-forms expectation))
	 (expected (expectation-answer expectation))
	 (reaction (interpreter-reaction-to forms (expectation-name expectation))))
    (if (matches? expected reaction)
	#f
	`(interpreting ,forms produced ,reaction expected ,expected))))

(define (interpreter-reaction-to forms basename)
  (write-forms forms basename)
  (frobnicate
   (shell-command-output
    (string-append stalingrad-command test-directory basename ".vlad"))))

;;; Checking whether the compiler behaved as expected

(define (compilation-discrepancy expectation)
  (define (tweak-for-compilation forms)
    (append (except-last-pair forms)
	    `((write-real (real ,(car (last-pair forms)))))))
  (let* ((name (expectation-name expectation))
	 (expected (expectation-answer expectation))
	 (forms (tweak-for-compilation (expectation-forms expectation)))
	 (compiler-reaction (compilation-reaction-to forms name)))
    (if (equal? "" compiler-reaction)
	(let ((run-reaction (execution-reaction name)))
	  (if (matches? expected run-reaction)
	      #f
	      `(running ,forms produced ,run-reaction expected ,expected)))
	(if (and (pair? expected) (eq? 'error (car expected)))
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

(define (execution-reaction basename)
  (shell-command-output (string-append "./" test-directory basename)))

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

;;; The compiler has some restrictions relative the interpreter, so we
;;; can autodetect that some examples should not be tested in it.
(define (suitable-for-compilation? expectation)
  (and (every (lambda (form)
		(not (and (pair? form)
			  (eq? (car form) 'exact-string))))
	      (expectation-forms expectation))
       (let ((expect (expectation-answer expectation)))
	 (or (number? expect)
	     (and (pair? expect)
		  (or (eq? (car expect) 'error)
		      (and (eq? (car expect) 'multiform)
			   (every number? (cdr expect)))))))))

(define (compiling-version expectation)
  (if (suitable-for-compilation? expectation)
      (%compiling-version expectation)
      #f))

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

(define (file->independent-expectations filename)
  (expectations-named
   (file-basename filename)
   (independent-expectations (read-forms filename))))

(define (file->independent-compiling-expectations filename)
  (expectations-named
   (string-append "compile-" (file-basename filename))
   (filter-map compiling-version
	       (independent-expectations (read-forms filename)))))

(define (file->independent-interpreter-compiler-expectations filename)
  (let ((expectations (independent-expectations (read-forms filename))))
    (append
     (expectations-named
      (file-basename filename)
      expectations)
     (expectations-named
      (string-append "compile-" (file-basename filename))
      (filter-map compiling-version expectations)))))

(define (file->definition-sharing-expectations filename)
  (expectations-named
   (file-basename filename)
   (shared-definitions-expectations (read-forms filename))))

(define (file->compiling-expectations filename)
  (expectations-named
   (string-append "compile-" (file-basename filename))
   (filter-map compiling-version
	       (file->definition-sharing-expectations filename))))

(define (file->interpreter-compiler-expectations filename)
  (let ((expectations (shared-definitions-expectations (read-forms filename))))
    (append
     (expectations-named
      (file-basename filename)
      expectations)
     (expectations-named
      (string-append "compile-" (file-basename filename))
      (filter-map compiling-version expectations)))))

(define (fast-expectations)
  (with-working-directory-pathname my-pathname
   (lambda ()
     (append
      (with-working-directory-pathname
       "../vlad"
       (lambda ()
	 (file->independent-interpreter-compiler-expectations "scratch.scm")))
      (with-working-directory-pathname
       "../examples/"
       (lambda ()
	 (append-map
	  file->interpreter-compiler-expectations
	  '("even-odd.vlad"
	    "example-forward.vlad"
	    "factorial.vlad"
	    "bug-a.vlad"
	    "bug-b.vlad"
	    "bug-c.vlad"
	    "bug0.vlad"
	    "bug1.vlad"
	    "bug2.vlad"
	    "marble.vlad"
	    "prefix.vlad"
	    "secant.vlad"
	    "sqrt.vlad"
	    ;;"bug3.vlad" ; I don't have patterns for anf s-exps :(
	    ;;"bug4.vlad"
	    ))))))))

(define (slow-expectations)
  (with-working-directory-pathname
   my-pathname
   (lambda ()
     (with-working-directory-pathname
      "../examples/"
      (lambda ()
	(append-map
	 file->interpreter-compiler-expectations
	 '("example.vlad"
	   "double-agent.vlad"
	   "hessian.vlad"
	   "saddle.vlad"
	   "triple.vlad"
	   "dn.vlad"
	   ;;"factor16.vlad" ; I don't have patterns for anf s-exps :(
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
  (ensure-directory test-directory)
  (write-makefile test-directory)
  (for-each save-expectation expectations)
  (flush-output)
  (%exit 0))

;;; Running an expectation loaded from standard input

(define (read-and-try-expectation!)
  (set! test-directory "./") ;; This entry point is called from the test-runs/ directory
  (report-if-discrepancy (list->expectation (read)))
  (flush-output)
  (%exit 0))
