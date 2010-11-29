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

(load-relative "../testing/load")

;;; File system manipulations

(define (ensure-directory filename)
  (if (file-exists? filename)
      (if (file-directory? filename)
	  'ok
	  (error "Exists and is not a directory" filename))
      (make-directory filename)))

(define my-pathname (self-relatively working-directory-pathname))
(define test-directory "test-runs/")
(ensure-directory test-directory)
(define stalingrad-command
  (string-append (->namestring my-pathname) "../../stalingrad/source/stalingrad -scmh 2000 -I "
		 (->namestring my-pathname) "../../stalingrad/examples/ "))

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

;;; Checking that answers are as expected

(define (matches? expected reaction)
  (if (and (pair? expected)
	   (eq? (car expected) 'error))
      (re-string-search-forward (cadr expected) reaction)
      (let ((result (with-input-from-string reaction read-all)))
	(cond ((and (pair? expected)
		    (eq? (car expected) 'multiform))
	       (equal? (cdr expected) result))
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
       (list (expectation-forms expectation)
	     (expectation-answer expectation))))))
  name
  compile?
  forms
  answer)

(define (compiling-version expectation)
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

;;; Checking whether the interpreter behaved as expected

(define (interpretation-discrepancy expectation)
  (let* ((forms (expectation-forms expectation))
	 (expected (expectation-answer expectation))
	 (reaction (interpreter-reaction-to forms (expectation-name expectation))))
    (if (matches? expected reaction)
	#f
	`(,forms produced ,reaction expected ,expected))))

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
	 (forms (tweak-for-compilation (expectation-forms expectation)))
	 (compiler-reaction (compilation-reaction-to forms name)))
    (if (equal? "" compiler-reaction)
	(let ((run-reaction (execution-reaction name))
	      (expected (expectation-answer expectation)))
	  (if (matches? expected run-reaction)
	      #f
	      `(running ,forms produced ,run-reaction expected ,expected)))
	`(compiling ,forms produced ,compiler-reaction))))

(define (compilation-reaction-to forms basename)
  (write-forms forms basename)
  (frobnicate
   (shell-command-output
    (string-append stalingrad-command "-compile -k " test-directory basename ".vlad"))))

(define (execution-reaction basename)
  (shell-command-output (string-append "./" test-directory basename)))

(define (discrepancy expectation)
  (if (expectation-compile? expectation)
      (compilation-discrepancy expectation)
      (interpretation-discrepancy expectation)))

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
  (map (lambda (expectation index)
	 (update-expectation-name
	  expectation
	  (string-append basename "-" (number->string index))))
       expectations
       (iota (length expectations) 1)))

(define (file->independent-expectations filename)
  (expectations-named
   (file-basename filename)
   (independent-expectations (read-forms filename))))

(define (file->definition-sharing-expectations filename)
  (expectations-named
   (file-basename filename)
   (shared-definitions-expectations (read-forms filename))))

(define (file->compiling-expectations filename)
  (expectations-named
   (string-append "compile-" (file-basename filename))
   (map compiling-version
	(file->definition-sharing-expectations filename))))

(define (file->interpreter-compiler-expectations filename)
  (let ((expectations (shared-definitions-expectations (read-forms filename))))
    (append
     (expectations-named
      (file-basename filename)
      expectations)
     (expectations-named
      (string-append "compile-" (file-basename filename))
      (map compiling-version expectations)))))

(define (all-expectations)
  (self-relatively
   (lambda ()
     (append
      (file->independent-expectations "scratch.scm")
      (with-working-directory-pathname
       "../../stalingrad/examples/"
       (lambda ()
	 (append
	  (append-map
	   file->interpreter-compiler-expectations
	   '("factorial.vlad"
	     "bug-a.vlad"
	     "bug-b.vlad"
	     "bug-c.vlad"
	     "bug0.vlad"
	     "bug1.vlad"
	     "bug2.vlad"
	     "double-agent.vlad"
	     "marble.vlad"
	     "secant.vlad"
	     "sqrt.vlad"
	     ;;"bug3.vlad" ; I don't have patterns for anf s-exps :(
	     ;;"bug4.vlad"
	     ))
	  ;; The compiler doesn't support structured write :(
	  (append-map
	   file->definition-sharing-expectations
	   '("even-odd.vlad"
	     "example.vlad"
	     "example-forward.vlad"
	     "prefix.vlad"
	     )))))))))

;;;; Converting expectations to test-manager tests

(define (register-expectation-test expectation)
  (register-test
   (make-single-test
    (expectation-name expectation)
    (lambda ()
      (check (not (discrepancy expectation))))
    #f))
  ;; The above instead of the below because I want to construct the
  ;; name of the test from the name of the expectation.
  #;
  (define-test
    (check (not (discrepancy expectation)))))

(define (parse-and-register-tests)
  (in-test-group
   vlad
   (for-each register-expectation-test (all-expectations))))
