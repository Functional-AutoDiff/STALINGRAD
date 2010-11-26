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

(define my-pathname (self-relatively working-directory-pathname))
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

(define (shell-command-output command)
  (with-output-to-string
    (lambda ()
      (run-shell-command command))))

(define (write-forms forms)
  (define (dispatched-write form)
    (if (and (pair? form) (eq? (car form) 'exact-string))
	(write-string (cadr form))
	(begin (pp form)
	       (newline))))
  (with-output-to-file "test-input.vlad"
    (lambda ()
      (for-each dispatched-write forms))))

(define (frobnicate string)
  ;; It appears that the latest binary of Stalingrad I have access
  ;; to emits an interesting message on startup.
  (string-tail
   string
   (string-length "***** INITIALIZEVAR Duplicately defined symbol MAP-REDUCE
***** INITIALIZEVAR Duplicately defined symbol GENSYM
")))

(define-structure
  (expectation
   (safe-accessors #t)
   (constructor %make-expectation)
   (print-procedure
    (simple-unparser-method 'expected
     (lambda (expectation)
       (list (expectation-forms expectation)
	     (expectation-answer expectation))))))
  forms
  answer)

(define (make-expectation test answer)
  (if (and (pair? test) (eq? (car test) 'multiform))
      (%make-expectation (cdr test) answer)
      (%make-expectation (list test) answer)))

(define (interpretation-discrepancy expectation)
  (let* ((forms (expectation-forms expectation))
	 (expected (expectation-answer expectation))
	 (reaction (interpreter-reaction-to forms)))
    (if (matches? expected reaction)
	#f
	`(,forms produced ,reaction expected ,expected))))

(define (interpreter-reaction-to forms)
  (write-forms forms)
  (frobnicate
   (shell-command-output
    (string-append stalingrad-command "test-input.vlad"))))

(define (compilation-discrepancy expectation)
  (define (tweak-for-compilation forms)
    (append (except-last-pair forms)
	    `((write-real (real ,(car (last-pair forms)))))))
  (let* ((forms (tweak-for-compilation (expectation-forms expectation)))
	 (compiler-reaction (compilation-reaction-to forms)))
    (if (equal? "" compiler-reaction)
	(let ((run-reaction (execution-reaction))
	      (expected (expectation-answer expectation)))
	  (if (matches? expected run-reaction)
	      #f
	      `(running ,forms produced ,run-reaction expected ,expected)))
	`(compiling ,forms produced ,compiler-reaction))))

(define (compilation-reaction-to forms)
  (write-forms forms)
  (frobnicate
   (shell-command-output
    (string-append stalingrad-command "-compile -k test-input.vlad"))))

(define (execution-reaction)
  (shell-command-output "./test-input"))

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

(define (expectation->test expectation)
  (define-test
    (check (not (interpretation-discrepancy expectation)))))

(define (expectation->interpreter-compiler-test expectation)
  (expectation->test expectation)
  (define-test
    (check (not (compilation-discrepancy expectation)))))

(define (file->independent-tests filename)
  (for-each expectation->test (independent-expectations (read-forms filename))))

(define (file->definition-sharing-tests filename)
  (for-each expectation->test (shared-definitions-expectations (read-forms filename))))

(define (file->interpreter-compiler-tests filename)
  (for-each expectation->interpreter-compiler-test
	    (shared-definitions-expectations (read-forms filename))))

(in-test-group
 vlad

 (self-relatively
  (lambda ()
    (file->independent-tests "scratch.scm")
    (with-working-directory-pathname
     "../../stalingrad/examples/"
     (lambda ()
       (for-each
	file->interpreter-compiler-tests
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
	  ;"bug3.vlad" ; I don't have patterns for anf s-exps :(
	  ;"bug4.vlad"
	  ))
       ;; The compiler doesn't support structured write :(
       (for-each
	file->definition-sharing-tests
	'("even-odd.vlad"
	  "example.vlad"
	  "example-forward.vlad"
	  "prefix.vlad"
	  )))))))
