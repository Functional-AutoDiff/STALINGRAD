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

(define (read-all)
  (let loop ((results '())
	     (form (read)))
    (if (eof-object? form)
	(reverse results)
	(loop (cons form results) (read)))))

(define (read-forms filename)
  (with-input-from-file filename read-all))

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

(define (interpreter-reaction-to forms)
  (define (dispatched-write form)
    (if (and (pair? form) (eq? (car form) 'exact-string))
	(write-string (cadr form))
	(write form)))
  (define (frobnicate string)
    ;; It appears that the latest binary of Stalingrad I have access
    ;; to emits an interesting message on startup.
    (string-tail
     string
     (string-length "***** INITIALIZEVAR Duplicately defined symbol MAP-REDUCE
***** INITIALIZEVAR Duplicately defined symbol GENSYM
")))
  (with-output-to-file "test-input.vlad"
    (lambda ()
      (for-each dispatched-write forms)))
  (frobnicate
   (shell-command-output
    (string-append (->namestring my-pathname) "../../stalingrad/source/stalingrad test-input.vlad"))))

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
    (cond ((null? forms)
	   (reverse answers))
	  ((definition? (car forms))
	   (loop answers (cdr forms) (cons (car forms) definitions)))
	  ((null? (cdr forms))
	   (reverse (cons (make-expectation `(multiform ,@definitions ,(car forms)) #t) answers)))
	  ((eq? '===> (cadr forms))
	   (loop (cons (make-expectation `(multiform ,@definitions ,(car forms)) (caddr forms)) answers)
		 (cdddr forms)
		 definitions))
	  (else
	   (loop (cons (make-expectation `(multiform ,@definitions ,(car forms)) #t) answers)
		 (cdr forms)
		 definitions)))))

(define (expectation->test expectation)
  (define-test
    (check (not (interpretation-discrepancy expectation)))))

(define (file->independent-tests filename)
  (for-each expectation->test (independent-expectations (read-forms filename))))

(define (file->definition-sharing-tests filename)
  (for-each expectation->test (shared-definitions-expectations (read-forms filename))))

(in-test-group
 vlad

 (self-relatively
  (lambda ()
    (file->independent-tests "scratch.scm")
    (with-working-directory-pathname
     "../../stalingrad/examples/"
     (lambda ()
       (file->definition-sharing-tests "bug0.vlad")
       (file->definition-sharing-tests "bug-a.vlad"))))))
