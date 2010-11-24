(load-option 'synchronous-subprocess)
(define (self-relatively thunk)
  (if (current-eval-unit #f)
      (with-working-directory-pathname
       (directory-namestring (current-load-pathname))
       thunk)
      (thunk)))

(define (load-relative filename)
  (self-relatively (lambda () (load filename))))

(load-relative "../../testing/load")

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

(define (make-expectations forms default)
  (let loop ((answers '())
	     (forms forms))
    (cond ((null? forms)
	   (reverse answers))
	  ((null? (cdr forms))
	   (reverse (cons (make-expectation (car forms) default) answers)))
	  ((eq? '===> (cadr forms))
	   (loop (cons (make-expectation (car forms) (caddr forms)) answers)
		 (cdddr forms)))
	  (else
	   (loop (cons (make-expectation (car forms) default) answers)
		 (cdr forms))))))

(define (discrepancy expectation)
  (let* ((forms (expectation-forms expectation))
	 (expected (expectation-answer expectation))
	 (reaction (vlad-reaction-to forms)))
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

(define (vlad-reaction-to forms)
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
  (with-output-to-file "input.vlad"
    (lambda ()
      (for-each dispatched-write forms)))
  (frobnicate
   (shell-command-output
    (string-append (->namestring my-pathname) "../../../bin/stalingrad input.vlad"))))

(define (eval-through-vlad forms)
  (with-input-from-string (vlad-reaction-to forms) read))

(in-test-group
 vlad

 (for-each (lambda (expectation)
	     (define-test
	       (check (not (discrepancy expectation)))))
	   (make-expectations (self-relatively
			       (lambda ()
				 (read-forms "scratch.scm")))
			      #t)))
