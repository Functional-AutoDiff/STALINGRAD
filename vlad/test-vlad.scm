(load-option 'synchronous-subprocess)
(load "../../testing/load")

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
      (re-string-match (cadr expected) reaction)
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
  (with-output-to-file "input.vlad"
    (lambda ()
      (for-each write forms)))
  (shell-command-output "../../stalingrad-amd64 input.vlad"))

(define (eval-through-vlad forms)
  (with-input-from-string (vlad-reaction-to forms) read))

(in-test-group
 vlad

 (for-each (lambda (expectation)
	     (define-test
	       (check (not (discrepancy expectation)))))
	   (make-expectations (read-forms "scratch.scm") #t)))
