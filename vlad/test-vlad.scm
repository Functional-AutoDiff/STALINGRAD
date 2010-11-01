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
   (print-procedure
    (simple-unparser-method 'expected
     (lambda (expectation)
       (list (expectation-form expectation)
	     (expectation-answer expectation))))))
  form
  answer)

(define (make-expectations forms default)
  (let loop ((answers '())
	     (forms forms))
    (cond ((null? forms)
	   (reverse answers))#;
	  ((multiform? (car forms))
	   (loop (cons (assemble-multiform (car forms)) answers)
		 (cdr forms)))
	  ((null? (cdr forms))
	   (reverse (cons (make-expectation (car forms) default) answers)))
	  ((eq? '===> (cadr forms))
	   (loop (cons (make-expectation (car forms) (caddr forms)) answers)
		 (cdddr forms)))
	  (else
	   (loop (cons (make-expectation (car forms) default) answers)
		 (cdr forms))))))

(define (discrepancy expectation)
  (let* ((form (expectation-form expectation))
	 (expected (expectation-answer expectation))
	 (reaction (vlad-reaction-to form))
	 (answers (with-input-from-string reaction read-all)))
    (if (matches? expected answers)
	#f
	`(,form produced ,answers via ,reaction expected ,expected))))

(define (matches? expected result)
  ;; TODO Augment to understand "error", "non-error", etc.
  (cond ((and (pair? expected)
	      (eq? (car expected) 'multiform))
	 (equal? (cdr expected) result))
	(else
	 (and (= 1 (length result))
	      (equal? expected (car result))))))

(define (shell-command-output command)
  (with-output-to-string
    (lambda ()
      (run-shell-command command))))

(define (vlad-reaction-to form)
  (with-output-to-file "input.vlad"
    (lambda ()
      (write form)))
  (shell-command-output "../../stalingrad-amd64 input.vlad"))

(define (eval-through-vlad form)
  (with-input-from-string (vlad-reaction-to form) read))

(in-test-group
 vlad

 (for-each (lambda (expectation)
	     (define-test
	       (check (not (discrepancy expectation)))))
	   (make-expectations (read-forms "scratch.scm") #t)))
