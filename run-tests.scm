
(set! load/suppress-loading-message? #t)

(define (self-relatively thunk)
  (if (current-eval-unit #f)
      (with-working-directory-pathname
       (directory-namestring (current-load-pathname))
       thunk)
      (thunk)))

(define (load-relative filename)
  (self-relatively (lambda () (load filename))))

(define test-driver "../BCL-AD/vlad/test-vlad.scm")

(self-relatively
 (lambda ()
   (if (not (file-readable? test-driver))
       (begin
	 (display "Fatal: Cannot find test driver in ")
	 (display test-driver)
	 (newline)
	 (display "Fatal: Did you clone BCL-AD in a sister directory?")
	 (newline)
	 (%exit 1)))))

(load-relative test-driver)
(let ((num-failures (show-time run-registered-tests)))
  (newline)
  (flush-output)
  (%exit num-failures))
