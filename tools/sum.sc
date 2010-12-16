;;; LaHaShem HaAretz U'Mloah

(module sum (main main))

(define (read-line . port)
 (if (null? port) (set! port (current-input-port)) (set! port (car port)))
 (let loop ((chars '()))
  (let ((char (read-char port)))
   (if (eof-object? char)
       (if (null? chars) char (list->string (reverse chars)))
       (if (char=? char #\newline)
	   (list->string (reverse chars))
	   (loop (cons char chars)))))))

(define (field-ref string n)
 (let loop ((n n) (chars (string->list string)))
  (if (char-whitespace? (car chars))
      (loop n (cdr chars))
      (if (zero? n)
	  (let loop ((chars chars) (field '()))
	   (if (or (null? chars) (char-whitespace? (car chars)))
	       (list->string (reverse field))
	       (loop (cdr chars) (cons (car chars) field))))
	  (loop (- n 1)
		(let loop ((chars chars))
		 (if (char-whitespace? (car chars))
		     chars
		     (loop (cdr chars)))))))))

(define (number->string-of-length-and-precision number length precision)
 (let* ((negative? (negative? number))
	(integer-part (inexact->exact (floor (abs number))))
	(fraction-part
	 (inexact->exact
	  (floor (* (expt 10 precision) (- (abs number) integer-part)))))
	(integer-part-string (number->string integer-part))
	(fraction-part-string (number->string fraction-part)))
  (if negative?
      (string-append
       (make-string
	(- length (string-length integer-part-string) 2 precision) #\space)
       "-"
       integer-part-string
       "."
       (make-string (- precision (string-length fraction-part-string)) #\0)
       fraction-part-string)
      (string-append
       (make-string
	(- length (string-length integer-part-string) 1 precision) #\space)
       integer-part-string
       "."
       (make-string (- precision (string-length fraction-part-string)) #\0)
       fraction-part-string))))

(define (main)
 (let loop ((line (read-line)) (sum 0))
  (cond
   ((eof-object? line)
    (display (number->string-of-length-and-precision sum 7 2))
    (newline))
   (else (loop (read-line) (+ sum (string->number (field-ref line 0))))))))

;;; Tam V'Nishlam Shevah L'El Borei Olam
