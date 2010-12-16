(define (primal* p)
 (if (and (pair? p) (eq? (car p) '*diff*)) (cadr (assq '() (cdr p))) p))

(define (lift-real^n->boolean f) (lambda ps (apply f (map primal* ps))))

(define d= (lift-real^n->boolean =))

(define d< (lift-real^n->boolean <))

(define d> (lift-real^n->boolean >))

(define d<= (lift-real^n->boolean <=))

(define d>= (lift-real^n->boolean >=))

(define dzero? (let ((= =)) (lift-real^n->boolean (lambda (x) (= x 0)))))

(define dpositive? (lift-real^n->boolean positive?))

(define dnegative? (lift-real^n->boolean negative?))

(define dreal? (lift-real^n->boolean real?))

(define (derivative-F f) (D f))

(define (replace-ith x i xi)
 (if (dzero? i)
     (cons xi (cdr x))
     (cons (car x) (replace-ith (cdr x) (- i 1) xi))))

(define (gradient-F f)
 (lambda (x)
  ((map-n
    (lambda (i)
     ((derivative-F (lambda (xi) (f (replace-ith x i xi)))) (list-ref x i))))
   (length x))))

(define (write-real x) (write x) (newline) x)

(define (first x) (car x))

(define (second x) (car (cdr x)))

(define (third x) (car (cdr (cdr x))))

(define (fourth x) (car (cdr (cdr (cdr x)))))

(define (rest x) (cdr x))

(define (sqr x) (* x x))

(define (map-n f)
 (lambda (n)
  (letrec ((loop (lambda (i) (if (d= i n) '() (cons (f i) (loop (+ i 1)))))))
   (loop 0))))

(define (reduce f i)
 (lambda (l) (if (null? l) i (f (car l) ((reduce f i) (cdr l))))))

(define (map-reduce g i f l)
 (if (null? l) i (g (f (first l)) (map-reduce g i f (rest l)))))

(define (remove-if p l)
 (cond ((null? l) '())
       ((p (first l)) (remove-if p (rest l)))
       (else (cons (first l) (remove-if p (rest l))))))

(define (v+ u v) (map + u v))

(define (v- u v) (map - u v))

(define (k*v k v) (map (lambda (x) (* k x)) v))

(define (magnitude-squared x) ((reduce + 0.0) (map sqr x)))

(define (magnitude x) (sqrt (magnitude-squared x)))

(define (distance-squared u v) (magnitude-squared (v- v u)))

(define (distance u v) (sqrt (distance-squared u v)))

(define (gradient-ascent-F f x0 n eta)
 (if (dzero? n)
     (list x0 (f x0) ((gradient-F f) x0))
     (gradient-ascent-F
      f
      (map (lambda (xi gi) (+ xi (* eta gi))) x0 ((gradient-F f) x0))
      (- n 1)
      eta)))

(define (multivariate-argmin-F f x)
 (let ((g (gradient-F f)))
  (letrec ((loop
	    (lambda (x fx gx eta i)
	     (cond ((d<= (magnitude gx) 1e-5) x)
		   ((d= i 10) (loop x fx gx (* 2.0 eta) 0))
		   (else
		    (let ((x-prime (v- x (k*v eta gx))))
		     (if (d<= (distance x x-prime) 1e-5)
			 x
			 (let ((fx-prime (f x-prime)))
			  (if (d< fx-prime fx)
			      (loop x-prime fx-prime (g x-prime) eta (+ i 1))
			      (loop x fx gx (/ eta 2.0) 0))))))))))
   (loop x (f x) (g x) 1e-5 0))))

(define (multivariate-argmax-F f x)
 (multivariate-argmin-F (lambda (x) (- 0.0 (f x))) x))

(define (multivariate-max-F f x) (f (multivariate-argmax-F f x)))
