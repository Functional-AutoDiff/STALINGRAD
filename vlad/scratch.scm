(+ 1 2) ===> 3
(- 1 2) ===> -1
; (- 1)
(* 1 2) ===> 2
(/ 1 2) ===> 0.5
(sqrt 2) ===> 1.414213562373095
(exp 1) ===> 2.718281828459045
(= 1 1)
(< 1 2)
(zero? 4) ===> #f
(zero? 0)
(positive? -1) ===> #f
(positive? 1)
(negative? 2) ===> #f
(negative? -1)
(sin 3) ===> .1411200080598672
(cos 3) ===> -.9899924966004454
(log 2) ===> .6931471805599453
(atan 2 3) ===> .5880026035475675
(real? 4)
(real? 2.073e-2)


(multiform
 (define (abs x) (if (negative? x) (- 0 x) x))
 (abs -3))
===> 3

(let ((ignore (write (* 2 (real 3)))))
  3) ===> (multiform 6 3)

(multiform
 (define (fact x)
   (if (= x 0)
       1
       (* x (fact (- x 1)))))

 (fact 5)
 (fact (real 5)))
===> (multiform 120 120)

(perturb 1) ===> (perturbation 1)
(write (perturb 1)) ===> (multiform (perturbation 1) (perturbation 1))
(perturbation? (perturb 1))
(perturbation? 1) ===> #f
(bundle 1 (perturb 1)) ===> (forward 1 (perturbation 1))
(forward? (bundle 1 (perturb 1)))
(forward? 1) ===> #f
(forward? (perturb 1)) ===> #f
(unperturb (perturb 1)) ===> 1
(primal (bundle 1 (perturb 1))) ===> 1
(tangent (bundle 1 (perturb 1))) ===> (perturbation 1)
(perturb (cons 1 2)) ===> (perturbation (1 . 2))
(perturb #t) ===> (perturbation #t)
(bundle (cons 1 2) (perturb (cons 3 4))) ===> (forward (1 . 2) (perturbation (3 . 4)))
(*j 1) ===> (reverse 1)

(multiform
 (define (car (cons x y)) x)
 (define (cdr (cons x y)) y)
 (reverse? (car ((*j sin) (*j 1))))
 (procedure? (cdr ((*j sin) (*j 1))))
 (sensitivity? ((cdr ((*j sin) (*j 1))) (sensitize 1)))
 (cdr (unsensitize ((cdr ((*j sin) (*j 1))) (sensitize 1)))))
===> (multiform #t #t #t 0.5403023058681398)

(reverse? (*j sin))
(plus (cons 1 2) (cons 2 3)) ===> (3 . 5)

;; (define (double-loop)
;;   (let* ((x (read-real))
;;          (y (write (* 3 x))))
;;     (double-loop)))

;; (double-loop)

'() ===> ()
() ===> (error "Invalid expression: ()") ;; TODO Fix testing error conditions

(multiform
 (define x 3)
 x) ===> (error "Invalid expression")

(let ((x 3)
      (x 4))
  x) ===> (error "Duplicate variables")

(let* ((x 3)
       (x 4))
  x) ===> 4

(letrec ((x 3)
	 (x 4))
  x) ===> (error "Duplicate variables")

(multiform
 (define x (lambda () 3))
 (x)) ===> 3

(letrec ((foo (cons (lambda () 2)
		    (lambda () 3))))
  foo) ===> (error "Invalid expression")

`(3) ===> (error "Unbound variable: QUASIQUOTE")

#b100 ===> 4
#o100 ===> 64
#d100 ===> 100
#x100 ===> 256

(write (cons 1 2)) ===> (multiform (1 . 2) (1 . 2))

;; TODO How do I test #; and #| |# comments? (They are not supported as of this writing)
