(set! *pp?* #t)
(set! *warn?* #f)
(set! *widen-first?* #f)
(set! *l1* 4)
(set! *l2* 1)
(set! *l3* 1)
(set! *l4* 1)
(set! *l5* 1)
(set! *l6* 6)
(set! *l7* 1)
(set! *l8* 2)
(set! *depth-measure* matching-nonrecursive-closure-depth)
(set! *no-apply-multiply?* #t)
(set! *new-widen?* #t)
(set! *new-l4-depth?* #t)
;(set! *new-subset?* #t)
(set! *aesthetic-reduce-depth?* #t)
(set! *expression-equality-using-structural?* #t)
(initialize-basis!)
(define path "forward-2d.vlad")
(define es (read-source path))
(define e (expand-definitions (but-last es) (last es)))
(define result (parse e))

(define tmp (read-checkpoint-from-file "checkpoint-i369"))
(define bs (first tmp))
(define bs-old (second tmp))
(define bs-368 bs)
(define bs-367 bs-old)
(define bs1 (update-abstract-analysis-ranges bs bs-old))
(define (abstract-analysis-rooted-at e vs)
 (output-procedure-name-after "abstract-analysis-rooted-at~%")
 (let ((xs (free-variables e)))
  (cond ((variable-access-expression? e)
	 (create-abstract-analysis e vs (vector-ref vs 0)))
	((lambda-expression? e)
	 (create-abstract-analysis e vs (new-nonrecursive-closure vs e)))
	((application? e)
	 (let ((e1 (application-callee e))
	       (e2 (application-argument e)))
	  (abstract-analysis-union
	   (create-abstract-analysis e vs (empty-abstract-value))
	   (abstract-analysis-union
	    (abstract-analysis-rooted-at
	     e1 (restrict-environment vs xs (free-variables e1)))
	    (abstract-analysis-rooted-at
	     e2 (restrict-environment vs xs (free-variables e2)))))))
	((letrec-expression? e)
	 (abstract-analysis-union
	  (create-abstract-analysis e vs (empty-abstract-value))
	  (let ((vs-e
		 (list->vector
		  (map
		   (lambda (x)
		    (if (memp variable=?
			      x
			      (letrec-expression-procedure-variables e))
			(new-recursive-closure
			 (letrec-expression-recursive-closure-variables e)
			 (list->vector
			  (map
			   (lambda (x) 
			    (vector-ref vs (positionp variable=? x xs)))
			   (letrec-expression-recursive-closure-variables e)))
			 (list->vector
			  (letrec-expression-procedure-variables e))
			 (list->vector
			  (letrec-expression-argument-variables e))
			 (list->vector (letrec-expression-bodies e))
			 (positionp
			  variable=?
			  x
			  (letrec-expression-procedure-variables e)))
			(vector-ref vs (positionp variable=? x xs))))
		   (free-variables (letrec-expression-body e))))))
	   (abstract-analysis-rooted-at (letrec-expression-body e) vs-e))))
	((cons-expression? e)
	 (let ((e1 (cons-expression-car e))
	       (e2 (cons-expression-cdr e)))
	  (abstract-analysis-union
	   (create-abstract-analysis e vs (empty-abstract-value))
	   (abstract-analysis-union
	    (abstract-analysis-rooted-at
	     e1 (restrict-environment vs xs (free-variables e1)))
	    (abstract-analysis-rooted-at
	     e2 (restrict-environment vs xs (free-variables e2)))))))
	(else (panic "Not a valid expression")))))
(define bs2 (update-abstract-analysis-domains bs bs-old))
(length *expression-list*)
(define bs-new-e (remove-if (lambda (b)
			     (memp expression=?
				   (abstract-expression-binding-expression b)
				   *expression-list*))
			    bs2))
(define bs2 (remove-if (lambda (b) (memq b bs-new-e)) bs2))
(define es-new (map abstract-expression-binding-expression bs-new-e))
(when (not (null? es-new))
 (set! *expression-list* (append *expression-list* es-new)) '())
(define bs-new-before
 (map-n (lambda (i)
	 (let* ((b1 (list-ref bs1 i))
		(e (abstract-expression-binding-expression b1))
		(bs1 (abstract-expression-binding-abstract-flow b1))
		(b2 (lookup-expression-binding e bs2))
		(bs2 (if (eq? b2 #f)
			 '()
			 (abstract-expression-binding-abstract-flow b2)))
		(b-old (lookup-expression-binding e bs))
		(bs-old (if (eq? b-old #f)
			    '()
			    (abstract-expression-binding-abstract-flow b-old)))
		(ei (positionp expression=? e *expression-list*))
		;; abstract environments are unchanged in bs1
		;; abstract environments can only be "added" in bs2
		;;   - those "added" can be either:
		;;     1. truly distinct
		;;     2. repeated copies of an old environment
		;;   - for those fitting #2,
		;;     add-new-abstract-environments-to-abstract-flow
		(bs-new
		 (add-new-abstract-environments-to-abstract-flow ei bs1 bs2))
		(bs-new2
		 (introduce-imprecision-to-abstract-flow ei bs-new bs-old)))
	  (make-abstract-expression-binding e bs-new2)))
	412))
(define b1 (list-ref bs1 412))
(define e (abstract-expression-binding-expression b1))
(define bs-flow1 (abstract-expression-binding-abstract-flow b1))
(define b2 (lookup-expression-binding e bs2))
(eq? b2 #f)
(define bs-flow2 (abstract-expression-binding-abstract-flow b2))
(define b-old (lookup-expression-binding e bs))
(eq? b-old #f)
(define bs-flow-old (abstract-expression-binding-abstract-flow b-old))
(define ei (positionp expression=? e *expression-list*))
(define bs-new 
 (add-new-abstract-environments-to-abstract-flow ei bs-flow1 bs-flow2))
(define bs-flow-new bs-new)
(define bs-flow-new
 (introduce-imprecision-by-restricting-abstract-function-size2
  *l1* bs-new))
(define bs-flow-new (remove-redundant-abstract-mappings bs-flow-new))
(define i 0)
(memq (list-ref bs-flow-new 0) bs-flow-old)
(define b (list-ref bs-flow-new i))
(define all-vs-old
 (reduce
  append
  (map (lambda (b)
	(cons (abstract-environment-binding-abstract-value b)
	      (vector->list
	       (abstract-environment-binding-abstract-values b))))
       bs-flow-old)
  '()))
(length all-vs-old)
(define vs (abstract-environment-binding-abstract-values b))
(map-vector (lambda (v) (if (memq v all-vs-old) #t #f)) vs)
(define vs-new (map-vector identity vs))
(abstract-environment-proper-subset? vs vs-new)
(define v (abstract-environment-binding-abstract-value b))
(define (constraints-met? v)
 (list (l2-met? v)
       (l3-met? v)
       (l4-met? v)
       (l5-met? v)
       (l6-met? v)
       (l7-met? v)
       (l8-met? v)))
(constraints-met? v)
(define v1 (remove-duplicate-proto-abstract-values v))
(constraints-met? v1)
(define v2a (limit-matching-closures v1))
(constraints-met? v2a)
(define v3a (limit-matching-pairs v2a))
(constraints-met? v3a)
(define v3b (limit-matching-bundles v3a))
(constraints-met? v3b)
(define v4a (limit-l4-depth2 v3b))
(constraints-met? v4a)
(define v5a (limit-l6-depth v4a))
(constraints-met? v5a)
(define v-saved v)
(define v v5a)
(define limit (- *l6* 1))
(define v-old v)
(define v-new
 (let inner ((path (path-of-depth-greater-than-k
		    limit pair-depth v))
	     (v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge
			 limit pair-depth path))
		 (v-new (reduce-depth2
			 path (first va-vb) (second va-vb))))
	   (inner (path-of-depth-greater-than-k
		   limit pair-depth v-new)
		  v-new)))))
(abstract-value=? v-new v-old)
(eq? v-new v-old)
(define limit (- limit 1))
(define v-old v-new)
(define path (path-of-depth-greater-than-k
	      limit pair-depth v))
(eq? path #f)
(define v-new v)
(define limit (- limit 1))
(define v-old v-new)
limit
(define path (path-of-depth-greater-than-k
	      limit pair-depth v))
(eq? path #f)
(pair-depth path)
(define v-new
 (let inner ((path (path-of-depth-greater-than-k
		    limit pair-depth v))
	     (v v))
      (if (eq? path #f)
	  v
	  (let* ((va-vb (get-values-to-merge
			 limit pair-depth path))
		 (v-new (reduce-depth2
			 path (first va-vb) (second va-vb))))
	   (inner (path-of-depth-greater-than-k
		   limit pair-depth v-new)
		  v-new)))))
(eq? v-old v)
(set! *unabbreviate-transformed?* #f)
(define v1 v-new)
(define v2 v-old)
(define (all-vs-and-us v vs1)
 (if (or (up? v) (memq v vs1))
     (list '() '())
     (let inner
       ((vs-to-explore
	 (reduce
	  append
	  (map (lambda (u)
		(if (branching-value? u) (branching-value-values u) '()))
	       v)
	  '()))
	(vs (list v))
	(us v))
      (if (null? vs-to-explore)
	  (list vs us)
	  (let ((result (all-vs-and-us (first vs-to-explore) (cons v vs1))))
	   (inner (rest vs-to-explore)
		  (append vs (first result))
		  (append us (second result))))))))
(define (abstract-value-subset?-cyclic v1 v2)
 (define trace-this? #t)
 (define vs-us-v1 (all-vs-and-us v1 '()))
 (define vs-v1 (first vs-us-v1))
 (define vs-v1-alt (remove-duplicatesp set-equalq? vs-v1))
 (define us-v1 (remove-duplicatesq (second vs-us-v1)))
 (define vs-us-v2 (all-vs-and-us v2 '()))
 (define vs-v2 (first vs-us-v2))
 (define vs-v2-alt (remove-duplicatesp set-equalq? vs-v2))
 (define us-v2 (remove-duplicatesq (second vs-us-v2)))
 (define (externalize-v1 v)
  (cond ((memq v vs-v1) (format #f "v[~s]" (positionq v vs-v1)))
	((memp set-equalq? v vs-v1-alt) 
	 (format #f "v-alt[~s]" (positionp set-equalq? v vs-v1-alt)))
	(else
	 (format #f "us[~s]" (map (lambda (u) (positionq u us-v1)) v)))))
 (define (externalize-v2 v)
  (cond ((memq v vs-v2) (format #f "v[~s]" (positionq v vs-v2)))
	((memp set-equalq? v vs-v2-alt) 
	 (format #f "v-alt[~s]" (positionp set-equalq? v vs-v2-alt)))
	(else
	 (format #f "us[~s]" (map (lambda (u) (positionq u us-v2)) v)))))
 (let loop? ((v1 v1) (v2 v2) (cs '()))
  (when (and trace-this? *subset-trace?*)
   (format #t "(subset?~%v1=~s v2=~s~%"
	   (externalize-v1 v1) (externalize-v2 v2))
   (pp (map (lambda (c) (list (externalize-v1 (car c)) 
			      (externalize-v2 (cdr c))))
	    cs))
   (newline))
;   (format #t "(subset?~%v1=")
;   (pp (externalize-abstract-value (uncyclicize-abstract-value v1))) (newline)
;   (display "v2=")
;   (pp (externalize-abstract-value (uncyclicize-abstract-value v2))) (newline)
;   (display "cs=")
;   (pp (map (lambda (c) (list (externalize-abstract-value
; 			       (uncyclicize-abstract-value (car c)))
; 			      (externalize-abstract-value
; 			       (uncyclicize-abstract-value (cdr c)))))
; 	    cs))
;   (newline))
  (set! *num-calls-abstract-value-subset-loop?*
	(+ *num-calls-abstract-value-subset-loop?* 1))
  (let ((result
  (cond
   ((eq? v1 v2))
   ((null? v1) #t)
   ((null? v2) #f)
   ((some (lambda (c)
	   (and (set-equalp? eq? v1 (car c)) (set-equalp? eq? v2 (cdr c))))
	  cs)
    #t)
   (else
    (let ((cs (cons (cons v1 v2) cs))
	  ;	  (us1-atomic (remove-if-not atomic-proto-abstract-value? v1))
	  ;	  (us1-branching (remove-if atomic-proto-abstract-value? v1))
	  ;	  (us2-atomic (remove-if-not atomic-proto-abstract-value? v2)))
	  (us1-branching (remove-if atomic-proto-abstract-value? v1))
	  (us2-branching (remove-if atomic-proto-abstract-value? v2)))
     (and
      (possible-abstract-value-subset? v1 v2)
      (every
       (if
	*new-subset?*
	(lambda (u1)
	 (cond
	  ((memq u1 v2) #t)
	  ((branching-value? u1)
	   (let* ((vs1 (branching-value-values u1))
		  (k (length vs1))
		  (us2-matching (remove-if-not
				 (lambda (u2) (branching-value-match? u1 u2))
				 us2-branching))
		  (vs2s-matching (map (lambda (u2)
				       (branching-value-values-matching u1 u2))
				      us2-matching)))
	    (let outer ((vs2s vs2s-matching) (results '()))
	     (if (null? vs2s)
		 (if (= k 1)
		     #f
		     (let ((results (reverse results)))
		      (some-n
		       (lambda (i)
			(let ((vs2s-matching-all-but-i
			       (remove-if-not
				(lambda (vs2)
				 (let ((result
					(list-ref
					 results
					 (positionq vs2 vs2s-matching))))
				  (every-n
				   (lambda (j)
				    (if (= i j) #t (list-ref result j)))
				   k)))
				vs2s-matching)))
			 (if (<= (length vs2s-matching-all-but-i) 1)
			     #f
			     (loop? (list-ref vs1 i)
				    (reduce abstract-value-union-cyclic
					    (map
					     (lambda (vs2) (list-ref vs2 i))
					     vs2s-matching-all-but-i)
					    (empty-abstract-value))
				    cs))))
		       k)))
		 (let ((result (map (lambda (v1 v2) (loop? v1 v2 cs))
				    vs1
				    (first vs2s))))
		  (if (every (lambda (b) (eq? b #t)) result)
		      #t
		      (outer (rest vs2s) (cons result results))))))))
	  ((reverse-tagged-value? u1)
	   (panic (string-append "abstract-value-subset? not defined "
				 " (yet) for reverse-tagged-values!")))
	  (else #f)))
	(lambda (u1)
	 (cond
	  ((memq u1 v2) #t)
	  ((branching-value? u1)
	   (let ((vs1 (branching-value-values u1))
		 (us2-matching (remove-if-not
				(lambda (u2) (branching-value-match? u1 u2))
				us2-branching)))
	    (some-n
	     (lambda (i)
	      (let ((us-matching-all-but-u1_i
		     (remove-if-not
		      (lambda (u2)
		       (let ((vs2-matching
			      (branching-value-values-matching u1 u2)))
			(every-n
			 (lambda (j)
			  (if (= i j)
			      #t
			      (loop? (list-ref vs1 j)
				     (list-ref vs2-matching j)
				     cs)))
			 (length vs1))))
		      us2-matching)))
	       (loop? (list-ref vs1 i)
		      (reduce abstract-value-union-cyclic
			      (map (lambda (u)
				    (list-ref
				     (branching-value-values-matching u1 u)
				     i))
				   us-matching-all-but-u1_i)
			      (empty-abstract-value))
		      cs)))
	     (length vs1))))
	  ((reverse-tagged-value? u1)
	   (panic (string-append "abstract-value-subset? not defined "
				 " (yet) for reverse-tagged-values!")))
	  (else #f))))
       us1-branching)))))))
   (when (and trace-this? *subset-trace?*) (format #t "result=~s)~%" result))
   result)))
(define v1c (cyclicize-abstract-value v1))
(define v2c (cyclicize-abstract-value v2))
(define v1-saved v1)
(define v1 v1c)
(define v2-saved v2)
(define v2 v2c)
(define vs-us-v1 (all-vs-and-us v1 '()))
(define vs-us-v2 (all-vs-and-us v2 '()))
(map length vs-us-v1)
(map length vs-us-v2)
