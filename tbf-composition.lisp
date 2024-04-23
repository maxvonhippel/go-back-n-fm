(in-package "ACL2S")

;; Import theory of tbf
(include-book "tbf")

;; Next up, I claim that the serial composition of two TBFs _is_
;; (in some sense) just another TBF.  Let's formalize that claim,
;; via simulation.  First we need to define the composition.
;;
;;         sender ---> tbfA ---> tbfB ---> receiver
;;
(defdata two-tbf (list tbf tbf))

(check= (o-finp 4) t)
(check= (o-finp (make-ord 1 1 0)) nil)

(definecd ord+ (o0 o1 :nat-ord) :nat-ord
  (cond
   ((natp o0) (if (natp o1) (+ o0 o1) o1))
   ((natp o1) o0)
   (t o0))) ;; different levels of infinity DO NOT MATTER for our proof.

(definecd incr-ttl (dgs :dgs del :nat-ord) :dgs
  (match dgs
    (() ())
    ((dg . rst) (cons (mset :ttl (ord+ (dg-ttl dg) del) dg) (incr-ttl rst del)))))

(property incr-ttl-len (dgs :dgs del :nat-ord)
  (= (len (incr-ttl dgs del)) (len dgs))
  :hints (("Goal" :in-theory (enable incr-ttl-definition-rule))))

;; Given a pair of tbfs, we can come up with a new (third) tbf which in
;; some sense is equivalent to the serial composition of the prior two.
(definecd [+] (ttbf :two-tbf) :tbf
  (tbf
   ;; bucket capacity (b-cap)
   (tbf-b-cap (cadr ttbf))
   ;; link capacity (l-cap)
   (+ (tbf-l-cap (car ttbf)) (tbf-l-cap (cadr ttbf)))
   ;; bucket (b)
   (tbf-b (cadr ttbf))
   ;; rate (r)
   (tbf-r (cadr ttbf))
   ;; time-to-live (ttl)
   (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf)))
   ;; queue of data (D) -- timed 
   (append (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf)))
	   (tbf-D (cadr ttbf)))))

;; We say two TBFs are equivalent if they match everywhere except their
;; buckets and expiries.

(definecd ~= (t1 t2 :tbf) :bool
  (^ (== (tbf-b-cap t1) (tbf-b-cap t2))
     (== (tbf-l-cap t1) (tbf-l-cap t2))
     (== (tbf-r t1) (tbf-r t2))
     (== (tbf-ttl t1) (tbf-ttl t2))
     (== (dgs->poss (tbf-D t1))
	 (dgs->poss (tbf-D t2)))))

(property dgs->poss-ignore-incr (dgs :dgs del :nat-ord)
  (equal (dgs->poss (incr-ttl dgs del))
	 (dgs->poss dgs))
  :hints (("Goal" :in-theory (enable dgs->poss-definition-rule
				     incr-ttl-definition-rule))))

(property dgs->poss-app (dgs0 dgs1 :dgs)
  (equal (dgs->poss (append dgs0 dgs1))
	 (append (dgs->poss dgs0) (dgs->poss dgs1)))
  :hints (("Goal" :in-theory (enable dgs->poss-definition-rule))))

(property tricky-dgs-append-step (ttbf :two-tbf p :pos drop :bool)
  (equal (dgs->poss (append (cons (dg p (tbf-ttl (car ttbf))) (tbf-D (car ttbf))) 
			    (tbf-D (cadr ttbf))))
	 (dgs->poss (append (cons (dg p (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf))))
				  (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))))
			    (tbf-D (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable dgs->poss-definition-rule))))

(property tricky-dgs-re-arrange-step (ttbf :two-tbf p :pos drop :bool)
  (equal (dgs->poss (append (cons (dg p (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf))))
                         (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))))
			    (tbf-D (cadr ttbf))))
	 (dgs->poss (cons (dg p (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf))))
			  (append (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))) (tbf-D (cadr ttbf))))))
  :hints (("Goal" :in-theory (enable dgs->poss-definition-rule))))

(property len-[+]-D=len-+-Ds (ttbf :two-tbf)
  (equal (len (tbf-D ([+] ttbf))) (+ (len (tbf-D (car ttbf))) (len (tbf-D (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule))))

(property if-car-tbf-not-full-then-ttbf-not-full (ttbf :two-tbf)
  :h (^ (< (len (tbf-D (car ttbf))) (tbf-l-cap (car ttbf)))
	(<= (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf))))
  (< (len (tbf-D ([+] ttbf))) (tbf-l-cap ([+] ttbf)))
  :hints (("Goal" :in-theory (enable [+]-definition-rule))))

#|
PROOF SKETCH:

Assume that (len (tbf-D (car ttbf))) < (tbf-l-cap (car ttbf)), and
            (len (tbf-D (cadr ttbf))) <= (tbf-l-cap (cadr ttbf)).  Then ...

(dgs->poss (tbf-D ([+] (list (tbf-trn (car ttbf) p drop) (cadr ttbf)))))

= { by [+]-definition-rule }

(dgs->poss (append (incr-ttl (tbf-D (tbf-trn (car ttbf) p drop)) (tbf-ttl (cadr ttbf)))
                   (tbf-D (cadr ttbf))))

= { by dgs->poss-app }

(append (dgs->poss (incr-ttl (tbf-D (tbf-trn (car ttbf) p drop)) (tbf-ttl (cadr ttbf))))
        (dgs->poss (tbf-D (cadr ttbf))))

= { by dgs->poss-ignore-incr }

(append (dgs->poss (tbf-D (tbf-trn (car ttbf) p drop)))
        (dgs->poss (tbf-D (cadr ttbf))))

= { by dgs->poss-app }

(dgs->poss (append (tbf-D (tbf-trn (car ttbf) p drop)) (tbf-D (cadr ttbf))))

= { tbf-trn-definition-rule}

(dgs->poss (append (cons (dg p (tbf-ttl (car ttbf))) (tbf-D (car ttbf))) 
                   (tbf-D (cadr ttbf))))

= { tricky-dgs-append-step }

(dgs->poss (append (cons (dg p (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf))))
                         (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))))
	           (tbf-D (cadr ttbf))))

= { tricky-dgs-re-arrange-step }

(dgs->poss (cons (dg p (ord+ (tbf-ttl (car ttbf)) (tbf-ttl (cadr ttbf))))
                 (append (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))) (tbf-D (cadr ttbf)))))

= { tbf-trn-definition-rule }

(dgs->poss (tbf-D (tbf-trn ([+] ttbf) p drop)))
|#
(property ~=-D[+]-trn (ttbf :two-tbf p :pos drop :bool)
  :proof-timeout 18000
  :h (^ (< (len (tbf-D (car ttbf))) (tbf-l-cap (car ttbf)))
	(<= (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf))))
  (== (dgs->poss (tbf-D ([+] (list (tbf-trn (car ttbf) p drop) (cadr ttbf)))))
      (dgs->poss (tbf-D (tbf-trn ([+] ttbf) p drop))))
  :hints (("Goal" :use ((:instance [+]-definition-rule
				   (ttbf (list (tbf-trn (car ttbf) p drop) (cadr ttbf))))
			(:instance dgs->poss-app
				   (dgs0 (incr-ttl (tbf-D (tbf-trn (car ttbf) p drop)) (tbf-ttl (cadr ttbf))))
				   (dgs1 (tbf-D (cadr ttbf))))
			(:instance dgs->poss-ignore-incr
				   (dgs (tbf-D (tbf-trn (car ttbf) p drop)))
				   (del (tbf-ttl (cadr ttbf))))
			(:instance dgs->poss-app
				   (dgs0 (tbf-D (tbf-trn (car ttbf) p drop)))
				   (dgs1 (tbf-D (cadr ttbf))))
			(:instance tbf-trn-definition-rule
				   (tbf (car ttbf))
				   (x p))
			(:instance tricky-dgs-append-step)
			(:instance tricky-dgs-re-arrange-step)
			(:instance tbf-trn-definition-rule
				   (tbf ([+] ttbf))
				   (x p))
			(:instance [+]-definition-rule)))))

;; If (T1 |> T2) does a transmit, this is equivalent to (T1 [+] T2) doing
;; a transmit.
(property (ttbf :two-tbf p :pos drop :bool)
  :proof-timeout 9000
  :h (^ (< (len (tbf-D (car ttbf))) (tbf-l-cap (car ttbf)))
	(<= (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf))))
  (~= ([+] (list (tbf-trn (car ttbf) p drop) (cadr ttbf)))
      (tbf-trn ([+] ttbf) p drop))
  :hints (("Goal" :in-theory (enable tbf-trn-definition-rule
				     ~=-definition-rule
				     [+]-definition-rule
				     incr-ttl-definition-rule)
	   :use (:instance ~=-D[+]-trn))))

(property [+]-dlv-contracts (ttbf :two-tbf i :nat)
  :proof-timeout 8000
  :h (^ (< i (len (tbf-D (car ttbf))))
	(posp (tbf-b (car ttbf)))
	(posp (tbf-b (cadr ttbf))))
  (^ (== (len (tbf-D ([+] ttbf)))
	 (+ (len (tbf-D (car ttbf)))
	    (len (tbf-D (cadr ttbf)))))
     (< i (len (tbf-D ([+] ttbf))))
     (two-tbfp (list (tbf-dlv (car ttbf) i)
		     (cadr ttbf)))
     (posp (tbf-b ([+] ttbf)))
     (recordp (cadr ttbf)))
  :instructions (:pro :s
                      (:use (:instance [+]-definition-rule))
                      :pro
                      (:use (:instance incr-ttl-len (dgs (tbf-d (car ttbf)))
                                       (del (tbf-ttl (cadr ttbf)))))
                      :pro
                      (:claim (equal (len (mget :d ([+] ttbf)))
                                     (+ (len (mget :d (car ttbf)))
                                        (len (mget :d (cadr ttbf))))))
                      :prove))

(definecd t1-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-D (car ttbf))))
	 (posp (tbf-b (car ttbf)))
	 (posp (tbf-b (cadr ttbf))))
  (~= ([+] (list (tbf-dlv (car ttbf) i) (cadr ttbf)))
      (tbf-dlv ([+] ttbf) i))
  :body-contracts-hints (("Goal" :use (:instance [+]-dlv-contracts))))

(property remove-ith-incr-ttl-commute (dgs :dgs i :nat del :nat-ord)
  :proof-timeout 9000
  :h (< i (len dgs))
  (== (remove-ith (incr-ttl dgs del) i)
      (incr-ttl (remove-ith dgs i) del))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule
				     incr-ttl-definition-rule))))

(defthm T1>T2-dlv
  (=> (^ (two-tbfp ttbf)
         (natp i)
         (< i (len (tbf-d (car ttbf))))
         (posp (tbf-b (car ttbf)))
         (posp (tbf-b (cadr ttbf))))
      (t1-dlv-witness ttbf i))
  :instructions
  ((:use (:instance remove-ith-incr-ttl-commute
                    (dgs (tbf-d (car ttbf)))
                    (del (tbf-ttl (cadr ttbf)))))
   (:use (:instance incr-ttl-definition-rule
                    (dgs (tbf-d (car ttbf)))
                    (del (tbf-ttl (cadr ttbf)))))
   (:use (:instance ~=-definition-rule
                    (t1 ([+] (list (tbf-dlv (car ttbf) i)
                                   (cadr ttbf))))
                    (t2 (tbf-dlv ([+] ttbf) i))))
   (:use (:instance [+]-definition-rule
                    (ttbf (list (tbf-dlv (car ttbf) i)
                                (cadr ttbf)))))
   (:use (:instance [+]-definition-rule))
   (:use (:instance t1-dlv-witness-definition-rule))
   (:use (:instance tbf-dlv-definition-rule
                    (tbf (car ttbf))))
   (:use (:instance remove-prefix
                    (ps0 (incr-ttl (tbf-d (car ttbf))
                                   (tbf-ttl (cadr ttbf))))
                    (ps1 (tbf-d (cadr ttbf)))))
   :pro
   (:in-theory (enable dgs->poss-definition-rule))
   (:claim (equal (dgs->poss (tbf-d ([+] (list (tbf-dlv (car ttbf) i)
                                               (cadr ttbf)))))
                  (dgs->poss (tbf-d (tbf-dlv ([+] ttbf) i)))))
   :prove))

;; If (T1 |> T2) does a delivery in T1, but nothing in T2, this is
;; equivalent to (T1 [+] T2) doing a delivery (to loss).
(property (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-D (car ttbf))))
	(posp (tbf-b (car ttbf)))
	(posp (tbf-b (cadr ttbf))))
  (t1-dlv-witness ttbf i)
  :hints (("Goal" :use (:instance T1>T2-dlv))))

(property [+]-dlv-2-body-contracts (ttbf :two-tbf i :nat)
  :proof-timeout 9000
  :h (^ (< i (len (tbf-D (cadr ttbf))))
	(posp (tbf-b (cadr ttbf))))
  (^ (< (+ (len (tbf-D (car ttbf))) i)
	(len (tbf-D ([+] ttbf))))
     (tbfp (cadr ttbf))
     (posp (tbf-b ([+] ttbf)))
     (two-tbfp (list (car ttbf)
		     (tbf-dlv (cadr ttbf) i)))
     (recordp (cadr ttbf)))
  :hints (("Goal" :in-theory (enable ~=-definition-rule
				     [+]-definition-rule))))

(definecd t2-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-D (cadr ttbf))))
	 (posp (tbf-b (cadr ttbf))))
  (~= ([+] (list (car ttbf) (tbf-dlv (cadr ttbf) i)))
      (tbf-dlv ([+] ttbf) (+ (len (tbf-D (car ttbf))) i)))
  :body-contracts-hints (("Goal" :use (:instance [+]-dlv-2-body-contracts))))

;; If (T1 |> T2) does a delivery in T2, but nothing in T1, this is
;; equivalent to (T1 [+] T2) doing a delivery (which might or might not
;; be a loss depending on whether or not any endpoint synchronizes with
;; the delivery event).
(property (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-D (cadr ttbf))))
	(posp (tbf-b (cadr ttbf))))
  :proof-timeout 15000
  (t2-dlv-witness ttbf i)
  :hints (("Goal"
	   :use
	   ((:instance t2-dlv-witness-definition-rule)
	    (:instance [+]-definition-rule)
	    (:instance [+]-definition-rule
		       (ttbf (list (car ttbf)
				   (tbf-dlv (cadr ttbf) i))))
	    (:instance ~=-definition-rule
		       (t1 ([+] (list (car ttbf)
				      (tbf-dlv (cadr ttbf) i))))
		       (t2 (tbf-dlv ([+] ttbf)
				    (+ (len (tbf-D (car ttbf))) i))))
	    (:instance tbf-dlv-definition-rule
		       (tbf (cadr ttbf)))
	    (:instance tbf-dlv-definition-rule (tbf ([+] ttbf))
		       (i (+ (len (tbf-D (car ttbf))) i)))
	    (:instance remove-postfix
		       (ps0 (incr-ttl (tbf-D (car ttbf)) (tbf-ttl (cadr ttbf))))
		       (ps1 (tbf-D (cadr ttbf))))))))


;; If (T1 |> T2) does a delivery in T1 and a matching transmission in T2,
;; this is equivalent to a noop.  We can prove this by defining permutations.
(check= (count 1 '(1 2 1 2)) 2)
(check= (count 2 '(1 2 1 2)) 2)
(check= (count 3 '(1 2 1 2)) 0)

(property decrement-count-nth (ps :tl i :nat)
  :h (< i (len ps))
  (== (count (nth i ps) ps)
      (1+ (count (nth i ps) (remove-ith ps i))))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property decrement-count-other (ps :tl i :nat p :all)
  :h (^ (< i (len ps)) (!= (nth i ps) p))
  (== (count p ps) (count p (remove-ith ps i)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property increment-count-nth (ps :tl p :all)
  (== (1+ (count p ps)) (count p (cons p ps))))

(property increment-count-other (ps :tl p0 p1 :all)
  :h (!= p0 p1)
  (== (count p1 ps) (count p1 (cons p0 ps))))

(property count-app (p :all ps0 ps1 :tl)
  (== (+ (count p ps0) (count p ps1))
      (count p (append ps0 ps1))))

(in-theory (disable decrement-count-nth
		    decrement-count-other
		    increment-count-nth
		    increment-count-other
		    count-app))

(property mv-is-a-permutation (ps0 ps1 :tl i :nat p :all)
  :proof-timeout 8000
  :h (< i (len ps0))
  (= (count p (append (remove-ith ps0 i)
		   (cons (nth i ps0) ps1)))
     (count p (append ps0 ps1)))
  :hints
  (("Goal":use ((:instance count-app)
		(:instance count-app (ps0 (remove-ith ps0 i))
			   (ps1 (cons (nth i ps0) ps1)))
		(:instance decrement-count-nth (ps ps0))
		(:instance decrement-count-other (ps ps0))
		(:instance increment-count-nth (ps ps1) (p (nth i ps0)))
		(:instance increment-count-other (ps ps1) (p0 (nth i ps0)) (p1 p)))
    :cases ((= p (nth i ps0))))))

(definecd v= (dgs0 dgs1 :dgs) :bool
  :ic (= (len dgs0) (len dgs1))
  (match dgs0
    (() t)
    ((dg . rst) (^ (= (dg-val dg) (dg-val (car dgs1)))
		   (v= rst (cdr dgs1))))))

(definecd swap-dgs-inner (dgs0 dgs1 :dgs i :nat) :dgs
  :ic (< i (len dgs0))
  (append (remove-ith dgs0 i)
       (cons (nth i dgs0) dgs1)))

(property swap-dgs-inner-len (dgs0 dgs1 :dgs i :nat)
  :h (< i (len dgs0))
  (= (len (swap-dgs-inner dgs0 dgs1 i))
     (+ (len dgs0) (len dgs1)))
  :hints (("Goal" :in-theory (enable swap-dgs-inner-definition-rule))))

(definecd swap-dgs (ttbf :two-tbf i :nat) :dgs
  :ic (< i (len (tbf-D (car ttbf))))
  (swap-dgs-inner (tbf-D (car ttbf))
		  (tbf-D (cadr ttbf))
		  i))

(property swap-dgs-len (ttbf :two-tbf i :nat)
  :h (< i (len (tbf-D (car ttbf))))
  (= (len (swap-dgs ttbf i)) (len (tbf-D ([+] ttbf))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     swap-dgs-definition-rule))))

(property ~=/mvd-i-v-contracts (ttbf0 ttbf1 :two-tbf i :nat)
  :proof-timeout 8000
  :h (^ (< i (len (tbf-D (car ttbf0))))
	(= (len (tbf-D ([+] ttbf1)))
	   (len (tbf-D ([+] ttbf0)))))
  (= (len (tbf-D ([+] ttbf1)))
     (len (swap-dgs ttbf0 i)))
  :hints (("Goal" :in-theory (enable [+]-definition-rule))))

;; Say that they're equivalent modulo the move if they're equivalent
;; except for the fact that we moved the nth element from one data queue
;; to the other.  We can do this explicitly, since we just proved that
;; this operation does, indeed, constitute a permutation.
(definecd ~=/mvd-i (ttbf0 ttbf1 :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-D (car ttbf0))))
	 (= (len (tbf-D ([+] ttbf1)))
	    (len (tbf-D ([+] ttbf0)))))
  (^ (= (tbf-l-cap ([+] ttbf0)) (tbf-l-cap ([+] ttbf1)))
     (= (tbf-b-cap ([+] ttbf0)) (tbf-b-cap ([+] ttbf1)))
     (= (tbf-r ([+] ttbf0)) (tbf-r ([+] ttbf1)))
     (equal (tbf-ttl ([+] ttbf0)) (tbf-ttl ([+] ttbf1)))
     (v= (tbf-D ([+] ttbf1))
	 (swap-dgs ttbf0 i)))
  :body-contracts-hints (("Goal" :use (:instance  ~=/mvd-i-v-contracts))))

(property nth-dg-is-record (ttbf :two-tbf i :nat)
  :h (< i (len (tbf-D (car ttbf))))
  (recordp (nth i (tbf-D (car ttbf))))
  :instructions (:pro (:claim (dgsp (tbf-D (car ttbf))))
                      (:claim (dgp (nth i (tbf-D (car ttbf)))))
                      :prove))

(property nth-val-is-pos (ttbf :two-tbf i :nat)
  :h (< i (len (mget :D (car ttbf))))
  (posp (dg-val (nth i (tbf-D (car ttbf)))))
  :instructions (:pro (:claim (dgsp (tbf-D (car ttbf))))
                      (:claim (dgp (nth i (tbf-D (car ttbf)))))
                      :prove))

(property contracts-lem (ttbf :two-tbf i :nat)
  :proof-timeout 8000
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (= (len (tbf-D ([+] (list (tbf-dlv (car ttbf) i)
			    (tbf-trn (cadr ttbf)
				     (dg-val (nth i (tbf-D (car ttbf))))
				     nil)))))
     (len (tbf-D ([+] ttbf))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     tbf-dlv-definition-rule
				     tbf-trn-definition-rule))))

(definecd mv-tbf-0 (ttbf :two-tbf i :nat) :tbf
  :ic (^ (posp (tbf-b (car ttbf)))
	 (< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	 (< i (len (tbf-D (car ttbf)))))
  (tbf-dlv (car ttbf) i))

(definecd mv-tbf-1 (ttbf :two-tbf i :nat) :tbf
  :ic (^ (posp (tbf-b (car ttbf)))
	 (< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	 (< i (len (tbf-D (car ttbf)))))
  (tbf-trn (cadr ttbf)
	   (dg-val (nth i (tbf-D (car ttbf))))
	   nil))

(definecd mv-ttbf (ttbf :two-tbf i :nat) :two-tbf
  :ic (^ (posp (tbf-b (car ttbf)))
	 (< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	 (< i (len (tbf-D (car ttbf)))))
  (list (mv-tbf-0 ttbf i)
	(mv-tbf-1 ttbf i)))

(property contracts-lem-2a (ttbf :two-tbf i :nat)
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (< i (len (tbf-D (car ttbf))))
  :hints (("Goal" :use ((:instance contracts-lem)
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)))))

(property contracts-lem-2b (ttbf :two-tbf i :nat)
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (= (len (tbf-D ([+] (mv-ttbf ttbf i))))
     (len (tbf-D ([+] ttbf))))
  :hints (("Goal" :use ((:instance contracts-lem)
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)))))

(definecd mv-lem-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (posp (tbf-b (car ttbf)))
	 (< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	 (< i (len (tbf-D (car ttbf)))))
  (~=/mvd-i ttbf (mv-ttbf ttbf i) i)
  :body-contracts-hints (("Goal" :use ((:instance contracts-lem-2a)
				       (:instance contracts-lem-2b)))))

(property v=-dgs-reduction (dgs0 dgs1 :dgs dg :dg ttl :nat-ord)
  (v= (append (incr-ttl dgs0 ttl) (cons (dg (mget :val dg) ttl) dgs1))
      (append dgs0 (cons dg dgs1)))
  :hints (("Goal" :in-theory (enable v=-definition-rule
				     incr-ttl-definition-rule))))

(property mv-lem-1 (ttbf :two-tbf i :nat)
  :proof-timeout 100000 
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (^ (= (tbf-l-cap ([+] ttbf))
	(tbf-l-cap ([+] (mv-ttbf ttbf i))))
     (= (tbf-b-cap ([+] ttbf))
	(tbf-b-cap ([+] (mv-ttbf ttbf i))))
     (= (tbf-r ([+] ttbf))
	(tbf-r ([+] (mv-ttbf ttbf i)))))
  :hints (("Goal" :use ((:instance contracts-lem-2a)
			(:instance contracts-lem-2b)
			(:instance mv-lem-witness-definition-rule)
			(:instance ~=/mvd-i-definition-rule (ttbf0 ttbf)
				   (ttbf1 (mv-ttbf ttbf i)))
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule
				   (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)
			(:instance tbf-dlv-definition-rule
				   (tbf (car ttbf)))
			(:instance tbf-trn-definition-rule
				   (tbf (cadr ttbf))
				   (x (dg-val (nth i (tbf-D (car ttbf)))))
				   (drop nil))))))

(property mv-lem-2 (ttbf :two-tbf i :nat)
  :proof-timeout 100000 
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (equal (tbf-ttl ([+] ttbf))
	 (tbf-ttl ([+] (mv-ttbf ttbf i))))
  :hints (("Goal" :use ((:instance contracts-lem-2a)
			(:instance contracts-lem-2b)
			(:instance mv-lem-witness-definition-rule)
			(:instance ~=/mvd-i-definition-rule (ttbf0 ttbf)
				   (ttbf1 (mv-ttbf ttbf i)))
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule
				   (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)
			(:instance tbf-dlv-definition-rule
				   (tbf (car ttbf)))
			(:instance tbf-trn-definition-rule
				   (tbf (cadr ttbf))
				   (x (dg-val (nth i (tbf-D (car ttbf)))))
				   (drop nil)))
	   :in-theory (enable ord+-definition-rule))))

(definecd mv-lem-3-helper (ttbf :two-tbf i :nat) :bool
  :ic (^ (posp (tbf-b (car ttbf)))
	 (< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	 (< i (len (tbf-D (car ttbf)))))
  (v= (tbf-d ([+] (mv-ttbf ttbf i)))
      (swap-dgs ttbf i))
  :body-contracts-hints (("Goal" :use (:instance contracts-lem-2b))))

;; This one is CRAZY slow.  Could be attacked later in a strategic fashion.
(property mv-lem-3 (ttbf :two-tbf i :nat)
  :proof-timeout 100000 
  :h (^ (posp (tbf-b (car ttbf)))
	(< (len (tbf-D (cadr ttbf))) (tbf-l-cap (cadr ttbf)))
	(< i (len (tbf-D (car ttbf)))))
  (mv-lem-3-helper ttbf i)
  :hints (("Goal" :use ((:instance mv-lem-3-helper-definition-rule)
			(:instance contracts-lem-2a)
			(:instance contracts-lem-2b)
			(:instance mv-lem-witness-definition-rule)
			(:instance ~=/mvd-i-definition-rule (ttbf0 ttbf)
				   (ttbf1 (mv-ttbf ttbf i)))
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule
				   (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)
			(:instance tbf-dlv-definition-rule
				   (tbf (car ttbf)))
			(:instance tbf-trn-definition-rule
				   (tbf (cadr ttbf))
				   (x (dg-val (nth i (tbf-D (car ttbf)))))
				   (drop nil))
			(:instance swap-dgs-definition-rule)
			(:instance swap-dgs-inner-definition-rule
				   (dgs0 (tbf-D (car ttbf)))
				   (dgs1 (tbf-D (cadr ttbf))))
			(:instance v=-dgs-reduction
				   (dgs0 (remove-ith (tbf-D (car ttbf)) i))
				   (dgs1 (tbf-D (cadr ttbf)))
				   (ttl (tbf-ttl (cadr (mv-ttbf ttbf i))))
				   (dg (nth i (tbf-D (car ttbf))))))
	   :in-theory (enable ord+-definition-rule))))

;; There is one important difference, which we highlight right here.
;; Namely, stuff in the second queue cannot go "back" to the first one.
;; Why would this matter?  Well, what if we have the second queue have size 1,
;; and the first have size 2.  Now consider this scenario.
;; [a _ _][_] = [a _ _ _]
;; [b a _][_] = [b a _ _]
;; [c b a][_] = [c b a _]
;; Now I try to insert d.  There is no way to insert it on the left
;; and then deliver it, because in order to make room for it, I need to
;; move c, b, or a into the second queue.
;; However, on the right I could insert it and then immediately deliver it.
;; Thus, the equivalence does NOT capture scenarios where messages are
;; reordered by swaps of the form (i, j) where i < j (WLOG), i < len(t1),
;; and j >= len(t1).  In other words, t1 [+] t2 has _strictly more_ behaviors
;; than t1 |> t2.
(defthm mv-theorem
  (=> (^ (two-tbfp ttbf)
         (natp i)
         (posp (tbf-b (car ttbf)))
         (< (len (tbf-d (cadr ttbf)))
            (tbf-l-cap (cadr ttbf)))
         (< i (len (tbf-d (car ttbf)))))
      (mv-lem-witness ttbf i))
  :instructions ((:use (:instance mv-lem-witness-definition-rule))
                 (:use (:instance mv-lem-3-helper-definition-rule))
                 (:use (:instance mv-lem-3))
                 (:use (:instance mv-lem-2))
                 (:use (:instance mv-lem-1))
                 :pro
                 (:use (:instance ~=/mvd-i-definition-rule (ttbf0 ttbf)
                                  (ttbf1 (mv-ttbf ttbf i))))
                 :pro
                 (:claim (and (= (tbf-l-cap ([+] ttbf))
                                 (tbf-l-cap ([+] (mv-ttbf ttbf i))))
                              (= (tbf-b-cap ([+] ttbf))
                                 (tbf-b-cap ([+] (mv-ttbf ttbf i))))
                              (= (tbf-r ([+] ttbf))
                                 (tbf-r ([+] (mv-ttbf ttbf i))))
                              (equal (tbf-ttl ([+] ttbf))
                                     (tbf-ttl ([+] (mv-ttbf ttbf i))))
                              (v= (tbf-d ([+] (mv-ttbf ttbf i)))
                                  (swap-dgs ttbf i))))
                 (:use (:instance contracts-lem-2b))
                 :prove))

(definecd all-nz (dgs :dgs) :bool
  (match dgs
    (() t)
    ((dg . rst) (^ (!= 0 (dg-ttl dg)) (all-nz rst)))))

(property all-nz->age-all-len=len (dgs :dgs)
  :h (all-nz dgs)
  (= (len (age-all dgs)) (len dgs))
  :hints (("Goal" :in-theory (enable all-nz-definition-rule
				     age-all-definition-rule))))

(property all-nz->age-all->dgs->poss= (dgs :dgs)
  :h (all-nz dgs)
  (equal (dgs->poss (age-all dgs)) (dgs->poss dgs))
  :hints (("Goal" :in-theory (enable dgs->poss-definition-rule
				     age-all-definition-rule
				     all-nz-definition-rule))))

(property all-nz->tbf-tick->dgs->poss= (tbf :tbf)
  :h (all-nz (tbf-D tbf))
  (equal (dgs->poss (tbf-D (tbf-tick tbf))) (dgs->poss (tbf-D tbf)))
  :hints (("Goal" :in-theory (enable tbf-tick-definition-rule
				     tbf-age-definition-rule))))

(property data-helper-for-tick-1 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-D (car ttbf)))
	(all-nz (tbf-D (cadr ttbf))))
  (equal (dgs->poss (tbf-D ([+] ttbf)))
	 (dgs->poss (tbf-D ([+] (list (tbf-tick (car ttbf)) (cadr ttbf))))))
  :hints (("Goal" :use ((:instance dgs->poss-app
				   (dgs0 (incr-ttl (tbf-d (car (list (tbf-tick (car ttbf))
								     (cadr ttbf))))
						   (tbf-ttl (cadr (list (tbf-tick (car ttbf))
									(cadr ttbf))))))
				   (dgs1 (tbf-d (cadr (list (tbf-tick (car ttbf))
							    (cadr ttbf))))))
			(:instance dgs->poss-app
				   (dgs0 (incr-ttl (tbf-d (car ttbf))
						   (tbf-ttl (cadr ttbf))))
				   (dgs1 (tbf-d (cadr ttbf))))
			(:instance dgs->poss-app (dgs0 (tbf-d (car ttbf)))
				   (dgs1 (tbf-d (cadr ttbf))))
			(:instance dgs->poss-ignore-incr
				   (dgs (tbf-d (car ttbf)))
				   (del (tbf-ttl (cadr ttbf))))
			(:instance dgs->poss-ignore-incr
				   (dgs (tbf-d (car (list (tbf-tick (car ttbf))
							  (cadr ttbf)))))
				   (del (tbf-ttl (cadr (list (tbf-tick (car ttbf))
							     (cadr ttbf))))))
			(:instance all-nz->tbf-tick->dgs->poss=
				   (tbf (car ttbf)))
			(:instance [+]-definition-rule
				   (ttbf (list (tbf-tick (car ttbf))
					       (cadr ttbf))))
			(:instance [+]-definition-rule)))))

;; If (T1 |> T2) does a tick in T1, this is equivalent to a noop, provided nothing disappears.
(defthm tick-t1-thm
  (=> (^ (two-tbfp ttbf)
         (all-nz (tbf-d (car ttbf)))
         (all-nz (tbf-d (cadr ttbf))))
      (~= ([+] ttbf)
          ([+] (list (tbf-tick (car ttbf))
                     (cadr ttbf)))))
  :instructions ((:use (:instance ~=-definition-rule (t1 ([+] ttbf))
                                  (t2 ([+] (list (tbf-tick (car ttbf))
                                                 (cadr ttbf))))))
                 (:use (:instance [+]-definition-rule))
                 (:use (:instance [+]-definition-rule
                                  (ttbf (list (tbf-tick (car ttbf))
                                              (cadr ttbf)))))
                 (:use (:instance tbf-tick-definition-rule
                                  (tbf (car ttbf))))
                 (:use (:instance tbf-age-definition-rule
                                  (tbf (mset :b
                                             (min (+ (tbf-b (car ttbf))
                                                     (tbf-r (car ttbf)))
                                                  (tbf-b-cap (car ttbf)))
                                             (car ttbf)))))
                 :prove))

(property data-helper-for-tick-2 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-D (car ttbf)))
	(all-nz (tbf-D (cadr ttbf))))
  (equal (dgs->poss (tbf-D ([+] ttbf)))
	 (dgs->poss (tbf-D ([+] (list (car ttbf) (tbf-tick (cadr ttbf)))))))
  :hints (("Goal" :use ((:instance dgs->poss-app
				   (dgs0 (incr-ttl (tbf-d (car (list (car ttbf)
								     (tbf-tick (cadr ttbf)))))
						   (tbf-ttl (cadr (list (car ttbf)
								(tbf-tick (cadr ttbf)))))))
				   (dgs1 (tbf-d (cadr (list (car ttbf)
							    (tbf-tick (cadr ttbf)))))))
			(:instance dgs->poss-app
				   (dgs0 (incr-ttl (tbf-d (car ttbf))
						   (tbf-ttl (cadr ttbf))))
				   (dgs1 (tbf-d (cadr ttbf))))
			(:instance dgs->poss-app (dgs0 (tbf-d (car ttbf)))
				   (dgs1 (tbf-d (cadr ttbf))))
			(:instance dgs->poss-ignore-incr
				   (dgs (tbf-d (car ttbf)))
				   (del (tbf-ttl (cadr ttbf))))
			(:instance dgs->poss-ignore-incr
				   (dgs (tbf-d (car (list (car ttbf)
							  (tbf-tick (cadr ttbf))))))
				   (del (tbf-ttl (cadr (list (car ttbf)
							     (tbf-tick (cadr ttbf)))))))
			(:instance all-nz->tbf-tick->dgs->poss=
				   (tbf (cadr ttbf)))
			(:instance [+]-definition-rule
				   (ttbf (list (car ttbf)
					       (tbf-tick (cadr ttbf)))))
			(:instance [+]-definition-rule)))))

;; If (T1 |> T2) does a tick in T2, this is equivalent to a noop, provided nothing disappears.
(defthm tick-t2-thm
  (=> (^ (two-tbfp ttbf)
         (all-nz (tbf-d (car ttbf)))
         (all-nz (tbf-d (cadr ttbf))))
      (~= ([+] ttbf)
          ([+] (list (car ttbf)
                     (tbf-tick (cadr ttbf))))))
  :instructions ((:use (:instance ~=-definition-rule (t1 ([+] ttbf))
                                  (t2 ([+] (list (car ttbf)
                                                 (tbf-tick (cadr ttbf)))))))
                 (:use (:instance [+]-definition-rule))
                 (:use (:instance [+]-definition-rule
                                  (ttbf (list (car ttbf)
                                              (tbf-tick (cadr ttbf))))))
                 (:use (:instance tbf-tick-definition-rule
                                  (tbf (cadr ttbf))))
                 (:use (:instance tbf-age-definition-rule
                                  (tbf (mset :b
                                             (min (+ (tbf-b (cadr ttbf))
                                                     (tbf-r (cadr ttbf)))
                                                  (tbf-b-cap (cadr ttbf)))
                                             (cadr ttbf)))))
                 :prove))
