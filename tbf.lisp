(in-package "ACL2S")

(defun nth-ord (n)
  (if (== n 0) (make-ord 1 1 0) (1+ n)))

(register-type nat-ord :predicate o-p :enumerator nth-ord)

#|
Model & theory of a Token Bucket Filter
|#

(defdata dg (record (val . pos) (ttl . nat-ord))) ;; datagram

(defdata dgs (listof dg)) ;; many datagrams

(defdata poss (listof pos))
(definecd dgs->poss (dgs :dgs) :poss
  (match dgs
    (() ())
    ((dg . rst) (cons (dg-val dg) (dgs->poss rst)))))

;; age all the datagrams in a list
(definecd age-all (dgs :dgs) :dgs
  (match dgs
    (() ())
    ((dg . rst)
     (cond
      ((posp (dg-ttl dg)) (cons (mset :ttl (1- (dg-ttl dg)) dg) (age-all rst)))
      ((== 0 (dg-ttl dg)) (age-all rst))
      ;; last case it must be an ordinal, so don't touch it
      ((! (o-finp (dg-ttl dg))) (cons dg (age-all rst)))))))

(check= (posp (make-ord 1 1 0)) nil)

(defdata tbf
  (record (b-cap . pos) ;; bucket capacity
	  (l-cap . pos) ;; link capacity
	  (b . nat) ;; bucket
	  (r . pos) ;; rate
	  (ttl . nat-ord) ;; ttl for datagrams
	  (D . dgs))) ;; data in-transit

;; Token decay
(definec token-decay (tbf :tbf) :tbf
  (if (posp (tbf-b tbf))
      (mset :b (1- (tbf-b tbf)) tbf)
    tbf))

(definecd tbf-age (tbf :tbf) :tbf
  (mset :D (age-all (tbf-D tbf)) tbf))

;; Tick transition for a tbf
(definec tbf-tick (tbf :tbf) :tbf
  (tbf-age
   (mset :b (min (+ (tbf-b tbf) (tbf-r tbf))
		 (tbf-b-cap tbf))
	 tbf)))

;; Transmission transition for a tbf
(definec tbf-trn (tbf :tbf x :pos drop :bool) :tbf
  (if (^ (< (len (tbf-D tbf))
	    (tbf-l-cap tbf))
	 (! drop))
      (mset :D (cons (dg x (tbf-ttl tbf)) (tbf-D tbf)) tbf)
    tbf))

(definecd remove-ith (ps :tl i :nat) :tl
  :ic (< i (len ps))
  (if (== i 0) (cdr ps) (cons (car ps) (remove-ith (cdr ps) (1- i)))))

(property remove-ith-slider (ps :tl i :nat)
  :h (^ (< i (len ps)) (posp i))
  (== (remove-ith ps i)
      (cons (car ps) (remove-ith (cdr ps) (1- i))))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(definecd remove-prefix-inductor (ps0 ps1 :tl i :nat) :nat
  :ic (< i (len ps0))
  (if (== i 0) 0
    (remove-prefix-inductor (cdr ps0) ps1 (1- i))))

(property remove-prefix (ps0 ps1 :tl i :nat)
  :h (< i (len ps0))
  (== (append (remove-ith ps0 i) ps1)
      (remove-ith (append ps0 ps1) i))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule)
	   :induct (remove-prefix-inductor ps0 ps1 i))))

(definecd remove-postfix-inductor (ps0 ps1 :tl i :nat) :nat
  :ic (< i (len ps1))
  (if (consp ps0)
      (remove-postfix-inductor (cdr ps0) ps1 i)
    0))

(property remove-postfix (ps0 ps1 :tl i :nat)
  :h (< i (len ps1))
  (== (append ps0 (remove-ith ps1 i))
      (remove-ith (append ps0 ps1) (+ (len ps0) i)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule)
	   :induct (remove-postfix-inductor ps0 ps1 i))))

;; Test a few times ...
(check= (remove-ith '(1 2 3) 0) '(2 3))
(check= (remove-ith '(1 2 3) 1) '(1 3))
(check= (remove-ith '(1 2 3) 2) '(1 2))

(property remove-ith-contracts (dgs :dgs i :nat)
  :h (< i (len dgs))
  (dgsp (remove-ith dgs i))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

;; Delivery transition for a tbf.  If the transition doesn't sync
;; with a corresponding rcv on an endpoint, then it constitutes a loss.
(definec tbf-dlv (tbf :tbf i :nat) :tbf
  :ic (^ (< i (len (tbf-D tbf))) (posp (tbf-b tbf)))
  (mset :b (1- (tbf-b tbf))
	(mset :D (remove-ith (tbf-D tbf) i) tbf))
  :function-contract-hints (("Goal" :use (:instance remove-ith-contracts (dgs (tbf-D tbf))))))

;; Suppose we deliver a message, removing it from the queue.  Then we
;; should have some way to check which message (up to identity) was removed.
(definec witness-i (ps0 ps1 :tl) :nat
  :ic (== (1+ (len ps1)) (len ps0))
  (if (or (! (consp ps1))
	  (!= (car ps0) (car ps1)))
      0
    (1+ (witness-i (cdr ps0) (cdr ps1)))))

;; Remove-ith subtracts one from the length.
(property remove-ith-sub1 (i :nat ps :tl)
  :h (< i (len ps))
  (== (len (remove-ith ps i)) (1- (len ps)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

;; Witness-i returns a witness.
(property witness-i-correct (ps0 ps1 :tl)
  :h (== (1+ (len ps1)) (len ps0))
  (^ (< (witness-i ps0 ps1) (len ps0))
     (or (== (witness-i ps0 ps1) (len ps1))
	 (!= (nth (witness-i ps0 ps1) ps0)
	     (nth (witness-i ps0 ps1) ps1))))
  :hints (("Goal" :in-theory (enable witness-i-definition-rule))))
