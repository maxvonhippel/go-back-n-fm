(in-package "ACL2S")

(defun nth-ord (n) (if (== n 0) (omega) (1+ n)))

(register-type nat-ord :predicate o-p :enumerator nth-ord)

(check= (posp (omega)) nil)
(check= (o-p 4) t)
(check= (o-p 0) t)
(check= (o-p (omega)) t)
(check= (o-p 3/4) nil)

#|
Model & theory of a Token Bucket Filter
|#

(defdata tdg (record (id . pos) (del . nat-ord) (pld . string))) ;; timed datagram

(defdata tdgs (listof tdg)) ;; many timed datagrams

(defdata poss (listof pos)) ;; pos-list

(include-book "higher-order")

(create-map* (lambda (d) (tdg-id d)) tdgsp possp)

(definecd tdgs->poss (tdgs :tdgs) :poss
  (map* (lambda (d) (tdg-id d)) tdgs))

;; age all the datagrams in a list
(definecd age-all (tdgs :tdgs) :tdgs
  (match tdgs
    (() ())
    ((tdg . rst)
     (if (o< 0 (tdg-del tdg))
	 (cons (mset :del (o- (tdg-del tdg) 1) tdg)
	       (age-all rst))
       (age-all rst)))))

(defdata tbf
  (record (b-cap . pos) ;; bucket capacity (how large can bkt be?)
	  (d-cap . pos) ;; link capacity (how many bytes can be in data?)
	  (bkt . nat) ;; bucket, which must always be <= b-cap
	  (rat . pos) ;; rate at which the bucket refills
	  (del . nat-ord) ;; maximum delay of a datagram in data
	  (data . tdgs))) ;; data in-transit, must satisfy sz(D) <= d-cap

(definecd tbf-age (tbf :tbf) :tbf
  (mset :data (age-all (tbf-data tbf)) tbf))

;; Tick transition for a tbf
(definecd tbf-tick (tbf :tbf) :tbf
  (mset :bkt (min (+ (tbf-bkt tbf) (tbf-rat tbf))
		   (tbf-b-cap tbf))
	 (tbf-age tbf)))

;; Token decay
(definecd tbf-decay (tbf :tbf) :tbf
  (if (posp (tbf-bkt tbf))
      (mset :bkt (1- (tbf-bkt tbf)) tbf)
    tbf))

;; The sz of a (timed) datagram is the length of the payload.
(definecd sz (tdgs :tdgs) :nat
  (match tdgs
    (() 0)
    ((tdg . rst) (+ (length (tdg-pld tdg)) (sz rst)))))

;; Transmission transition for a tbf
(definecd tbf-prc (tbf :tbf x :pos pld :string) :tbf
  (if (<= (+ (sz (tbf-data tbf)) (length pld))
	  (tbf-d-cap tbf))
      (mset :data (cons (tdg x (tbf-del tbf) pld) (tbf-data tbf)) tbf)
    tbf))

(definecd remove-ith (ps :tl i :nat) :tl
  :ic (< i (len ps))
  (if (= i 0) (cdr ps) (cons (car ps) (remove-ith (cdr ps) (1- i)))))

(property remove-prefix (ps0 ps1 :tl i :nat)
  :h (< i (len ps0))
  (== (append (remove-ith ps0 i) ps1)
      (remove-ith (append ps0 ps1) i))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property remove-postfix (ps0 ps1 :tl i :nat)
  :h (< i (len ps1))
  (== (append ps0 (remove-ith ps1 i))
      (remove-ith (append ps0 ps1) (+ (len ps0) i)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

;; Test a few times ...
(check= (remove-ith '(1 2 3) 0) '(2 3))
(check= (remove-ith '(1 2 3) 1) '(1 3))
(check= (remove-ith '(1 2 3) 2) '(1 2))

(property remove-ith-contracts (tdgs :tdgs i :nat)
  :h (< i (len tdgs))
  (tdgsp (remove-ith tdgs i))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property remove-ith-decrs-sz (tdgs :tdgs i :nat)
  :h (< i (len tdgs))
  (= (sz (remove-ith tdgs i))
     (- (sz tdgs) (length (tdg-pld (nth i tdgs)))))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule sz-definition-rule))))

(propertyd remove-ith-decreases-sz (tdgs :tdgs i :nat)
	   :h (< i (len tdgs))
	   (= (+ (sz (remove-ith tdgs i)) (length (tdg-pld (nth i tdgs))))
	      (sz tdgs))
	   :hints (("Goal" :in-theory (enable sz-definition-rule
					      remove-ith-definition-rule))))

;; Claim: sz(data) - sz(data') = bkt - bkt' = len(nth dg)
(definecd tbf-fwd (tbf :tbf i :nat) :tbf
  :ic (^ (< i (len (tbf-data tbf)))
	 (<= (length (tdg-pld (nth i (tbf-data tbf))))
	     (tbf-bkt tbf)))
  ;; Theorem: TBF can only fwd bkt many bytes, and after forwarding, its bkt
  ;; is decremented by the sz of the forwarded datagram.
  :oc (^ (<= (- (sz (tbf-data (tbf-fwd tbf i))) (sz (tbf-data tbf)))
	     (tbf-bkt tbf))
         (= (- (sz (tbf-data tbf)) (sz (tbf-data (tbf-fwd tbf i))))
	    (length (tdg-pld (nth i (tbf-data tbf))))))
  (msets tbf :bkt (- (tbf-bkt tbf)
		     (length (tdg-pld (nth i (tbf-data tbf)))))
	 :data (remove-ith (tbf-data tbf) i))
  :function-contract-hints (("Goal" :use (:instance remove-ith-decreases-sz
						    (tdgs (tbf-data tbf))))))

(definecd tbf-drop (tbf :tbf i :nat) :tbf
  :ic (< i (len (tbf-data tbf)))
  (mset :data (remove-ith (tbf-data tbf) i) tbf))

;; Suppose we deliver a message, removing it from the queue.  Then we
;; should have some way to check which message (up to identity) was removed.
(definecd witness-i (ps0 ps1 :tl) :nat
  :ic (= (1+ (len ps1)) (len ps0))
  :oc (<= (witness-i ps0 ps1) (len ps1))
  (if (v (! (consp ps1))
	 (!= (car ps0) (car ps1)))
      0
    (1+ (witness-i (cdr ps0) (cdr ps1)))))

;; Remove-ith subtracts one from the length.
(property remove-ith-sub1 (i :nat ps :tl)
  :h (< i (len ps))
  (= (len (remove-ith ps i)) (1- (len ps)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

;; Witness-i returns a witness.
(property witness-i-correct (ps0 ps1 :tl)
  :h (= (1+ (len ps1)) (len ps0))
  (^ (< (witness-i ps0 ps1) (len ps0))
     (v (= (witness-i ps0 ps1) (len ps1))
	(!= (nth (witness-i ps0 ps1) ps0)
	    (nth (witness-i ps0 ps1) ps1))))
  :hints (("Goal" :in-theory (enable witness-i-definition-rule))))

(definecd tbfIntR (tbf0 tbf1 :tbf) :bool
  (v (== tbf1 (tbf-tick tbf0))
     (== tbf1 (tbf-decay tbf0))
     (^ (consp (tbf-data tbf0))
	(= (1+ (len (tbf-data tbf1))) (len (tbf-data tbf0)))
	(== tbf1 (tbf-drop tbf0 (witness-i (tbf-data tbf0) (tbf-data tbf1)))))))

(definecd tbfProcR (tbf0 tbf1 :tbf) :bool
  (^ (consp (tbf-data tbf1))
     (let ((tdg (car (tbf-data tbf1))))
       (== (tbf-prc tbf0 (tdg-id tdg) (tdg-pld tdg)) tbf1))))

(definecd tbfFwdR (tbf0 tbf1 :tbf) :bool
  (^ (= (1+ (len (tbf-data tbf1))) (len (tbf-data tbf0)))
     (let ((i (witness-i (tbf-data tbf0) (tbf-data tbf1))))
       (^ (>= (tbf-bkt tbf0) (length (tdg-pld (nth i (tbf-data tbf0)))))
	  (== (tbf-fwd tbf0 i) tbf1)))))

;; Entire transition relation for a TBF
(definecd tbf-tranr (tbf0 tbf1 :tbf) :bool
  (v (tbfIntR tbf0 tbf1) (tbfProcR tbf0 tbf1) (tbfFwdR tbf0 tbf1)))
