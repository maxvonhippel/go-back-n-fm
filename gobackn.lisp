(in-package "ACL2S")

;; Import theory of tbf
(include-book "tbf")

#|
Model of a sender
|#
(defdata sender-state
  (record (N . pos) ;; window size
	  (hiA . pos) ;; high ack
	  (hiP . pos) ;; high pkt
	  (cur . pos))) ;; next transmission

;; Transition when the sender receives an ACK
;; b* with _
(definecd sender-rcv-ack (ss :sender-state ack :pos) :sender-state
  (if (<= ack (1+ (sender-state-hiP ss))) 
      (b* ((hiA (max (sender-state-hiA ss) ack))
	   (cur (max (sender-state-cur ss) hiA)))
	(msets ss :hiA hiA :cur cur))
    ss))

;; Transition when the sender transmits a PKT
(definecd sender-adv-cur (ss :sender-state) :sender-state
  :ic (< (sender-state-cur ss) (+ (sender-state-N ss) (sender-state-hiA ss)))
  (let* ((cur (sender-state-cur ss))
	 (hiP (max (sender-state-hiP ss) cur)))
    (msets ss :cur (1+ cur) :hiP hiP)))

;; Transition when the sender times out
(definecd sender-timeout (ss :sender-state) :sender-state
  :ic (= (sender-state-cur ss) (+ (sender-state-N ss) (sender-state-hiA ss)))
  (mset :cur (sender-state-hiA ss) ss))

;; Transition relation
(definecd sender-tranr (ss0 ss1 :sender-state) :bool
  (v (== (sender-rcv-ack ss0 (sender-state-hiA ss1)) ss1)
     (^ (< (sender-state-cur ss0) (+ (sender-state-N ss0) (sender-state-hiA ss0)))
	(== (sender-adv-cur ss0) ss1))
     (^ (= (sender-state-cur ss0) (+ (sender-state-N ss0) (sender-state-hiA ss0)))
	(== (sender-timeout ss0) ss1))))

(encapsulate ()
	     (local (defconst *initial-ss-10* (sender-state 10 1 1 2)))
	     
	     (local (definecd initial-ss (N :pos) :sender-state (mset :N N *initial-ss-10*)))
	     
	     (local (in-theory (enable sender-tranr-definition-rule
				       sender-rcv-ack-definition-rule
				       sender-adv-cur-definition-rule
				       sender-timeout-definition-rule
				       initial-ss-definition-rule)))

	     ;; Invariant: HiA ≤ HiP + 1
	     (local 
	      (property (N :pos)
		(<= (sender-state-hiA (initial-ss N)) (1+ (sender-state-hiP (initial-ss N))))))

	     (local
	      (property (ss0 ss1 :sender-state)
		:h (^ (sender-tranr ss0 ss1)
		      (<= (sender-state-hiA ss0) (1+ (sender-state-hiP ss0))))
		(<= (sender-state-hiA ss1) (1+ (sender-state-hiP ss1)))))

	     ;; Invariant: HiA ≤ CurP ≤ HiA + N
	     (local (property (N :pos)
		      (^ (<= (sender-state-hiA (initial-ss N)) (sender-state-cur (initial-ss N)))
			 (<= (sender-state-cur (initial-ss N)) (+ (sender-state-hiA (initial-ss N))
								  (sender-state-N (initial-ss N)))))))

	     (local (property (ss0 ss1 :sender-state)
		      :h (^ (sender-tranr ss0 ss1)
			    (<= (sender-state-hiA ss0) (sender-state-cur ss0))
			    (<= (sender-state-cur ss0) (+ (sender-state-hiA ss0) (sender-state-N ss0))))
		      (^ (<= (sender-state-hiA ss1) (sender-state-cur ss1))
			 (<= (sender-state-cur ss1) (+ (sender-state-hiA ss1) (sender-state-N ss1))))))

	     ;; Invariant: N is constant
	     ;; Invariant: HiA and HiP are non-decreasing
	     (property (ss0 ss1 :sender-state)
	       :h (sender-tranr ss0 ss1)
	       (^ (= (sender-state-N ss0) (sender-state-N ss1))
		  (<= (sender-state-hiA ss0) (sender-state-hiA ss1))
		  (<= (sender-state-hiP ss0) (sender-state-hiP ss1)))))

#|
Below is a model & theory of a receiver
|#

;; Helper function to check if a list `ps` contains every integer
;; i in the range [1, p].
(definecd has-all (p :pos ps :poss) :bool
  (^ (in p ps) (v (= 1 p) (has-all (1- p ) ps))))

;; Proof that the helper function indeed does what it is supposed to do.
(property has-all-down (p0 p1 :pos ps :poss)
  :h (^ (has-all p1 ps) (<= p0 p1))
  (has-all p0 ps)
  :hints (("Goal" :in-theory (enable has-all-definition-rule))))

;; Recognizer for a cumulative ACK, based on has-all.
(definecd cumackp (a :pos ps :poss) :bool
  (^ (! (in a ps)) (v (= 1 a) (has-all (1- a) ps))))

;; Lemma: If a0 is a cum ACK, and a0 < a1, then a1 is NOT a cum ACK.
(property cumackp-!-up (a0 a1 :pos ps :poss)
  :h (^ (cumackp a0 ps) (< a0 a1))
  (! (cumackp a1 ps))
  :hints (("Goal" :in-theory (enable cumackp-definition-rule
				     has-all-definition-rule)
	   :use ((:instance has-all-down (p0 a0) (p1 (1- a1)))))))

;; Thm: the cumulative ack is unique
(propertyd cumack-is-unique (a0 a1 :pos ps :poss)
  :h (^ (cumackp a0 ps) (cumackp a1 ps))
  (== (= a0 a1) t)
  :hints (("Goal" :cases ((<= a0 a1) (<= a1 a0)))))

;; Next, let's define a global state.
(defdata system
  (record (sender . sender-state)
	  (receiver . poss)
	  (s2r . tbf)
	  (r2s . tbf)))

(definecd nth-id-helper (tdgs0 tdgs1 :tdgs) :tdg
  :ic (= (1+ (len tdgs1)) (len tdgs0))
  (nth (witness-i tdgs0 tdgs1) tdgs0))

(definecd nth-id-helper-lift (sys0 sys1 :system) :pos
  :ic (= (1+ (len (tbf-data (system-r2s sys1)))) (len (tbf-data (system-r2s sys0))))
  (tdg-id (nth-id-helper (tbf-data (system-r2s sys0))
			 (tbf-data (system-r2s sys1)))))

(definecd nth-pld-helper-lift (sys0 sys1 :system) :string
  :ic (= (1+ (len (tbf-data (system-r2s sys1)))) (len (tbf-data (system-r2s sys0))))
  (tdg-pld (nth-id-helper (tbf-data (system-r2s sys0))
			  (tbf-data (system-r2s sys1)))))

(definecd or-cases-system-sender-rcv (sys0 sys1 :system) :bool
  :ic (^ (= (1+ (len (tbf-data (system-r2s sys1)))) (len (tbf-data (system-r2s sys0))))
	 (posp (tbf-bkt (system-r2s sys0))))
  (v (== (system-sender sys1)
	 (sender-rcv-ack (system-sender sys0)
			 (nth-id-helper-lift sys0 sys1)))
     (== (system-sender sys1) (system-sender sys0))))

;; Allow dropping at rcv step as well ...
(definecd system-sender-rcv (sys0 sys1 :system) :bool
  (^
   (= (1+ (len (tbf-data (system-r2s sys1)))) (len (tbf-data (system-r2s sys0))))
   (>= (tbf-bkt (system-r2s sys0))
       (length (tdg-pld (nth (witness-i (tbf-data (system-r2s sys0))
				     (tbf-data (system-r2s sys1)))
			  (tbf-data (system-r2s sys0))))))
   (== (system-r2s sys1)
       (tbf-fwd (system-r2s sys0)
		(witness-i (tbf-data (system-r2s sys0))
			   (tbf-data (system-r2s sys1)))))
   (== (system-sender sys1)
       (sender-rcv-ack (system-sender sys0)
		       (nth-id-helper-lift sys0 sys1)))
   (== (system-receiver sys0) (system-receiver sys1))
   (== (system-s2r sys0) (system-s2r sys1))))

(property rem-upper-bound (x :nat y :pos)
  (^ (< (rem x y) y)
     (<= (rem x y) x))
  :rule-classes (:linear :rewrite))

;; Transition function component 1
(definecd system-sender-rcv-step (sys :system i :nat) :system
  :ic (^ (consp (tbf-data (system-r2s sys)))
	 (>= (tbf-bkt (system-r2s sys))
	     (length (tdg-pld (nth (if (= i 0) i (rem i (len (tbf-data (system-r2s sys)))))
				(tbf-data (system-r2s sys)))))))
  (let ((i (if (= i 0) i (rem i (len (tbf-data (system-r2s sys)))))))
    (msets sys :r2s (tbf-fwd (system-r2s sys) i)
	   :sender (sender-rcv-ack (system-sender sys)
				   (tdg-id (nth i (tbf-data (system-r2s sys)))))))
  :function-contract-hints
  (("Goal" :use (:instance rem-upper-bound (x i) (y (len (tbf-data (system-r2s sys))))))))

(definecd system-sender-prc (sys0 sys1 :system pld :string) :bool
  (^ (< (sender-state-cur (system-sender sys0))
	(+ (sender-state-N (system-sender sys0))
	   (sender-state-hiA (system-sender sys0))))
     (== (sender-adv-cur (system-sender sys0))
	 (system-sender sys1))
     (== (system-s2r sys1)
	 (tbf-prc (system-s2r sys0)
		  (sender-state-cur (system-sender sys0))
		  pld))
     (== (system-r2s sys0) (system-r2s sys1))
     (== (system-receiver sys0) (system-receiver sys1))))

;; Transition function component 2
(definecd system-sender-prc-step (sys :system pld :string) :system
  :ic (< (sender-state-cur (system-sender sys))
	 (+ (sender-state-N (system-sender sys))
	    (sender-state-hiA (system-sender sys))))
  (msets sys :s2r
	 (tbf-prc (system-s2r sys)
		  (sender-state-cur (system-sender sys))
		  pld)
	 :sender (sender-adv-cur (system-sender sys))))

(definecd system-sender-to (sys0 sys1 :system) :bool
  (^ (= (sender-state-cur (system-sender sys0))
	(+ (sender-state-N (system-sender sys0)) (sender-state-hiA (system-sender sys0))))
     (== (system-sender sys1) (sender-timeout (system-sender sys0)))
     (== (system-receiver sys0) (system-receiver sys1))
     (== (system-s2r sys0) (system-s2r sys1))
     (== (system-r2s sys0) (system-r2s sys1))))

;; Transition function component 3
(definecd system-sender-to-step (sys :system) :system
  :ic (= (sender-state-cur (system-sender sys))
	 (+ (sender-state-N (system-sender sys)) (sender-state-hiA (system-sender sys))))
  (mset :sender (sender-timeout (system-sender sys)) sys))

(definecd system-r2s-decay (sys0 sys1 :system) :bool
  (^ (== (tbf-decay (system-r2s sys0)) (system-r2s sys1))
     (== (system-s2r sys0) (system-s2r sys1))
     (== (system-sender sys0) (system-sender sys1))
     (== (system-receiver sys0) (system-receiver sys1))))

;; Transition function component 4
(definecd system-r2s-decay-step (sys :system) :system
  (mset :r2s (tbf-decay (system-r2s sys)) sys))

(definecd system-s2r-decay (sys0 sys1 :system) :bool
  (^ (== (tbf-decay (system-s2r sys0)) (system-s2r sys1))
     (== (system-r2s sys0) (system-r2s sys1))
     (== (system-sender sys0) (system-sender sys1))
     (== (system-receiver sys0) (system-receiver sys1))))

;; Transition function component 5
(definecd system-s2r-decay-step (sys :system) :system
  (mset :s2r (tbf-decay (system-s2r sys)) sys))

(definecd system-r2s-tick (sys0 sys1 :system) :bool
  (^ (== (tbf-tick (system-r2s sys0)) (system-r2s sys1))
     (== (system-s2r sys0) (system-s2r sys1))
     (== (system-sender sys0) (system-sender sys1))
     (== (system-receiver sys0) (system-receiver sys1))))

;; Transition function component 6
(definecd system-r2s-tick-step (sys :system) :system
  (mset :r2s (tbf-tick (system-r2s sys)) sys))

(definecd system-s2r-tick (sys0 sys1 :system) :bool
  (^ (== (tbf-tick (system-s2r sys0)) (system-s2r sys1))
     (== (system-r2s sys0) (system-r2s sys1))
     (== (system-sender sys0) (system-sender sys1))
     (== (system-receiver sys0) (system-receiver sys1))))

;; Transition function component 7
(definecd system-s2r-tick-step (sys :system) :system
  (mset :s2r (tbf-tick (system-s2r sys)) sys))

(definecd system-receiver-rcv (sys0 sys1 :system) :bool
  (^ (= (1+ (len (tbf-data (system-s2r sys1))))
	(len (tbf-data (system-s2r sys0))))
     (<= (length (tdg-pld (nth (witness-i (tbf-data (system-s2r sys0))
				       (tbf-data (system-s2r sys1)))
			    (tbf-data (system-s2r sys0)))))
	 (tbf-bkt (system-s2r sys0)))
     (== (system-receiver sys1)
	 (if (cumackp (tdg-id (nth (witness-i (tbf-data (system-s2r sys0))
					      (tbf-data (system-s2r sys1)))
				   (tbf-data (system-s2r sys0))))
		      (system-receiver sys0))
	     (cons (tdg-id (nth (witness-i (tbf-data (system-s2r sys0))
					   (tbf-data (system-s2r sys1)))
				(tbf-data (system-s2r sys0))))
		   (system-receiver sys0))
	   (system-receiver sys0)))
     (== (system-r2s sys0) (system-r2s sys1))
     (== (system-s2r sys0) (tbf-fwd (system-s2r sys0) (witness-i (tbf-data (system-s2r sys0))
								 (tbf-data (system-s2r sys1)))))
     (== (system-sender sys0) (system-sender sys1))))

;; Transition function component 8
(definecd system-receiver-rcv-step (sys :system i :nat) :system
  :ic (^ (consp (tbf-data (system-s2r sys)))
	 (>= (tbf-bkt (system-s2r sys))
	     (length (tdg-pld (nth (if (= i 0) i (rem i (len (tbf-data (system-s2r sys)))))
				(tbf-data (system-s2r sys)))))))
  (let ((i (if (= i 0) i (rem i (len (tbf-data (system-s2r sys)))))))
    (msets sys :s2r (tbf-fwd (system-s2r sys) i) :receiver
	   (if (in (tdg-id (nth i (tbf-data (system-s2r sys))))
		   (system-receiver sys))
	       (system-receiver sys)
	     (cons (tdg-id (nth i (tbf-data (system-s2r sys))))
		   (system-receiver sys)))))
  :function-contract-hints
  (("Goal" :use (:instance rem-upper-bound (x i) (y (len (tbf-data (system-s2r sys))))))))

;; Thm: the set of acks the receiver keeps track of is non-decreasing according to the
;; subset relation over time.
(property (a :pos sys0 sys1 :system)
  :h (^ (system-receiver-rcv sys0 sys1)
	(in a (system-receiver sys0)))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-receiver-rcv-definition-rule))))

(definecd system-receiver-prc (sys0 sys1 :system) :bool
  (^ (== (system-s2r sys0) (system-s2r sys1))
     (== (system-receiver sys0) (system-receiver sys1))
     (== (system-sender sys0) (system-sender sys1))
     ;; successful delivery ...
     (= (len (tbf-data (system-r2s sys0)))
	(1+ (len (tbf-data (system-r2s sys1)))))
     ;; ... of a cumulative ack ...
     (cumackp (nth-id-helper-lift sys0 sys1)
	      (system-receiver sys0))
     ;; for which we had the tokens to fwd -- and did fwd.
     (<= (length (tdg-pld (nth (witness-i (tbf-data (system-r2s sys0))
				       (tbf-data (system-r2s sys1)))
			    (tbf-data (system-r2s sys0)))))
	 (tbf-bkt (system-r2s sys0)))
     (== (system-r2s sys1)
	 (tbf-fwd (system-r2s sys0)
		  (witness-i (tbf-data (system-r2s sys0))
			     (tbf-data (system-r2s sys1)))))))

(definecd maxl (ps :poss) :nat
  (match ps
    (() 0)
    ((p . rst) (max p (maxl rst)))))

;; Transition function component 9
(definecd system-receiver-prc-step (sys :system pld :string) :system
  (mset :r2s
	(tbf-prc (system-r2s sys)
		 (1+ (maxl (system-receiver sys))) ;; assuming throw away out of order pkts
		 pld)
	sys))

(definecd witness-system-sender-prc-pld (sys0 sys1 :system) :string
  (if (= (1+ (len (tbf-data (system-s2r sys0))))
	 (len (tbf-data (system-s2r sys1))))
      (tdg-pld (nth (witness-i (tbf-data (system-s2r sys1))
			       (tbf-data (system-s2r sys0)))
		    (tbf-data (system-s2r sys1))))
    "blarg"))

;; And a global state transition.
(definecd system-tranr (sys0 sys1 :system) :bool
  (v
   ;; Transition when the sender receives an ACK
   (system-sender-rcv sys0 sys1)
   ;; Transition when the sender transmits a PKT
   (system-sender-prc sys0 sys1 (witness-system-sender-prc-pld sys0 sys1))
   ;; Transition when the sender times out
   (system-sender-to sys0 sys1)
   ;; Transition when one of the tbfs ticks
   (system-s2r-tick sys0 sys1)
   (system-r2s-tick sys0 sys1)
   ;; Transition when one of the tbfs decays
   (system-s2r-decay sys0 sys1)
   (system-r2s-decay sys0 sys1)
   ;; Transition when the receiver receives a new pkt
   (system-receiver-rcv sys0 sys1)
   ;; Transition when the receiver transmits a new ack
   (system-receiver-prc sys0 sys1)))

;; Only sytstem-receiver-rcv changes the rcvd acks.
(property (sys0 sys1 :system)
  :h (v (system-sender-rcv sys0 sys1)
	(system-sender-prc sys0 sys1 (witness-system-sender-prc-pld sys0 sys1))
	(system-sender-to sys0 sys1)
	(system-s2r-tick sys0 sys1)
	(system-r2s-tick sys0 sys1)
	(system-s2r-decay sys0 sys1)
	(system-r2s-decay sys0 sys1)
	(system-receiver-prc sys0 sys1))
  (== (system-receiver sys0) (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-rcv-definition-rule
				     system-sender-prc-definition-rule
				     system-sender-to-definition-rule
				     system-s2r-tick-definition-rule
				     system-r2s-tick-definition-rule
				     system-s2r-decay-definition-rule
				     system-r2s-decay-definition-rule
				     system-receiver-prc-definition-rule))))

(definecd max-tdg-id (tdgs :tdgs) :pos
  :ic (consp tdgs)
  (if (consp (cdr tdgs))
      (max (tdg-id (car tdgs))
	   (max-tdg-id (cdr tdgs)))
    (tdg-id (car tdgs))))

(definecd min-tdg-id (tdgs :tdgs) :pos
  :ic (consp tdgs)
  (if (consp (cdr tdgs))
      (min (tdg-id (car tdgs))
	   (min-tdg-id (cdr tdgs)))
    (tdg-id (car tdgs))))

(definecd get-ids (tdgs :tdgs) :poss
  (match tdgs
    (() ())
    ((tdg . rst) (cons (tdg-id tdg) (get-ids rst)))))

(definecd max-ack<=cur-ack (sys :system a :pos) :bool
  :ic (^ (consp (tbf-data (system-r2s sys)))
	 (cumackp a (get-ids (tbf-data (system-r2s sys)))))
  (<= (max-tdg-id (tbf-data (system-r2s sys))) a))

;; Steps that don't change s2r
(property (sys0 sys1 :system)
  :h (v (system-sender-rcv sys0 sys1)
	(system-receiver-prc sys0 sys1)
	(system-r2s-tick sys0 sys1))
  (== (system-s2r sys0) (system-s2r sys1))
  :hints (("Goal" :in-theory (enable system-sender-rcv-definition-rule
				     system-receiver-prc-definition-rule
				     system-r2s-tick-definition-rule))))

;; Steps that don't change r2s
(property (sys0 sys1 :system pld :string)
  :h (v (system-receiver-rcv sys0 sys1)
	(system-sender-prc sys0 sys1 pld)
	(system-s2r-tick sys0 sys1))
  (== (system-r2s sys0) (system-r2s sys1))
  :hints (("Goal" :in-theory (enable system-receiver-rcv-definition-rule
				     system-sender-prc-definition-rule
				     system-s2r-tick-definition-rule))))

;; Theorem: In the global system, the set of rcvd acks is non-decreasing under the subset relation.
(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0))
	(system-sender-rcv sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-rcv-definition-rule))))

(property (a :pos sys0 sys1 :system pld :string)
  :h (^ (in a (system-receiver sys0)) (system-sender-prc sys0 sys1 pld))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-prc-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-sender-to sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-to-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-s2r-tick sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-s2r-tick-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-r2s-tick sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-r2s-tick-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-s2r-decay sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-s2r-decay-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-r2s-decay sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-r2s-decay-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-receiver-prc sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-receiver-prc-definition-rule))))

(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0)) (system-receiver-rcv sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-receiver-rcv-definition-rule))))

;; Now let's make an executable version so we can print traces.

(defdata evt (oneof 'snd_s 'snd_r 'rcv_s 'rcv_r 'decay_s 'decay_r 'tick_s 'tick_r 'drop_s 'drop_r 'timeout))

(defdata evt_sys (list evt system))

(defdata evt_syss (listof evt_sys))

(definecd add-system-sender-rcv-steps-if-appropriate (sys :system choice1 :nat options :evt_syss) :evt_syss
  :timeout 100
  (if (^ (consp (tbf-data (system-r2s sys)))
	 (>= (tbf-bkt (system-r2s sys))
	     (length (tdg-pld (nth (if (= choice1 0) choice1 (rem choice1 (len (tbf-data (system-r2s sys)))))
				(tbf-data (system-r2s sys)))))))
      (cons (list 'rcv_s (system-sender-rcv-step sys choice1))
	   options)
    options))

(definecd add-system-sender-snd-steps-if-appropriate (sys :system pld :string options :evt_syss) :evt_syss
  :timeout 100
  (if (< (sender-state-cur (system-sender sys))
	 (+ (sender-state-N (system-sender sys))
	    (sender-state-hiA (system-sender sys))))
      (cons (list 'snd_s (system-sender-prc-step sys pld))
	    options)
    options))

(definecd add-system-sender-to-step-if-appropriate (sys :system options :evt_syss) :evt_syss
  (if (= (sender-state-cur (system-sender sys))
	 (+ (sender-state-N (system-sender sys)) (sender-state-hiA (system-sender sys))))
      (cons (list 'timeout (system-sender-to-step sys)) options)
    options))

(definecd add-system-receiver-rcv-steps-if-appropriate (sys :system choice1 :nat options :evt_syss) :evt_syss
  :timeout 200
  (if (^ (consp (tbf-data (system-s2r sys)))
	 (>= (tbf-bkt (system-s2r sys))
	     (length (tdg-pld (nth (if (= choice1 0) choice1 (rem choice1 (len (tbf-data (system-s2r sys)))))
				(tbf-data (system-s2r sys)))))))
      (cons (list 'rcv_r (system-receiver-rcv-step sys choice1))
	    options)
    options))

(definecd simulation-step (sys :system choice1 choice2 :nat pld :string) :evt_sys
  (b* ((options nil) ;; Initialize list of options
       (options (add-system-sender-rcv-steps-if-appropriate sys choice1 options))
       (options (add-system-sender-snd-steps-if-appropriate sys pld options))
       (options (add-system-sender-to-step-if-appropriate sys options))
       (options (cons (list 'decay_r (system-r2s-decay-step sys)) options))
       (options (cons (list 'decay_s (system-s2r-decay-step sys)) options))
       (options (cons (list 'tick_r (system-r2s-tick-step sys)) options))
       (options (cons (list 'tick_s (system-s2r-tick-step sys)) options))
       (options (add-system-receiver-rcv-steps-if-appropriate sys choice1 options))
       (options (cons (list 'snd_r (system-receiver-prc-step sys "ACK"))
		      options))
       (choice (rem choice2 (len options))))
       (nth choice options)))
		    
(defdata choice (list nat nat string))
(defdata choices (listof choice))

(definecd get-choice1 (ch :choice) :nat (car ch))
(definecd get-choice2 (ch :choice) :nat (cadr ch))
(definecd get-pld (ch :choice) :string (caddr ch))

(definecd nxt-step-given-choice (sys :system ch :choice) :evt_sys
  (simulation-step sys
		   (get-choice1 ch)
		   (get-choice2 ch)
		   (get-pld ch)))

(definecd get-sys (evts :evt_sys) :system (cadr evts))

(definecd simulation-step* (sys :system chs :choices) :evt_syss
  (match chs
    (() nil)
    ((ch . rst)
     (cons (nxt-step-given-choice sys ch)
	   (simulation-step* (get-sys (nxt-step-given-choice sys ch)) rst)))))

;; Print a trace.  Commented out so that cert.pl works.
#|
(simulation-step* (nth-system 0) '((0 100 "banana")
				   (1 0 "hotdog")
				   (2 1 "mango")
				   (3 2 "emily")
				   (6 0 "avenue")
				   (2 13 "red-wine")
				   (88 22 "candle")
				   (18 3 "wax")
				   (11 9 "usa")
				   (0 0 "brazil")
				   (1 5 "waterbottle")
				   (2 2 "bumblebee")
				   (0 100 "banana")
				   (1 13 "methyl")
				   (2 14 "airpod")
				   (3 15 "chocolate")))
|#
