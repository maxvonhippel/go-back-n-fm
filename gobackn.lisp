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
(definec sender-rcv-ack (ss :sender-state ack :pos) :sender-state
  (if (<= ack (1+ (mget :hiP ss))) 
      (let* ((hiA (mget :hiA ss))
	     (hiA (max hiA ack))
	     (cur (mget :cur ss))
	     (cur (max cur hiA)))
	(mset :hiA hiA (mset :cur cur ss)))
    ss))

;; Transition when the sender transmits a PKT
(definec sender-snd-cur (ss :sender-state) :sender-state
  :ic (< (mget :cur ss) (+ (mget :N ss) (mget :hiA ss)))
  (let* ((cur (mget :cur ss))
	 (hiP (mget :hiP ss))
	 (hiP (max hiP cur))
	 (cur (1+ cur)))
    (mset :cur cur (mset :hiP hiP ss))))

;; Transition when the sender times out
(definec sender-timeout (ss :sender-state) :sender-state
  :ic (== (mget :cur ss) (+ (mget :N ss) (mget :hiA ss)))
  (mset :cur (mget :hiA ss) ss))

;; Transition relation
(definec sender-tran (ss0 ss1 :sender-state) :bool
  (or (if (<= (mget :hiA ss1) (1+ (mget :hiP ss0)))
	  (== (sender-rcv-ack ss0 (mget :hiA ss1)) ss1) nil)
      (if (< (mget :cur ss0) (+ (mget :N ss0) (mget :hiA ss0)))
	  (== (sender-snd-cur ss0) ss1) nil)
      (if (== (mget :cur ss0) (+ (mget :N ss0) (mget :hiA ss0)))
	  (== (sender-timeout ss0) ss1) nil)))

;; Invariant: HiA <= HiP + 1
(property (ss0 ss1 :sender-state)
  :h (^ (sender-tran ss0 ss1)
	(<= (mget :hiA ss0) (1+ (mget :hiP ss0))))
  (<= (mget :hiA ss1) (1+ (mget :hiP ss1))))

;; Invariant: HiA ≤ CurP ≤ HiA + N
(property (ss0 ss1 :sender-state)
  :h (^ (sender-tran ss0 ss1)
	(<= (mget :hiA ss0) (mget :cur ss0))
	(<= (mget :cur ss0) (+ (mget :hiA ss0) (mget :N ss0))))
  (^ (<= (mget :hiA ss1) (mget :cur ss1))
     (<= (mget :cur ss1) (+ (mget :hiA ss1) (mget :N ss1)))))

;; Invariant: N is constant
;; Invariant: HiA and HiP are non-decreasing
(property (ss0 ss1 :sender-state)
  :h (sender-tran ss0 ss1)
  (^ (== (mget :N ss0) (mget :N ss1))
     (<= (mget :hiA ss0) (mget :hiA ss1))
     (<= (mget :hiP ss0) (mget :hiP ss1))))

#|
Below is a model & theory of a receiver
|#

;; Helper function to check if a list `ps` contains every integer
;; i in the range [1, p].
(definecd has-all (p :pos ps :poss) :bool
  (^ (in p ps) (if (< 1 p) (has-all (1- p ) ps) t)))

;; Proof that the helper function indeed does what it is supposed to do.
(property has-all-down (p0 p1 :pos ps :poss)
  :h (^ (has-all p1 ps) (< p0 p1))
  (has-all p0 ps)
  :hints (("Goal" :in-theory
	   (enable has-all has-all-definition-rule))))

;; Recognizer for a cumulative ACK, based on has-all.
(definecd cumackp (a :pos ps :poss) :bool
  (^ (! (in a ps)) (if (< 1 a) (has-all (1- a) ps) t)))

;; Lemma: If a0 is a cum ACK, and a0 < a1, then a1 is NOT a cum ACK.
(property cumackp-!-up (a0 a1 :pos ps :poss)
  :h (^ (cumackp a0 ps) (< a0 a1))
  (! (cumackp a1 ps))
  :instructions ((:use (:instance cumackp-definition-rule (a a0)))
		 (:use (:instance cumackp-definition-rule (a a1)))
		 (:use (:instance has-all-down (p0 a0) (p1 (1- a1))))
		 (:use (:instance has-all-definition-rule (p a0)))
                 :pro
		 (:claim (=> (cumackp a1 ps) (has-all (1- a1) ps)))
		 (:casesplit (< a0 (1- a1)))
                 (:claim (^ (posp a0)
			    (posp (1- a1))
			    (pos-listp ps)
			    (< a0 (1- a1))))
                 (:claim (=> (cumackp a1 ps) (has-all a0 ps)))
                 :prove
                 (:claim (=> (cumackp a1 ps) (has-all a0 ps)))
                 :prove))

;; Thm: the cumulative ack is unique
(property (a0 a1 :pos ps :poss)
  :h (^ (cumackp a0 ps) (cumackp a1 ps))
  (== a0 a1)
  :hints (("Goal" :cases ((<= a0 a1) (<= a1 a0)))))

;; Next, let's define a global state.
(defdata system
  (record (sender . sender-state)
	  (receiver . poss)
	  (s2r . tbf)
	  (r2s . tbf)))

(definecd nth-val-helper (dgs0 dgs1 :dgs) :dg
  :ic (== (1+ (len dgs1)) (len dgs0))
  (nth (witness-i dgs0 dgs1) dgs0))

(definecd nth-val-helper-lift (sys0 sys1 :system) :pos
  :ic (== (1+ (len (mget :D (mget :r2s sys1)))) (len (mget :D (mget :r2s sys0))))
  (mget :val (nth-val-helper (mget :D (mget :r2s sys0))
			     (mget :D (mget :r2s sys1)))))

(definecd or-cases-system-sender-dlv (sys0 sys1 :system) :bool
  :ic (^ (== (1+ (len (mget :D (mget :r2s sys1)))) (len (mget :D (mget :r2s sys0))))
	 (posp (mget :b (mget :r2s sys0))))
  (or (== (mget :sender sys1)
	  (sender-rcv-ack (mget :sender sys0)
			  (nth-val-helper-lift sys0 sys1)))
      (== (mget :sender sys1) (mget :sender sys0))))

;; Allow dropping at dlv step as well ...
(definecd system-sender-dlv (sys0 sys1 :system) :bool
  (^
   (== (1+ (len (mget :D (mget :r2s sys1)))) (len (mget :D (mget :r2s sys0))))
   (posp (mget :b (mget :r2s sys0)))
   (== (mget :r2s sys1)
       (tbf-dlv (mget :r2s sys0)
		(witness-i (mget :D (mget :r2s sys0))
			   (mget :D (mget :r2s sys1)))))
   (or (== (mget :sender sys1)
	   (sender-rcv-ack (mget :sender sys0)
			   (nth-val-helper-lift sys0 sys1)))
       (== (mget :sender sys1) (mget :sender sys0))) ;; if drop at dlv step ...
   (== (mget :receiver sys0) (mget :receiver sys1))
   (== (mget :s2r sys0) (mget :s2r sys1))))

(definecd system-sender-trn (sys0 sys1 :system) :bool
  (^
   (< (mget :cur (mget :sender sys0))
      (+ (mget :N (mget :sender sys0))
	 (mget :hiA (mget :sender sys0))))
   (== (sender-snd-cur (mget :sender sys0))
       (mget :sender sys1))
   (or ;; handle dropping case as well ...
    (== (mget :s2r sys1)
	(tbf-trn (mget :s2r sys1)
		 (mget :cur (mget :sender sys0))
		 t))
    (== (mget :s2r sys1)
	(tbf-trn (mget :s2r sys1)
		 (mget :cur (mget :sender sys0))
		 nil)))
   (== (mget :r2s sys0) (mget :r2s sys1))
   (== (mget :receiver sys0) (mget :receiver sys1))))

(definecd system-sender-to (sys0 sys1 :system) :bool
  (^ (== (mget :cur (mget :sender sys0))
	 (+ (mget :N (mget :sender sys0)) (mget :hiA (mget :sender sys0))))
     (== (mget :sender sys1) (sender-timeout (mget :sender sys0)))
     (== (mget :receiver sys0) (mget :receiver sys1))
     (== (mget :s2r sys0) (mget :s2r sys1))
     (== (mget :r2s sys0) (mget :r2s sys1))))

(definecd system-r2s-tick (sys0 sys1 :system) :bool
  (^ (== (token-decay (tbf-tick (mget :r2s sys0))) (mget :r2s sys1))
      (== (mget :s2r sys0) (mget :s2r sys1))
      (== (mget :sender sys0) (mget :sender sys1))
      (== (mget :receiver sys0) (mget :receiver sys1))))

(definecd system-s2r-tick (sys0 sys1 :system) :bool
  (^ (== (token-decay (tbf-tick (mget :s2r sys0))) (mget :s2r sys1))
      (== (mget :r2s sys0) (mget :r2s sys1))
      (== (mget :sender sys0) (mget :sender sys1))
      (== (mget :receiver sys0) (mget :receiver sys1))))

(definecd system-receiver-dlv (sys0 sys1 :system) :bool
  (^ (== (1+ (len (mget :D (mget :s2r sys1))))
	 (mget :D (mget :s2r sys0)))
     ;; first case in the or handles 2 cases at once:
     ;; (a) the delivered message is already in the list, or
     ;; (b) the delivered message is lost at the delivery step ...
     (or (== (mget :receiver sys0) (mget :receiver sys1))
	 (^ (! (in (mget :val (nth (witness-i (mget :D (mget :s2r sys0))
					      (mget :D (mget :s2r sys1)))
				   (mget :D (mget :s2r sys0))))
		   (mget :receiver sys0)))
	    (== (mget :receiver sys0)
		(cons (mget :val (nth (witness-i (mget :D (mget :s2r sys0))
						 (mget :D (mget :s2r sys1)))
				      (mget :D (mget :s2r sys0))))
		      (mget :receiver sys1)))))
     (== (mget :r2s sys0) (mget :r2s sys1))
     (== (mget :sender sys0) (mget :sender sys1))))

;; Thm: the set of acks the receiver keeps track of is non-decreasing according to the
;; subset relation over time.
(property system-receiver-dlv-doesnt-decrease-acks (a :pos sys0 sys1 :system)
  :h (^ (system-receiver-dlv sys0 sys1)
	(in a (mget :receiver sys0)))
  (in a (mget :receiver sys1))
  :hints (("Goal" :in-theory (enable system-receiver-dlv-definition-rule))))

(definecd system-receiver-trn-cumack-helper (sys0 sys1 :system) :bool
  :ic (== (len (mget :D (mget :r2s sys0)))
	  (1+ (len (mget :D (mget :r2s sys1)))))
  (cumackp (nth-val-helper-lift sys0 sys1)
	   (mget :receiver sys0)))
  
(definecd system-receiver-trn (sys0 sys1 :system) :bool
  (^ (== (mget :s2r sys0) (mget :s2r sys1))
     (== (mget :receiver sys0) (mget :receiver sys1))
     (== (mget :sender sys0) (mget :sender sys1))
     ;; drop, more convenient than computing and then ignoring next ack
     (or (== (mget :r2s sys0) (mget :r2s sys1))
	 ;; successful transmission ...
	 (^ (== (len (mget :D (mget :r2s sys0)))
		(1+ (len (mget :D (mget :r2s sys1)))))
	    ;; ... of a cumulative ack ...
	    (system-receiver-trn-cumack-helper sys0 sys1)
	    (== (mget :r2s sys1)
		(tbf-trn (mget :r2s sys0)
			 (nth-val-helper-lift sys0 sys1)
			 nil))))))	    

;; And a global state transition.
(definecd system-tranr (sys0 sys1 :system) :bool
  (or
   ;; Transition when the sender receives an ACK
   (system-sender-dlv sys0 sys1)
   ;; Transition when the sender transmits a PKT
   (system-sender-trn sys0 sys1)
   ;; Transition when the sender times out
   (system-sender-to sys0 sys1)
   ;; Transition when one of the tbfs ticks
   (system-s2r-tick sys0 sys1)
   (system-r2s-tick sys0 sys1)
   ;; Transition when the receiver receives a new pkt
   (system-receiver-dlv sys0 sys1)
   ;; Transition when the receiver transmits a new ack
   (system-receiver-trn sys0 sys1)))

(property only-system-receiver-dlv-changes-acks (sys0 sys1 :system)
  :h (or (system-sender-dlv sys0 sys1)
	 (system-sender-trn sys0 sys1)
	 (system-sender-to sys0 sys1)
	 (system-s2r-tick sys0 sys1)
	 (system-r2s-tick sys0 sys1)
	 (system-receiver-trn sys0 sys1))
  (== (mget :receiver sys0) (mget :receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-dlv-definition-rule
				     system-sender-trn-definition-rule
				     system-sender-to-definition-rule
				     system-s2r-tick-definition-rule
				     system-r2s-tick-definition-rule
				     system-receiver-trn-definition-rule))))

(in-theory (disable only-system-receiver-dlv-changes-acks
		    system-receiver-dlv-doesnt-decrease-acks))

(definecd max-dg-val (dgs :dgs) :pos
  :ic (consp dgs)
  (if (consp (cdr dgs))
      (max (mget :val (car dgs))
	   (max-dg-val (cdr dgs)))
    (mget :val (car dgs))))

(definecd min-dg-val (dgs :dgs) :pos
  :ic (consp dgs)
  (if (consp (cdr dgs))
      (min (mget :val (car dgs))
	   (min-dg-val (cdr dgs)))
    (mget :val (car dgs))))

(definecd get-vals (dgs :dgs) :poss
  (match dgs
    (() ())
    ((dg . rst) (cons (mget :val dg) (get-vals rst)))))

(definecd max-ack<=cur-ack (sys :system a :pos) :bool
  :ic (^ (consp (mget :D (mget :r2s sys)))
	 (cumackp a (get-vals (mget :D (mget :r2s sys)))))
  (<= (max-dg-val (mget :D (mget :r2s sys))) a))

(property steps-that-dont-change-s2r (sys0 sys1 :system)
  :h (or (system-sender-dlv sys0 sys1)
	 (system-receiver-trn sys0 sys1)
	 (system-r2s-tick sys0 sys1))
  (== (mget :s2r sys0) (mget :s2r sys1))
  :hints (("Goal" :in-theory (enable system-sender-dlv-definition-rule
				     system-receiver-trn-definition-rule
				     system-r2s-tick-definition-rule))))

(property steps-that-dont-change-r2s (sys0 sys1 :system)
  :h (or (system-receiver-dlv sys0 sys1)
	 (system-sender-trn sys0 sys1)
	 (system-s2r-tick sys0 sys1))
  (== (mget :r2s sys0) (mget :r2s sys1))
  :hints (("Goal" :in-theory (enable system-receiver-dlv-definition-rule
				     system-sender-trn-definition-rule
				     system-s2r-tick-definition-rule))))
				     
(in-theory (disable steps-that-dont-change-s2r
		    steps-that-dont-change-r2s))

;; Theorem: In the global system, the set of rcvd acks is non-decreasing under the subset relation.
(property receiver-acks-nondecreasing (a :pos sys0 sys1 :system)
  :h (^ (in a (mget :receiver sys0))
	(system-tranr sys0 sys1))
  (in a (mget :receiver sys1))
  :hints (("Goal" :in-theory (enable only-system-receiver-dlv-changes-acks
				     system-receiver-dlv-doesnt-decrease-acks
				     system-tranr-definition-rule))))

