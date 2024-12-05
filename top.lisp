(in-package "ACL2S")
(include-book "tbf")
(include-book "tbf-composition")
(include-book "gobackn")
(include-book "performance-models")
(include-book "performance")
(include-book "performance-results-1")
(include-book "performance-results-2")
(include-book "performance-results-3")
(include-book "performance-results-4")
(include-book "performance-results-5")
(include-book "performance-results-6")

;; A datagram consists of a nat id and a string payload.  Usually, we associate
;; a datagram with some maximal delay, indicating how much longer it is allowed to
;; remain in-transit before it must be lost.  This delay is an ordinal, which means
;; it could be either finite or infinite.  We refer to the combination of a datagram
;; and its maximum delay as a "timed datagram", or tdg.
(defdata tdg (record (id . pos) (del . nat-ord) (pld . string)))

;; The sender's state consists of four variables: N (the constant window size),
;; hiA (the highest ack rcvd so far, or 1 if none were rcvd), hiP (the highest pkt sent
;; so far), and cur (the next pkt to send).
(defdata sender-state
  (record (N . pos) ;; window size
	  (hiA . pos) ;; high ack
	  (hiP . pos) ;; high pkt
	  (cur . pos))) ;; next transmission

(encapsulate ()
;; Note how we define initial-ss to range over all choices of N.  Note also how hiP=1 and
;; hiA=cur=1, as we assume the sender-state is not really initialized until something was sent.
(local (defconst *initial-ss-10* (sender-state 10 1 1 2)))
(local (definecd initial-ss (N :pos) :sender-state (mset :N N *initial-ss-10*)))
	     
(local (in-theory (enable sender-tranr-definition-rule
			  sender-rcv-ack-definition-rule
			  sender-adv-cur-definition-rule
			  sender-timeout-definition-rule
			  initial-ss-definition-rule)))

;; Invariant: HiA ≤ HiP + 1
(property (N :pos)
  (<= (sender-state-hiA (initial-ss N)) (1+ (sender-state-hiP (initial-ss N)))))
(property (ss0 ss1 :sender-state)
  :h (^ (sender-tranr ss0 ss1) (<= (sender-state-hiA ss0) (1+ (sender-state-hiP ss0))))
  (<= (sender-state-hiA ss1) (1+ (sender-state-hiP ss1))))

;; Invariant: HiA ≤ CurP ≤ HiA + N
(property (N :pos)
  (^ (<= (sender-state-hiA (initial-ss N)) (sender-state-cur (initial-ss N)))
     (<= (sender-state-cur (initial-ss N)) (+ (sender-state-hiA (initial-ss N))
					      (sender-state-N (initial-ss N))))))
(property (ss0 ss1 :sender-state)
  :h (^ (sender-tranr ss0 ss1)
	(<= (sender-state-hiA ss0) (sender-state-cur ss0))
	(<= (sender-state-cur ss0) (+ (sender-state-hiA ss0) (sender-state-N ss0))))
  (^ (<= (sender-state-hiA ss1) (sender-state-cur ss1))
     (<= (sender-state-cur ss1) (+ (sender-state-hiA ss1) (sender-state-N ss1)))))

;; Invariant: N is constant, and HiA and HiP are non-decreasing
(property (ss0 ss1 :sender-state)
  :h (sender-tranr ss0 ss1)
  (^ (= (sender-state-N ss0) (sender-state-N ss1))
     (<= (sender-state-hiA ss0) (sender-state-hiA ss1))
     (<= (sender-state-hiP ss0) (sender-state-hiP ss1)))))

;; The sender transmits into a TBF called s2r, which then forwards packets on to the
;; receiver.  Likewise, the receiver transmits into a TBF called r2s, which then forwards
;; acks on to the sender.
(defdata tbf
  (record (b-cap . pos) ;; bucket capacity (how large can bkt be?)
	  (d-cap . pos) ;; link capacity (how many bytes can be in data?)
	  (bkt . nat) ;; bucket, which must always be <= b-cap
	  (rat . pos) ;; rate at which the bucket refills
	  (del . nat-ord) ;; maximum delay of a datagram in data
	  (data . tdgs))) ;; data in-transit, must satisfy sz(data) <= d-cap

;; All the TBF's actions are defined in TBF.lisp, but I just want to note that we proved
;; than the TBF cannot forward more bytes than it has tokens to spend in its bkt, as we
;; proved using the contracts here.
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
	 :data (remove-ith (tbf-data tbf) i)))

;; The other important thing we show is that the serial composition of two TBFs
;; can be simulated by a single TBF with nondeterministic loss.
(defdata two-tbf (list tbf tbf))

(defthm transmission-rule
  (=> (^ (two-tbfp ttbf)
         (posp p)
         (stringp pld)
         (<= (+ (sz (tbf-data (car ttbf))) (length pld))
             (tbf-d-cap (car ttbf)))
         (<= (sz (tbf-data (cadr ttbf)))
             (tbf-d-cap (cadr ttbf))))
      (~= ([+] (list (tbf-prc (car ttbf) p pld)
                     (cadr ttbf)))
          (tbf-prc ([+] ttbf) p pld))))

(definecd t1-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (~= ([+] (list (tbf-fwd (car ttbf) i) (cadr ttbf)))
      (tbf-fwd ([+] ttbf) i)))

(property (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (t1-dlv-witness ttbf i))

(definecd t2-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (cadr ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	     (tbf-bkt (cadr ttbf))))
  (~= ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i)))
      (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i))))

(property (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (cadr ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	    (tbf-bkt (cadr ttbf))))
  (t2-dlv-witness ttbf i)
  :hints (("Goal" :in-theory (enable t2-dlv-witness-definition-rule
				     ~=-definition-rule)
	   :use ((:instance t2-dlv-witness-helper-1)
		 (:instance t2-dlv-witness-helper-2)
		 (:instance [+]-dlv-2-body-contracts)))))

(property mv-is-a-permutation (ps0 ps1 :tl i :nat p :all)
  :h (< i (len ps0))
  (= (count p (append (remove-ith ps0 i)
		      (cons (nth i ps0) ps1)))
     (count p (append ps0 ps1))))

(definecd mv-lem-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (~=/mvd-i ttbf (mv-ttbf ttbf i) i))

(property mv-theorem (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (mv-lem-witness ttbf i))

(property tick-t1 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (~= ([+] ttbf) ([+] (list (tbf-tick (car ttbf)) (cadr ttbf)))))

(property tick-t2 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (~= ([+] ttbf) ([+] (list (car ttbf) (tbf-tick (cadr ttbf))))))

;; Now, let's turn our attention to the receiver.  We define the receiver as a list of positive
;; integers (a poss).  Then given such a list we can determine if an ack value would be
;; cumulative for it as follows.
(definecd cumackp (a :pos ps :poss) :bool
  (^ (! (in a ps)) (v (= 1 a) (has-all (1- a) ps))))

;; Note that the cumack is unique.
(propertyd cumack-is-unique (a0 a1 :pos ps :poss)
  :h (^ (cumackp a0 ps) (cumackp a1 ps))
  (== (= a0 a1) t))

;; Given a receiver "rcvd" we can easily compute which ack it would send next by taking
;; 1+ (maxl rcvd) where maxl is defined below.
(definecd maxl (ps :poss) :nat
  (match ps
    (() 0)
    ((p . rst) (max p (maxl rst)))))

;; Next, let's define the system, consisting of sender, receiver, and two TBFs.
(defdata system
  (record (sender . sender-state)
	  (receiver . poss)
	  (s2r . tbf)
	  (r2s . tbf)))

;; Note that the receiver set is non-decreasing with the subset relation over time.
(property (a :pos sys0 sys1 :system)
  :h (^ (in a (system-receiver sys0))
	(system-sender-rcv sys0 sys1))
  (in a (system-receiver sys1))
  :hints (("Goal" :in-theory (enable system-sender-rcv-definition-rule))))

#|
A cool attribute of our model is that it is executable.  Here's an example run.
(Just paste this into the repl and it will print out the actual run ...)

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

;; Now let's go ahead and talk about performance.  We can say a couple of interesting
;; things.  For this analysis, we are going to define a "simplified model", which we will
;; prove to be equivalent under certain assumptions.
(defdata simplified-model
  (record (chan . poss)
	  (d-cap . nat) ;; bcap = bkt = rat
	  (ack . pos)
	  (cur . pos)
	  (hiA . pos)
	  (N . pos)))

(definecd simplify (sys :system) :simplified-model
  (simplified-model (tdgs->poss (tbf-data (system-s2r sys)))
		    (tbf-d-cap (system-s2r sys))
		    (1+ (maxl (system-receiver sys))) ;; out of order pkts ignored
		    (sender-state-cur (system-sender sys))
		    (sender-state-hiA (system-sender sys))
		    (sender-state-N (system-sender sys))))


;; In a single step of the real system, sender sends R packets, s2r ticks, then s2r delivers
;; bkt packets (each has sz 1).
(definecd single-step (sys :system R b :pos) :system
  :ic (^ (<= (+ (sender-state-cur (system-sender sys)) R)
	     (+ (sender-state-hia (system-sender sys))
		(sender-state-n (system-sender sys))))
	 (all-inf (tbf-data (system-s2r sys)))
	 (all-1 (tbf-data (system-s2r sys)))
	 (not (natp (tbf-del (system-s2r sys))))
	 (<= b (min R (tbf-d-cap (system-s2r sys))))
	 (= b (tbf-b-cap (system-s2r sys)))
	 (= b (tbf-rat (system-s2r sys)))
	 (<= (tbf-bkt (system-s2r sys))
	     (tbf-b-cap (system-s2r sys)))
	 (<= (tbf-b-cap (system-s2r sys))
	     (tbf-d-cap (system-s2r sys)))
	 (<= (len (tbf-data (system-s2r sys)))
	     (tbf-d-cap (system-s2r sys))))
  (dlv-b (system-s2r-tick-step (snd-R sys R)) b))

;; Many-steps just does a fixed number of consecutive single-steps.
(definecd many-steps (sys :system R b steps :pos) :system
  :ic (^ (<= (+ (sender-state-cur (system-sender sys)) (* R steps))
	     (+ (sender-state-hiA (system-sender sys))
		(sender-state-N (system-sender sys))))
	 (all-inf (tbf-data (system-s2r sys)))
	 (all-1 (tbf-data (system-s2r sys)))
	 (! (natp (tbf-del (system-s2r sys))))
	 (<= b (min R (tbf-d-cap (system-s2r sys))))
	 (= b (tbf-b-cap (system-s2r sys)))
	 (= b (tbf-rat (system-s2r sys)))
	 (<= (tbf-bkt (system-s2r sys))
	     (tbf-b-cap (system-s2r sys)))
	 (<= (tbf-b-cap (system-s2r sys))
	     (tbf-d-cap (system-s2r sys)))
	 (<= (len (tbf-data (system-s2r sys)))
	     (tbf-d-cap (system-s2r sys)))
	 (receiver-is-valid sys))
  (if (= steps 1)
      (single-step sys R b)
    (many-steps (single-step sys R b) R b (1- steps))))

;; Thm: Many steps of the simplified model are equivalent to many steps of the real one.
(encapsulate () (local (in-theory (enable tdgs->poss-preserves-len simplify-definition-rule)))
(propertyd many-steps-moves-thru-simplification (sys :system R b steps :pos)
	   :h (^ (<= (+ (sender-state-cur (system-sender sys))
			(* r steps))
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys))))
		 (all-inf (tbf-data (system-s2r sys)))
		 (all-1 (tbf-data (system-s2r sys)))
		 (! (natp (tbf-del (system-s2r sys))))
		 (<= b (min r (tbf-d-cap (system-s2r sys))))
		 (= b (tbf-b-cap (system-s2r sys)))
		 (= b (tbf-rat (system-s2r sys)))
		 (<= (tbf-bkt (system-s2r sys))
		     (tbf-b-cap (system-s2r sys)))
		 (<= (tbf-b-cap (system-s2r sys))
		     (tbf-d-cap (system-s2r sys)))
		 (<= (len (tbf-data (system-s2r sys)))
		     (tbf-d-cap (system-s2r sys)))
		 (receiver-is-valid sys))
	   (== (simplify (many-steps sys r b steps))
	       (many-steps-simplified (simplify sys)
				      r b steps))))

;; How many steps does it take until the channel is R packets away from being full?
(definecd steps-to-fill (R b d-cap :pos) :pos
  :ic (^ (< b R) ;; overtransmission
	 (< R d-cap)
	 (natp (/ (- d-cap R) (- R b)))) ;; (R - b) needs to divide (dcap - R)
  (/ (- d-cap R) (- R b)))

;; Thm: After "steps" many (dlv-b (tick (snd-R ...)))'s, ack has increased
;; by steps * b, and the channel contains the next (R - b) * steps ack values.
;; Let warmup be such that (R - b) * warmup + R = d-cap.
;; In other words, warmup = (d-cap - R) / (R - b).
;; Then after warmup + 2 steps:
;;     ack has increased by b(warmup + 2)
;;     chan contains the next (d-cap - b) values (top-dn)
;; which means eventually
;;     ack increases by b(warmup + 2) + (d-cap - b)
;;                      = b(warmup) + b + d-cap
;;                      = b(warmup) + b + (R - b) * warmup + R
;;                      = R(warmup) + R + b
;;                      = R (d-cap - R) / (R - b) + R + b
(propertyd time-to-fill-and-conditions-once-[nearly]-full (sm :simplified-model R b steps :pos)
	   :h (^ (< b r)
		 (< r (simplified-model-d-cap sm))
		 (<= (len (simplified-model-chan sm))
		     (simplified-model-d-cap sm))
		 (natp (/ (- (simplified-model-d-cap sm) r)
			  (- r b)))
		 (<= (+ (simplified-model-cur sm)
			(* r
			   (steps-to-fill r b (simplified-model-d-cap sm))))
		     (+ (simplified-model-hia sm)
			(simplified-model-n sm)))
		 (endp (simplified-model-chan sm))
		 (<= steps
		     (steps-to-fill r b (simplified-model-d-cap sm)))
		 ;; Suppose that an ack was just sent and, immediately afterword, received.
		 ;; Therefore, cur = ack.
		 (= (simplified-model-cur sm)
		    (simplified-model-ack sm)))
	   (^ (== (simplified-model-chan (many-steps-simplified sm r b steps))
		  (top-dn (+ (simplified-model-cur sm)
			     (* r steps)
			     -1)
			  (* (- r b) steps)))
	      (= (simplified-model-ack (many-steps-simplified sm r b steps))
		 (+ (* b steps)
		    (simplified-model-ack sm)))
	      (= (simplified-model-cur (many-steps-simplified sm r b steps))
		 (+ (* r steps)
		    (simplified-model-cur sm)))))

;; Thm: After steps-to-fill consecutive steps, there are precisely R packets of space remaining
;; in the channel, and the channel is consecutive in nature.  Moreover, the next packet the
;; sender plans to send is also consecutive relative to the contents of the channel.
(propertyd time-to-fill-and-conditions-once-[nearly]-full-penultimate-step
	   (sm :simplified-model R b :pos)
	   :h (^ (< b R)
		 (< R (simplified-model-d-cap sm))
		 (endp (simplified-model-chan sm))
		 (natp (/ (- (simplified-model-d-cap sm) R) (- R b)))
		 (<= (+ (simplified-model-cur sm)
			(* R (steps-to-fill R b (simplified-model-d-cap sm))))
		     (+ (simplified-model-hia sm) (simplified-model-n sm)))
		 ;; Suppose that an ack was just sent and, immediately afterword, received.
		 ;; Therefore, cur = ack.
		 (= (simplified-model-cur sm) (simplified-model-ack sm)))
	   (let* ((warmup-period (steps-to-fill R b (simplified-model-d-cap sm)))
		  (many-steps-later (many-steps-simplified sm R b warmup-period)))
	     (^ (== (simplified-model-chan many-steps-later)
		    (top-dn (+ (simplified-model-cur sm) (* R warmup-period) -1)
			    (* (- R b) warmup-period)))
		(= (simplified-model-ack many-steps-later)
		   (+ (* b warmup-period)
		      (simplified-model-ack sm)))
		(= (simplified-model-cur many-steps-later)
		   (+ (* R warmup-period) (simplified-model-cur sm)))))
	   :hints
	   (("Goal" :use (:instance time-to-fill-and-conditions-once-[nearly]-full
				    (steps (steps-to-fill R b (simplified-model-d-cap sm)))))))


;; So, we know how long it takes to fill.
;; In the next step, where it bcomes full, the sender's cur increases by R, the receiver's
;; ack increases by b, and the channel grows to be b less than full.
(defthm overtransmission-filling
  (=>
   (^ (simplified-modelp sm)
      (posp r)
      (posp b)
      (< b r)
      ;; :h (...)
      (<= r (simplified-model-d-cap sm))
      (<= (+ (len (simplified-model-chan sm)) r)
	  (simplified-model-d-cap sm))
      (<= (+ (simplified-model-cur sm) r)
	  (+ (simplified-model-hia sm)
	     (simplified-model-n sm)))
      (== (simplified-model-chan sm)
	  (if (! (endp (simplified-model-chan sm)))
	      (top-dn (+ (1- (len (simplified-model-chan sm)))
			 (simplified-model-ack sm))
		      (len (simplified-model-chan sm)))
	    nil))
      (= (simplified-model-cur sm)
	 (+ (len (simplified-model-chan sm))
	    (simplified-model-ack sm))))
   (^
    ;; The input contracts to the next call to this theorem are satisfied.
    (==
     (simplified-model-chan (single-step-simplified sm r b))
     (top-dn
      (+ (1- (len (simplified-model-chan (single-step-simplified sm r b))))
	 (simplified-model-ack (single-step-simplified sm r b)))
      (len (simplified-model-chan (single-step-simplified sm r b)))))
    ;; We can totally characterize the contents of the channel as being top-dn.
    (== (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r)
						 b))
	(top-dn (+ -1 r (simplified-model-cur sm))
		(+ (len (simplified-model-chan sm))
		   r (- b))))
    ;; The sender's cur incremented by R.
    (= (simplified-model-cur (single-step-simplified sm r b))
       (+ (len (simplified-model-chan (single-step-simplified sm r b)))
	  (simplified-model-ack (single-step-simplified sm r b))))
    ;; The receiver's ack incremented by b.  (note, R > b -- epistemic dilemna)
    (= (simplified-model-ack (single-step-simplified sm r b))
       (+ b (simplified-model-ack sm))))))

;; And in the final step, when it overflows, losses occur.  Since cur only increases
;; until a timeout, this means that all subsequent packets sent are wasted.
(defthm overtransmission-overfilling
  (=> (^ (simplified-modelp sm)
	 (posp r)
	 (posp b)
	 (< b r)
	 (<= r (simplified-model-d-cap sm))
	 (< (len (simplified-model-chan sm))
	    (simplified-model-d-cap sm))
	 (< 1 (simplified-model-cur sm))
	 (> (+ (len (simplified-model-chan sm)) r)
	    (simplified-model-d-cap sm))
	 (<= (+ (simplified-model-cur sm) r)
	     (+ (simplified-model-hia sm)
		(simplified-model-n sm)))
	 (== (simplified-model-chan sm)
	     (if (! (endp (simplified-model-chan sm)))
		 (top-dn (+ (1- (len (simplified-model-chan sm)))
			    (simplified-model-ack sm))
			 (len (simplified-model-chan sm)))
	       nil))
	 (= (simplified-model-cur sm)
	    (+ (len (simplified-model-chan sm))
	       (simplified-model-ack sm))))
      (^
       ;; The channel is still in top-dn form, however ...
       (== (simplified-model-chan (single-step-simplified sm r b))
	   (top-dn (+ -1
		      (- (simplified-model-d-cap sm)
			 (len (simplified-model-chan sm)))
		      (simplified-model-cur sm))
		   (- (simplified-model-d-cap sm) b)))
       (= (simplified-model-cur (single-step-simplified sm r b))
	  (+ r (simplified-model-cur sm)))
       (= (simplified-model-ack (single-step-simplified sm r b))
	  (+ b (simplified-model-ack sm)))
       (< (+ (- (simplified-model-d-cap sm)
		(len (simplified-model-chan sm)))
	     (simplified-model-cur sm))
	  (simplified-model-cur (single-step-simplified sm r b)))
       ;; it no longer matches with cur.  Indeed, cur is now far beyond the top
       ;; of the channel.  So losses happened.
       (! (in (+ (- (simplified-model-d-cap sm)
		    (len (simplified-model-chan sm)))
		 (simplified-model-cur sm))
	      (simplified-model-chan (single-step-simplified sm r b))))
       (< (car (simplified-model-chan (single-step-simplified sm r b)))
	  (+ (- (simplified-model-d-cap sm)
		(len (simplified-model-chan sm)))
	     (simplified-model-cur sm))))))
