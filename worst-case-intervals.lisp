(in-package "ACL2S")

#|
This is prototype work analyzing the scenario where the sender-to-receiver direction
is not allowed to drain because the sender and receiver transmit too quickly.
In contrast to the other two performance proofs, we do not yet have a bisimulation
theorem for this one, hence it is not listed as an Observation in the document.

So we have: r_s <= d <= N
                <  r <  N

- Receiver receives (d/r_s) bursts before sending an ACK.
- The value of the ack is min(N \ rcvd)

burst 1      butst 2      butst 3      butst 4      butst 5
[     ||||||][     ||||||][     ||||||][     ||||||][     ||||||] = 1 window
      ack
      [     ||||||][     ||||||][     ||||||][     ||||||][     ||||||] = 1 window
                                                                ack

or

burst 1         butst 2         burst 3         butst 4         butst 5
[     |||||||||][     |||||||||][     |||||||||][     |||||||||][     |||||||||] = 1 window
      ack
      [     |||||||||][     |||||||||][     |||||||||][     |||||||||][     |||||||||] = 1 window
            ack
            [     |||||||||][     |||||||||][     |||||||||][     |||||||||][     |||||||||] = 1 window
                  ack
                  [     |||||||||][     |||||||||][     |||||||||][     |||||||||][     |||||||||] = 1 window
                                                                                        ack

Ansatz: It takes N/r bursts to transmit a window.
        After r/r_s acks (= r/r_s windows), the high ack increases by window + r 
        So # good packets = 1 window + r, and
           # dup packets = 3 windows
           # time = time(burst) * (N / r) * (r / r_s) + time(ack) * (r / r_s)
             where time(burst) includes tick, transmit, and deliver, and 
                   time(ack) includes tick, transmit, and deliver. 

        Then throughput = (4 windows + r)/#time,
             goodput    = (1 window + r)/#time, and
             efficiency = (1 window + r)/(4 windows + r)

       
|#

;; First let's prove a lemma over intervals.
(defdata interval (list nat nat))

(definecd valid-interval (i :interval) :bool
  (< (car i) (cadr i)))

(definecd extend-interval (i :interval p :pos) :interval
  (list (car i) (+ (cadr i) p)))

(definecd extend-interval* (i :interval p :pos N :nat) :interval
  (if (= N 0) i (extend-interval (extend-interval* i p (1- N)) p)))

(property simplify-extend-interval* (i :interval p :pos N :nat)
  (equal (extend-interval* i p N)
	 (if (posp N) (extend-interval i (* p N)) i))
  :hints (("Goal" :in-theory (enable extend-interval*-definition-rule
				     extend-interval-definition-rule))))

(defdata intervals (listof interval))

(definecd extend-intervals (is :intervals p :pos) :intervals
  (if (consp is)
      (cons (extend-interval (car is) p)
	    (extend-intervals (cdr is) p))
    nil))

(property extend-extend-intervals (is :intervals p0 p1 :pos)
  (equal (extend-intervals (extend-intervals is p0) p1)
	 (extend-intervals is (+ p0 p1)))
  :hints (("Goal" :in-theory (enable extend-intervals-definition-rule
				     extend-interval-definition-rule))))

(definecd extend-intervals* (is :intervals p :pos N :nat) :intervals
  (if (= N 0) is (extend-intervals (extend-intervals* is p (1- N)) p)))

#|
(extend-intervals* is p N)

= { assuming posp N }

(extend-intervals (extend-intervals* is p (1- N)) p)

= { by induction }

(extend-intervals (if (posp (1- N)) (extend-intervals is (* p (1- N))) is) p)

= { assuming N > 1 }

(extend-intervals (extend-intervals is (* p (1- N))) p)

= { by extend-extend-intervals }

(extend-intervals is (+ p (* p (1- N))))

=

(extend-intervals is (* N p))
|#

(definecd simplify-extend-intervals*-ind (is :intervals p :pos N :nat) :nat
  (if (= N 0) 0
    (1+ (simplify-extend-intervals*-ind is p (1- N)))))

(property simplify-extend-intervals* (is :intervals p :pos N :nat)
  (equal (extend-intervals* is p N)
	 (if (posp N) (extend-intervals is (* p N)) is))
  :hints (("Goal" :in-theory (enable extend-intervals-definition-rule
				     extend-intervals*-definition-rule)
	   :induct (simplify-extend-intervals*-ind is p N))))

(definecd gapped-intervals (is :intervals p :nat) :bool
  (match is
    (() t)
    ((i . rst) (^
		(< (car i) (cadr i))
		(if (consp rst)
		      (= (+ (cadr i) p) (car (car rst)))
		    t)
		(gapped-intervals rst p)))))

(property gap-closes (is :intervals p0 p1 :pos)
  :h (^ (<= p0 p1) (gapped-intervals is p1))
  (gapped-intervals (extend-intervals is p0) (- p1 p0))
  :hints (("Goal" :in-theory (enable extend-intervals-definition-rule
				     extend-interval-definition-rule
				     gapped-intervals-definition-rule))))

(property gap-closed (is :intervals p0 N :pos)
  :h (gapped-intervals is (* p0 N))
  (gapped-intervals (extend-intervals* is p0 N) 0)
  :hints (("Goal" :use ((:instance simplify-extend-intervals* (p p0))
			(:instance gap-closes (p0 (* p0 N)) (p1 (* p0 N)))))))

;; Now that I've proven how quickly the gaps close, I need to also show how much extra
;; stuff we get through in the process.  Since each time we make a move to close gaps
;; we shift r_s slots to the right (see above diagram ...)
(property destruct-interval (i :interval)
  (^ (natp (car i))
     (natp (cadr i))))

(property nth-is-interval (is :intervals j :nat)
  :h (< j (len is))
  (intervalp (nth j is)))

(definecd simplify-once-gaps-closed (is :intervals) :interval
  :ic (^ (consp is) (gapped-intervals is 0))
  (list (car (nth 0 is))
	(cadr (nth (1- (len is)) is)))
  :function-contract-hints
  (("Goal" :use ((:instance nth-is-interval (j 0))
		 (:instance nth-is-interval (j (1- (len is))))
		 (:instance destruct-interval (i (nth 0 is)))
		 (:instance destruct-interval (i (nth (1- (len is)) is))))))
  :body-contracts-hints
  (("Goal" :use ((:instance nth-is-interval (j 0))
		 (:instance nth-is-interval (j (1- (len is))))
		 (:instance destruct-interval (i (nth 0 is)))
		 (:instance destruct-interval (i (nth (1- (len is)) is)))))))

(in-theory (disable destruct-interval))

(property each-interval-was-incrd (is :intervals i :nat p :pos)
  :h (< i (len is))
  (equal (nth i (extend-intervals is p)) (extend-interval (nth i is) p))
  :hints (("Goal" :in-theory (enable extend-intervals-definition-rule))))

(property len-extend-intervals* (is :intervals p0 N :pos)
  (= (len (extend-intervals* is p0 N))
     (len is))
  :hints (("Goal" :in-theory (enable extend-intervals*-definition-rule
				     extend-intervals-definition-rule))))

(property each-interval-was-incrd* (is :intervals p0 N :pos i :nat)
  :h (^ (< i (len is)) (gapped-intervals is (* p0 N)))
  (equal (nth i (extend-intervals* is p0 N))
	 (extend-interval (nth i is) (* p0 N))))

(property cadr-interval-is-nat (i :interval)
  (natp (cadr i)))

(property destruct-extended-interval (i :interval p :pos)
  (^
   (natp (cadr i))
   (natp (cadr (extend-interval i p)))
   (= (cadr (extend-interval i p))
      (+ (cadr i) p)))
  :hints (("Goal" :in-theory (enable extend-interval-definition-rule)
	   :use ((:instance cadr-interval-is-nat)
		 (:instance cadr-interval-is-nat (i (extend-interval i p)))))))

(property destruct-ith-interval (is :intervals p0 N :pos i :nat)
  :h (^ (< i (len is)) (gapped-intervals is (* p0 N)))
  (^
   ;; for contract checking ...
   (intervalp (nth i is))
   (equal (nth i (extend-intervals* is p0 N))
	  (extend-interval (nth i is) (* p0 N)))
   (intervalsp (extend-intervals* is p0 N))
   (= (len (extend-intervals* is p0 N)) (len is))
   (< i (len (extend-intervals* is p0 N)))
   (intervalp (nth i (extend-intervals* is p0 N)))
   ;; the actual things I want to prove.
   (= (car (nth i (extend-intervals* is p0 N)))
      (car (nth i is)))
   (= (cadr (nth i (extend-intervals* is p0 N)))
      (+ (cadr (nth i is)) (* N p0))))
  :hints (("Goal" :in-theory (enable extend-interval-definition-rule)
	   :use ((:instance destruct-extended-interval
			    (p (extend-interval (nth i is) (* p0 N))))
		 (:instance len-extend-intervals*)
		 (:instance nth-is-interval (is (extend-intervals* is p0 N)) (j i))))))


(property witness-gap-closed-simplification-contracts
  (is :intervals p0 N :pos)
  :h (^ (consp is) (gapped-intervals is (* p0 N)))
  (^ ;; contracts stuff
   (= (len (extend-intervals* is p0 N)) (len is))
   (consp (extend-intervals* is p0 N))
   (gapped-intervals (extend-intervals* is p0 n) 0)
   (intervalp (nth 0 is))
   (intervalp (nth (1- (len is)) is))
   (intervalp (nth 0 (extend-intervals* is p0 n)))
   (intervalp (nth (1- (len is)) (extend-intervals* is p0 n)))
   (natp (car (nth 0 is)))
   (natp (cadr (nth (1- (len is)) (extend-intervals* is p0 n))))
   ;; the actual theorem I am interested in
   (equal (simplify-once-gaps-closed (extend-intervals* is p0 N)) 
	  (list (car (nth 0 is)) (+ (cadr (nth (1- (len is)) is)) (* p0 N))))) ;; [start, end + p0 N]
  :hints (("Goal" :use ((:instance len-extend-intervals*)
			(:instance gap-closed)
			(:instance nth-is-interval (j 0))
			(:instance nth-is-interval (j (1- (len is))))
			(:instance nth-is-interval
				   (is (extend-intervals* is p0 n)) (j 0))
			(:instance nth-is-interval
				   (is (extend-intervals* is p0 n))
				   (j (1- (len is))))
			(:instance destruct-ith-interval (i 0))
			(:instance destruct-ith-interval (i (1- (len is)))))
	   :in-theory (enable simplify-once-gaps-closed-definition-rule))))

