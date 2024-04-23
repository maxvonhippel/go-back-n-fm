(in-package "ACL2S")
(include-book "tbf")
(include-book "gobackn")

#|
Theory of a perfect receiver.
|#
(definecd first-N (bot top :pos) :poss
  :ic (<= bot top)
  (if (equal bot top) (list top) (cons bot (first-N (1+ bot) top))))
  
(check= (first-N 1 4) '(1 2 3 4))
(check= (first-N 1 1) '(1))

(property first-N-last=N (bot top :pos)
  :h (<= bot top)
  (equal (car (last (first-N bot top))) top)
  :hints (("Goal" :in-theory (enable first-N-definition-rule))))

(property first-N-bisect (bot mid top :pos)
  :h (^ (<= bot mid) (< mid top))
  (equal (append (first-N bot mid)
		 (first-N (1+ mid) top))
	 (first-N bot top))
  :hints (("Goal" :in-theory (enable first-N-definition-rule))))

(in-theory (disable first-N-bisect))

(property len[first-n]=1+n (bot top :pos)
  :h (<= bot top)
  (equal (len (first-n bot top)) (1+ (- top bot)))
  :hints (("Goal" :in-theory (enable first-N-definition-rule))))

(property last=nth (tl :tl)
  :h (consp tl)
  (equal (nth (1- (len tl)) tl) (car (last tl))))

(property nth-T=nth-TX (tl0 tl1 :tl n :nat)
  :h (< n (len tl0))
  (equal (nth n (append tl0 tl1)) (nth n tl0)))

#|
Proof:
(nth k (first-n bot top))

= { first-N-bisect (mid (+ bot k)) }

(nth k (append (first-n bot (+ bot k)) (first-n (+ bot k 1) top)))

= { nth-T=nth-TX (tl0 (first-n bot (+ bot k))) 
                 (tl1 (first-n (+ bot k 1) top))
                 (n k) }

(nth k (first-n bot (+ bot k)))

= { len[first-n]=1+n (top (+ bot k)) }

(nth (1- (len (first-n bot (+ bot k)))) (first-n bot (+ bot k)))

= { last=nth (tl (first-n bot (+ bot k))) }

(car (last (first-n bot (+ bot k))))

= { first-N-last=N (top (+ bot k)) }

(+ bot k)
|#
(property kth-element-first-n (bot top :pos k :nat)
  :h (^ (< bot top) (< k (1+ (- top bot))))
  (equal (nth k (first-n bot top)) (+ bot k))
  :hints (("Goal" :use ((:instance first-N-bisect (mid (+ bot k)))
			(:instance nth-T=nth-TX (tl0 (first-n bot (+ bot k))) 
				   (tl1 (first-n (+ bot k 1) top))
				   (n k))
			(:instance len[first-n]=1+n (top (+ bot k)))
			(:instance last=nth (tl (first-n bot (+ bot k))))
			(:instance first-N-last=N (top (+ bot k)))))))


(definecd index-of (k :pos ps :poss) :nat
  :ic (in k ps)
  (if (equal k (car ps)) 0 (1+ (index-of k (cdr ps)))))

(property index-of-works (k :pos ps :poss)
  :h (in k ps)
  (equal (nth (index-of k ps) ps) k)
  :hints (("Goal" :in-theory (enable index-of-definition-rule))))

(in-theory (disable index-of-works))

(property index-of<len (k :pos ps :poss)
  :h (in k ps)
  (< (index-of k ps) (len ps))
  :hints (("Goal" :in-theory (enable index-of-definition-rule))))

(property j>N->j-not-in-first-n (bot top k :pos)
  :h (^ (< top k) (<= bot top))
  (! (in k (first-N bot top)))
  :instructions ((:casesplit (in k (first-n bot top)))
                 (:use (:instance index-of<len (ps (first-n bot top))))
                 (:use (:instance len[first-n]=1+n))
                 (:use (:instance kth-element-first-n
                                  (k (index-of k (first-n bot top)))))
		 (:use (:instance index-of-works (ps (first-n bot top))))
                 (:casesplit (equal bot top))
                 (:use (:instance first-n-definition-rule))
                 :prove :prove :prove))

(definecd first-1N (N :pos) :poss (first-N 1 N))

(property has-all-cons (ps0 :poss p b :pos)
  :h (has-all p ps0)
  (has-all p (append ps0 (list b)))
  :hints (("Goal" :in-theory (enable has-all-definition-rule))))

(property first-1N=first-1N-1+[N] (N :pos)
  (equal (first-1N (1+ N))
	 (append (first-1N N) (list (1+ N))))
  :hints (("Goal" :use ((:instance first-1N-definition-rule (N (1+ N)))
			(:instance first-1N-definition-rule)
			(:instance first-N-bisect
				   (bot 1) (mid N) (top (1+ N)))
			(:instance first-n-definition-rule
				   (bot (1+ N)) (top (1+ N)))))))

(definecd first-1N-inductor (N :pos) :bool
  (if (equal N 1) t (first-1N-inductor (1- N))))

(property app-in2 (a :all tl0 tl1 :tl)
  :h (in a tl0)
  (in a (append tl0 tl1)))

(in-theory (disable app-in2 first-1N=first-1N-1+[N] has-all-cons))

(property has-all-first-1N (N :pos)
  (has-all N (first-1N N))
  :instructions ((:induct (first-1n-inductor n))
                 (:casesplit (< 1 n))
                 :pro
                 (:use (:instance has-all-cons (ps0 (first-1n (1- n)))
                                  (p (1- n))
                                  (b n)))
                 :pro
                 (:use (:instance has-all-definition-rule (p n)
                                  (ps (first-1n n))))
                 (:use (:instance first-1n-definition-rule))
                 (:use (:instance first-1n=first-1n-1+[n] (n (1- n))))
                 (:use (:instance app-in2 (a n)
                                  (tl0 (first-1n (1- n)))
                                  (tl1 (list n))))
                 :pro :prove
                 :prove :prove))

(property cumackp-n (N :pos) (cumackp (1+ N) (first-1N N))
  :instructions ((:induct (first-1n-inductor n))
                 :pro
                 (:use (:instance cumackp-definition-rule (a (1+ n))
                                  (ps (first-1n n))))
                 :pro
                 (:use (:instance first-1n-definition-rule))
                 :pro
                 (:claim (not (in (+ 1 n) (first-1n n))))
                 (:claim (has-all (+ -1 1 n) (first-1n n)))
                 :prove :prove))


(in-theory (disable has-all-first-1N))

#|
Theory of a perfect sender + receiver system.
|#
(definecd single-step (sys :system) :system
  :ic (^ (cumackp (sender-state-cur (system-sender sys))
		  (system-receiver sys))
	 (= (len (tbf-D (system-s2r sys))) 0)
	 (o< 1 (tbf-ttl (system-s2r sys)))
	 ;; Note the precondition that cur < N + hiA
	 (< (sender-state-cur (system-sender sys))
	    (+ (sender-state-N (system-sender sys))
	       (sender-state-hiA (system-sender sys)))))
  (mset :s2r
	(tbf-dlv
	 (tbf-tick
	  (tbf-trn (system-s2r sys) (sender-state-cur (system-sender sys)) nil))
	 0)
	(mset :sender
	      (sender-snd-cur (system-sender sys))
	      (mset :receiver
		    (append (system-receiver sys)
			    (list (sender-state-cur (system-sender sys))))
		    sys)))
  :body-contracts-hints (("Goal" :in-theory (enable tbf-dlv-definition-rule
						    tbf-age-definition-rule
						    age-all-definition-rule
						    remove-ith-definition-rule
						    tbf-tick-definition-rule
						    tbf-trn-definition-rule
						    sender-snd-cur-definition-rule))))

;; Sender and s2r constants stay the same; r2s stays the same
(property single-step-doesnt-change-hiA-N-chans (sys :system)
  :h (^ (cumackp (sender-state-cur (system-sender sys))
		  (system-receiver sys))
	 (= (len (tbf-D (system-s2r sys))) 0)
	 (o< 1 (tbf-ttl (system-s2r sys)))
	 ;; Note the precondition that cur < N + hiA
	 (< (sender-state-cur (system-sender sys))
	    (+ (sender-state-N (system-sender sys))
	       (sender-state-hiA (system-sender sys)))))
  (^ (= (sender-state-hiA (system-sender (single-step sys))) (sender-state-hiA (system-sender sys)))
       (= (sender-state-N (system-sender (single-step sys))) (sender-state-N (system-sender sys)))
       (equal (tbf-D (system-s2r (single-step sys))) (tbf-D (system-s2r sys)))
       (equal (tbf-ttl (system-s2r (single-step sys))) (tbf-ttl (system-s2r sys)))
       (= (tbf-b-cap (system-s2r (single-step sys))) (tbf-b-cap (system-s2r sys)))
       (= (tbf-l-cap (system-s2r (single-step sys))) (tbf-l-cap (system-s2r sys)))
       (= (tbf-r (system-s2r (single-step sys))) (tbf-r (system-s2r sys)))
       (equal (system-r2s (single-step sys)) (system-r2s sys)))
  :hints (("Goal" :in-theory (enable single-step-definition-rule
                                          tbf-trn-definition-rule
                                          tbf-tick-definition-rule
                                          tbf-age-definition-rule
                                          age-all-definition-rule
                                          remove-ith-definition-rule
                                          tbf-dlv-definition-rule))))

;; If rcvd = 1,...,cur-1 then cumack = cur
(property first-1N-cumack-translation-sys (sys :system)
  :h (equal (system-receiver sys)
	    (if (equal (sender-state-cur (system-sender sys)) 1)
		nil
	      (first-1N (1- (sender-state-cur (system-sender sys))))))
  (cumackp (sender-state-cur (system-sender sys))
	   (system-receiver sys))
  :hints (("Goal" :use (:instance cumackp-n (N (1- (sender-state-cur (system-sender sys))))))))

;; ... therefore, we can wrap single-step in a precondition that rcvd = 1,...,cur-1
(definecd single-step-perfect-r (sys :system) :system
  :ic (^ (equal (system-receiver sys)
		(if (equal (sender-state-cur (system-sender sys)) 1)
		    nil
		  (first-1N (1- (sender-state-cur (system-sender sys))))))
	 (= (len (tbf-D (system-s2r sys))) 0)
	 (o< 1 (tbf-ttl (system-s2r sys)))
	 ;; Note the precondition that cur < N + hiA
	 (< (sender-state-cur (system-sender sys))
	    (+ (sender-state-N (system-sender sys))
	       (sender-state-hiA (system-sender sys)))))
  (single-step sys)
  :body-contracts-hints
  (("Goal" :use (:instance first-1N-cumack-translation-sys))))

;; Indeed, it's an invariant!  (i.e., if rcvd was 1,...,cur-1, then now, it is 1,...,cur.
;; But we will see shortly that cur increments, so actually, it's simply the invariant:
;;                             rcvd = 1,...,cur-1
(property sender-snd-cur-incr-cur (ss :sender-state)
  :h (< (mget :cur ss)
	(+ (mget :n ss) (mget :hia ss)))
  (equal (sender-state-cur (sender-snd-cur ss))
	 (1+ (sender-state-cur ss)))
  :hints (("Goal" :in-theory (enable sender-snd-cur-definition-rule))))

;; This theorem will be useful later.  Basically says that in single-step, the sender
;; updates precisely according to sender-snd-cur function.
(property system-sender-perfect-step (sys :system)
  :h (^ (equal (system-receiver sys)
	       (if (equal (sender-state-cur (system-sender sys)) 1)
		   nil
		 (first-1N (1- (sender-state-cur (system-sender sys))))))
	(= (len (tbf-D (system-s2r sys))) 0)
	(o< 1 (tbf-ttl (system-s2r sys)))
	;; Note the precondition that cur < N + hiA
	(< (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys)))))
  (equal (system-sender (single-step-perfect-r sys))
	 (sender-snd-cur (system-sender sys)))
  :instructions
  ((:use (:instance single-step-perfect-r-definition-rule))
   (:use (:instance single-step-definition-rule))
   (:use (:instance first-1n-cumack-translation-sys))
   :pro
   (:claim
    (equal
     (single-step-perfect-r sys)
     (mset :s2r
           (tbf-dlv (tbf-tick (tbf-trn (system-s2r sys)
                                       (sender-state-cur (system-sender sys))
                                       nil))
                    0)
           (mset :sender
                 (sender-snd-cur (system-sender sys))
                 (mset :receiver
                       (app (system-receiver sys)
                            (list (sender-state-cur (system-sender sys))))
                       sys)))))
   (:drop 1 2 3)
   :prove))

;; In a "single step", cur gets incremented, as I described previously.
(property single-step-perfect-r-cur (sys :system)
  :h (^ (equal (system-receiver sys)
	       (if (equal (sender-state-cur (system-sender sys)) 1)
		   nil
		 (first-1N (1- (sender-state-cur (system-sender sys))))))
	(= (len (tbf-D (system-s2r sys))) 0)
	(o< 1 (tbf-ttl (system-s2r sys)))
	(< (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys)))))
  (= (sender-state-cur (system-sender (single-step-perfect-r sys)))
     (1+ (sender-state-cur (system-sender sys))))
  :hints (("Goal" :use ((:instance sender-snd-cur-incr-cur (ss (system-sender sys)))
			(:instance system-sender-perfect-step)))))

;; In a "single step", rcvd gets "incremented" from 1,...,cur-1 to 1,...,cur.
;; And then, cur is incremented after that, as described above.
;; At which point, it is once again the case that rcvd = 1,...,cur-1.
(property single-step-perfect-r-oc (sys :system)
  :h (^ (equal (system-receiver sys)
	       (if (equal (sender-state-cur (system-sender sys)) 1)
		   nil
		 (first-1N (1- (sender-state-cur (system-sender sys))))))
	(= 0 (len (tbf-D (system-s2r sys))))
	(o< 1 (tbf-ttl (system-s2r sys)))
	;; Note the precondition that cur < N + hiA
	(< (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys)))))
  (equal (system-receiver (single-step-perfect-r sys))
	 (first-1N (sender-state-cur (system-sender sys))))
  :instructions
  ((:use (:instance single-step-perfect-r-definition-rule))
   (:use (:instance single-step-definition-rule))
   (:use (:instance first-1n-cumack-translation-sys))
   :pro
   (:claim
    (equal
     (single-step-perfect-r sys)
     (mset :s2r
           (tbf-dlv (tbf-tick (tbf-trn (system-s2r sys)
                                       (sender-state-cur (system-sender sys))
                                       nil))
                    0)
           (mset :sender
                 (sender-snd-cur (system-sender sys))
                 (mset :receiver
                       (app (system-receiver sys)
                            (list (sender-state-cur (system-sender sys))))
                       sys)))))
   (:drop 1 2 3)
   (:claim (equal (system-receiver (single-step-perfect-r sys))
		  (app (system-receiver sys)
		       (list (sender-state-cur (system-sender sys))))))
   (:use (:instance first-1n=first-1n-1+[n]
		    (n (1- (sender-state-cur (system-sender sys))))))
   :pro :prove))

(property car-last-cons-possp-is-pos (ps :pos)
  :h (consp ps)
  (posp (car (last ps))))

;; After the final delivery to the receiver, the right-most value is
;; (1- (sender-state-cur (system-sender sys))).  Therefore,
;;     rcvd = 1,...,(1- (sender-state-cur (system-sender sys)))
;; and the receiver responds with ack=(sender-state-cur (system-sender sys)).
(property ack=1-cur (sys :system)
  :h (^ (equal (system-receiver sys)
	       (if (equal (sender-state-cur (system-sender sys)) 1)
		   nil
		 (first-1N (1- (sender-state-cur (system-sender sys))))))
	;; Note the precondition that cur < N + hiA
	(= (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys)))))
  (^ (posp (sender-state-N (system-sender sys)))
     (posp (sender-state-hiA (system-sender sys)))
     (< 1 (sender-state-cur (system-sender sys)))
     (equal (system-receiver sys) (first-1N (1- (sender-state-cur (system-sender sys)))))
     (consp (system-receiver sys))
     (possp (system-receiver sys))
     (posp (car (last (system-receiver sys))))
     (= (car (last (system-receiver sys))) (1- (sender-state-cur (system-sender sys)))))
  :hints (("Goal" :instructions
  ((:use (:instance first-1n=first-1n-1+[n]
		    (n (1- (1- (sender-state-cur (system-sender sys)))))))
   :pro
   (:claim (and (posp (sender-state-n (system-sender sys)))
		(posp (sender-state-hia (system-sender sys)))
		(< 1
		   (sender-state-cur (system-sender sys)))
		(equal (system-receiver sys)
		       (first-1n (+ -1
				    (sender-state-cur (system-sender sys)))))
		(consp (system-receiver sys))
		(pos-listp (system-receiver sys))))
   :s
   (:use (:instance car-last-cons-possp-is-pos
		    (ps (system-receiver sys))))
   :pro
   (:use (:instance first-1n-definition-rule
		    (n (1- (sender-state-cur (system-sender sys))))))
   (:use (:instance first-n-last=n (bot 1)
		    (top (1- (sender-state-cur (system-sender sys))))))
   :pro
   (:claim (equal (first-1n (+ -1
			       (sender-state-cur (system-sender sys))))
		  (first-n 1
			   (+ -1
			      (sender-state-cur (system-sender sys))))))
   (:drop 2)
   (:claim
    (equal (car (last (first-n 1
			       (+ -1
				  (sender-state-cur (system-sender sys))))))
	   (+ -1
	      (sender-state-cur (system-sender sys)))))
   (:drop 1)
   (:casesplit (posp (+ -1 -1
			(sender-state-cur (system-sender sys)))))
   :prove :prove))))

;; Finish off the above property by saying precisely which ack receiver will send.
(property cumack=car-last+1-rcvd (sys :system)
  :h (^ (equal (system-receiver sys)
	       (if (equal (sender-state-cur (system-sender sys)) 1)
		   nil
		 (first-1N (1- (sender-state-cur (system-sender sys))))))
	;; Note the precondition that cur < N + hiA
	(= (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys)))))
  (cumackp (sender-state-cur (system-sender sys)) (system-receiver sys))
  :hints (("Goal" :use ((:instance cumackp-N (N (1- (sender-state-cur (system-sender sys)))))))))

;; Prove that the ack can, in fact, get sent.
(definecd send-that-ack (sys :system) :system
  :ic (^ (= 0 (len (tbf-D (system-r2s sys))))
	 (o< 1 (tbf-ttl (system-r2s sys))))
  (mset :r2s (tbf-dlv (tbf-tick (tbf-trn (system-r2s sys) (sender-state-cur (system-sender sys)) nil)) 0) sys)
  :body-contracts-hints (("Goal" :in-theory (enable tbf-dlv-definition-rule
						   tbf-trn-definition-rule
						   tbf-tick-definition-rule
						   tbf-age-definition-rule
						   age-all-definition-rule
						   remove-ith-definition-rule))))

;; Now if we send the ack, show that hiA gets incremented to be cur + N, and so the window slides.
(property (sys :system)
  :h (^ (= (sender-state-cur (system-sender sys))
	   (+ (sender-state-N (system-sender sys))
	      (sender-state-hiA (system-sender sys))))
	(= (sender-state-hiP (system-sender sys))
	   (1- (sender-state-cur (system-sender sys)))))
  (= (sender-state-hiA
      (sender-rcv-ack
       (system-sender sys)
       (sender-state-cur (system-sender sys))))
     (sender-state-cur (system-sender sys)))
  :hints (("Goal" :in-theory (enable sender-rcv-ack-definition-rule))))

;; So, we've shown that it takes N steps to get the window transmitted to the receiver.
;; We can say each step takes del(trn_s) + del(tick_s) + del(dlv_s) time.
;; And we've shown that it takes 1 additional step to get the ack back to the sender,
;; and this step takes del(trn_r) + del(tick_r) + del(dlv_r) time.
;; I claim that in the best case, all you need to know are cur, hiA, and N to predict the entire
;; system behavior, as cur > 1 -> hiP = cur - 1.
(defdata bst-state (record (cur . pos) (hiA . pos) (N . pos)))

(definecd bst-refinement (sys :system) :bst-state
  (bst-state (sender-state-cur (system-sender sys))
       (sender-state-hiA (system-sender sys))
       (sender-state-N (system-sender sys))))

(definecd sending-window (sys :system) :boolean
  (< (sender-state-cur (system-sender sys))
     (+ (sender-state-N (system-sender sys))
  (sender-state-hiA (system-sender sys)))))

(definecd sliding-window (sys :system) :boolean
  (= (sender-state-cur (system-sender sys))
     (+ (sender-state-N (system-sender sys))
  (sender-state-hiA (system-sender sys)))))

;; Invariant over system variables which must hold in all best case system states.
(definecd bst-casep (sys :system) :boolean
  (^ (equal (system-receiver sys)
      (if (equal (sender-state-cur (system-sender sys)) 1)
    nil
        (first-1N (1- (sender-state-cur (system-sender sys))))))
     (endp (tbf-D (system-s2r sys))) ;; change len=0 to endp (TODO everywhere)
     (o< 1 (tbf-ttl (system-s2r sys)))
     (endp (tbf-D (system-r2s sys)))
     (o< 1 (tbf-ttl (system-r2s sys)))
     (or (sending-window sys) (sliding-window sys))
     (= (sender-state-hiP (system-sender sys))
  (1- (sender-state-cur (system-sender sys))))))

(definecd bst-sending-window-tran (sys :system) :system
  :ic (^ (sending-window sys) (bst-casep sys))
  (single-step-perfect-r sys)
  :body-contracts-hints (("Goal" :in-theory (enable sending-window-definition-rule
                bst-casep-definition-rule))))

(property bst-sending-window-tran-oc-hints-1 (sys :system)
  :h (^ (sending-window sys) (bst-casep sys))
  (^ (< (sender-state-cur (system-sender sys))
        (+ (sender-state-n (system-sender sys))
           (sender-state-hia (system-sender sys))))
     (equal (system-receiver sys)
      (and (not (equal (sender-state-cur (system-sender sys))
           1))
     (first-1n (+ -1
            (sender-state-cur (system-sender sys))))))
     (= (len (tbf-d (system-s2r sys))) 0)
     (o< 1 (tbf-ttl (system-s2r sys)))
     (= (len (tbf-d (system-r2s sys))) 0)
     (o< 1 (tbf-ttl (system-r2s sys)))
     (or (sending-window sys)
   (sliding-window sys))
     (equal (system-sender (single-step-perfect-r sys))
      (sender-snd-cur (system-sender sys)))
     (equal (sender-state-cur (sender-snd-cur (system-sender sys)))
      (+ 1
         (sender-state-cur (system-sender sys))))
     (or (sending-window (bst-sending-window-tran sys))
   (sliding-window (bst-sending-window-tran sys)))
     (= (len (tbf-d (system-s2r (bst-sending-window-tran sys)))) 0)
     (= (len (tbf-d (system-r2s (bst-sending-window-tran sys)))) 0)
     (o< 1 (tbf-ttl (system-s2r (bst-sending-window-tran sys))))
     (o< 1 (tbf-ttl (system-r2s (bst-sending-window-tran sys))))
     (= (1+ (sender-state-hiP (system-sender sys)))
  (sender-state-hiP (system-sender (bst-sending-window-tran sys)))))
  :hints (("Goal" :use ((:instance bst-casep-definition-rule)
      (:instance system-sender-perfect-step)
      (:instance sender-snd-cur-incr-cur (ss (system-sender sys)))
      (:instance sending-window-definition-rule)
      (:instance sending-window-definition-rule
           (sys (bst-sending-window-tran sys)))
      (:instance sliding-window-definition-rule
           (sys (bst-sending-window-tran sys)))
      (:instance bst-sending-window-tran-definition-rule)
      (:instance single-step-perfect-r-definition-rule)
      (:instance single-step-doesnt-change-hia-n-chans)
      (:instance first-1n-cumack-translation-sys)))))

#|
This is an important theorem, because it says that bst-sending-window-tran
can simply repeat until cur = hiA + N.
|#
(property bst-sending-window-tran-oc (sys :system)
  :h (^ (sending-window sys) (bst-casep sys))
  (bst-casep (bst-sending-window-tran sys))
  :instructions
  ((:use (:instance bst-sending-window-tran-oc-hints-1))
   (:use (:instance bst-casep-definition-rule))
   (:use (:instance system-sender-perfect-step))
   (:use (:instance sender-snd-cur-incr-cur
        (ss (system-sender sys))))
   (:use (:instance sending-window-definition-rule))
   (:use (:instance sending-window-definition-rule
        (sys (bst-sending-window-tran sys))))
   (:use (:instance sliding-window-definition-rule
        (sys (bst-sending-window-tran sys))))
   (:use (:instance single-step-perfect-r-oc))
   (:use (:instance bst-casep-definition-rule
        (sys (bst-sending-window-tran sys))))
   (:use (:instance bst-sending-window-tran-definition-rule))
   (:use (:instance single-step-perfect-r-definition-rule))
   :pro
   (:claim (equal (system-receiver (bst-sending-window-tran sys))
      (first-1n (sender-state-cur (system-sender sys)))))
   (:claim
    (equal
     (system-receiver (bst-sending-window-tran sys))
     (^ (!= (sender-state-cur (system-sender (bst-sending-window-tran sys))) 1)
  (first-1n (1- (sender-state-cur (system-sender (bst-sending-window-tran sys))))))))
   :prove))

(definecd bst-sliding-window-tran (sys :system) :system
  :ic (^ (sliding-window sys) (bst-casep sys))
  (mset :r2s
  (tbf-dlv
   (tbf-tick
    (tbf-trn (system-r2s sys)
       (sender-state-cur (system-sender sys))
       nil))
   0)
  (mset :sender
        (sender-rcv-ack
         (system-sender sys)
         (sender-state-cur (system-sender sys)))
        sys))
  :body-contracts-hints (("Goal" :in-theory (enable tbf-dlv-definition-rule
                tbf-tick-definition-rule
                tbf-age-definition-rule
                age-all-definition-rule
                remove-ith-definition-rule
                tbf-trn-definition-rule
                sender-rcv-ack-definition-rule
                sliding-window-definition-rule
                bst-casep-definition-rule))))

(in-theory (disable bst-sending-window-tran-oc-hints-1))

;; Again -- sorry pete!  I will improve.
(property bst-sliding-window-tran-oc (sys :system)
  :h (^ (sliding-window sys) (bst-casep sys))
  (^ (sending-window (bst-sliding-window-tran sys))
     (bst-casep (bst-sliding-window-tran sys)))
  :instructions
  ((:use (:instance bst-sliding-window-tran-definition-rule))
   (:use (:instance sliding-window-definition-rule))
   (:use (:instance sending-window-definition-rule
        (sys (bst-sliding-window-tran sys))))
   (:use (:instance sender-rcv-ack-definition-rule
        (ss (system-sender sys))
        (ack (sender-state-cur (system-sender sys)))))
   (:use (:instance bst-casep-definition-rule))
   :pro
   (:claim (sending-window (bst-sliding-window-tran sys)))
   :s
   (:in-theory (enable tbf-dlv-definition-rule
           tbf-trn-definition-rule
           tbf-tick-definition-rule
           tbf-age-definition-rule
           age-all-definition-rule
           remove-ith-definition-rule))
   (:use (:instance bst-casep-definition-rule
        (sys (bst-sliding-window-tran sys))))
   :pro
   (:claim
    (= (sender-state-hip (system-sender (bst-sliding-window-tran sys)))
       (+ -1
          (sender-state-cur (system-sender (bst-sliding-window-tran sys))))))
   (:claim (o< 1
         (tbf-ttl (system-r2s (bst-sliding-window-tran sys)))))
   (:claim (o< 1
         (tbf-ttl (system-s2r (bst-sliding-window-tran sys)))))
   (:claim (= (len (tbf-d (system-r2s sys))) 0))
   (:claim (= (len (tbf-d (system-s2r sys))) 0))
   (:claim (equal (system-receiver (bst-sliding-window-tran sys))
      (system-receiver sys)))
   :prove))

#|
Here is our comnplete best case transition function.
|#
(definecd bst-case-sys-tran (sys :system) :system
  :ic (bst-casep sys)
  (if (sliding-window sys)
      (bst-sliding-window-tran sys)
    (bst-sending-window-tran sys))
  :body-contracts-hints (("Goal" :in-theory (enable bst-casep-definition-rule))))

#|
Let's prove that bst-case-sys-tran can repeat.
|#
(property bst-case-sys-tran-oc (sys :system)
  :h (bst-casep sys)
  (bst-casep (bst-case-sys-tran sys))
  :hints (("Goal" :use ((:instance bst-casep-definition-rule)
      (:instance bst-case-sys-tran-definition-rule)))))

#| 
Claim: Best case machine bisimulates the following

                            hiA:=cur
           ___________[ snd_r tick_r dlv_r ]________________
          |                                               |
          V                                               |
---> (cur < hiA + N) ----[ snd_s tick_s dlv_s ] ---> (cur = hiA + N)
     |           ^             cur++
     |           |
     |-[ snd_s tick_s dlv_s ]
              cur++
 
which encodes the regular expression

    ( ( snd_s tick_s dlv_s )^N snd_r tick_r dlv_r )^*

|#
(definecd bst-case-tran (as :bst-state) :bst-state
  :ic (<= (bst-state-cur as) (+ (bst-state-hiA as) (bst-state-N as)))
  (if (< (bst-state-cur as)
   (+ (bst-state-hiA as)
      (bst-state-N as)))
      (mset :cur (1+ (bst-state-cur as)) as)
    (mset :hiA (bst-state-cur as) as)))


(definecd bst-refinement (sys :system) :bst-state
  (bst-state (sender-state-cur (system-sender sys))
       (sender-state-hiA (system-sender sys))
       (sender-state-N (system-sender sys))))

(property bst-refinement-preserves-tran-ic-sending (sys :system)
  :h (^ (bst-casep sys) (sending-window sys))
  (< (bst-state-cur (bst-refinement sys))
     (+ (bst-state-hiA (bst-refinement sys))
  (bst-state-N (bst-refinement sys))))
  :hints (("Goal" :in-theory (enable bst-refinement-definition-rule
             bst-casep-definition-rule
             sending-window-definition-rule))))

(property bst-refinement-preserves-tran-ic-sliding (sys :system)
  :h (^ (bst-casep sys) (sliding-window sys))
  (= (bst-state-cur (bst-refinement sys))
     (+ (bst-state-hiA (bst-refinement sys))
  (bst-state-N (bst-refinement sys))))
  :hints (("Goal" :in-theory (enable bst-refinement-definition-rule
             bst-casep-definition-rule
             sliding-window-definition-rule))))

#|
system = the whole shabang with sender, receiver, and tbf
bst-state = the tuple with (cur, hiA, N) and nothing else

bst-refinement : system -> bst-state
bst-case-tran : bst-state -> bst-state
bst-case-sys-tran : system -> system
|#
(definecd bst-case-refinement-thm-witness (sys :system) :boolean
  :ic (bst-casep sys)
  (equal (bst-case-tran (bst-refinement sys))
   (bst-refinement (bst-case-sys-tran sys)))
  :body-contracts-hints (("Goal" :use ((:instance bst-refinement-preserves-tran-ic-sending)
               (:instance bst-refinement-preserves-tran-ic-sliding)
               (:instance bst-casep-definition-rule)))))

(property bst-sliding-window-tran-sender-effect (sys :system)
  :h (^ (sliding-window sys) (bst-casep sys))
  (^ (= (sender-state-cur (system-sender (bst-sliding-window-tran sys)))
  (sender-state-cur (system-sender sys)))
     (= (sender-state-hiA (system-sender (bst-sliding-window-tran sys)))
  (sender-state-cur (system-sender sys)))
     (= (sender-state-N (system-sender (bst-sliding-window-tran sys)))
  (sender-state-N (system-sender sys))))
  :hints (("Goal" :use ((:instance bst-sliding-window-tran-definition-rule)
      (:instance sender-rcv-ack-definition-rule
           (ss (system-sender sys))
           (ack (sender-state-cur (system-sender sys))))
      (:instance sliding-window-definition-rule)
      (:instance bst-casep-definition-rule)))))

(property bst-hiP-cur-relationship (sys :system)
  :h (bst-casep sys)
  (= (sender-state-hiP (system-sender sys))
     (1- (sender-state-cur (system-sender sys))))
  :hints (("Goal" :in-theory (enable bst-casep-definition-rule))))


(property bst-case-refinement-thm-sliding-helper (sys :system)
  :h (^ (bst-casep sys) (sliding-window sys))
  (^
   (= (bst-state-cur (bst-refinement sys))
     (+ (bst-state-N (bst-refinement sys))
  (bst-state-hiA (bst-refinement sys))))
   ;; 1. (bst-case-tran (bst-refinement sys))'s cur = (bst-refinement sys)'s cur
   (= (bst-state-cur (bst-case-tran (bst-refinement sys)))
      (bst-state-cur (bst-refinement sys)))
   ;; 2. (bst-case-tran (bst-refinement sys))' hiA = 1 - (bst-refinement sys)'s cur
   (= (bst-state-hiA (bst-case-tran (bst-refinement sys)))
      (bst-state-cur (bst-refinement sys)))
   ;; 3. (bst-case-tran (bst-refinement sys))'s N = (bst-refinement sys)'s N
   (= (bst-state-N (bst-case-tran (bst-refinement sys)))
      (bst-state-N (bst-refinement sys)))
   ;; 4. (bst-refinement sys)'s cur = sys's sender's cur
   (= (bst-state-cur (bst-refinement sys))
      (sender-state-cur (system-sender sys)))
   ;; 5. (bst-refinement sys)'s hiA = sys's sender's hiA
   (= (bst-state-hiA (bst-refinement sys))
      (sender-state-hiA (system-sender sys)))
   ;; 6. (bst-refinement sys)'s N = sys's sender's N
   (= (bst-state-N (bst-refinement sys))
      (sender-state-N (system-sender sys)))
   ;; 7. (bst-refinement (bst-case-sys-tran sys))'s cur = (bst-case-sys-tran sys)'s cur
   (= (bst-state-cur (bst-refinement (bst-case-sys-tran sys)))
      (sender-state-cur (system-sender (bst-case-sys-tran sys))))
   (= (sender-state-cur (system-sender (bst-case-sys-tran sys)))
      (sender-state-cur (system-sender sys)))
   ;; 8. (bst-refinement (bst-case-sys-tran sys))'s hiA = (bst-case-sys-tran sys)'s hiA
   (= (bst-state-hiA (bst-refinement (bst-case-sys-tran sys)))
      (sender-state-hiA (system-sender (bst-case-sys-tran sys))))
   ;; 9. (bst-refinement (bst-case-sys-tran sys))'s N = (bst-case-sys-tran sys)'s N
   (= (bst-state-N (bst-refinement (bst-case-sys-tran sys))) ;; this one is failing
      (sender-state-N (system-sender (bst-case-sys-tran sys))))
   ;; 10. (bst-case-sys-tran sys)'s cur = sys's sender's cur
   (= (bst-state-cur (bst-refinement (bst-case-sys-tran sys)))
      (sender-state-cur (system-sender sys)))
   ;; 11. (bst-case-sys-tran sys)'s hiA = sys's sender's cur
   (= (bst-state-hiA (bst-refinement (bst-case-sys-tran sys)))
      (bst-state-cur (bst-refinement (bst-case-sys-tran sys)))))
   :hints (("Goal" :in-theory (enable sliding-window-definition-rule
              bst-case-tran-definition-rule
              bst-refinement-definition-rule
              bst-case-sys-tran-definition-rule
              bst-sliding-window-tran-definition-rule
              sender-rcv-ack-definition-rule)
      :use ((:instance bst-hiP-cur-relationship)))))

(property bst-case-refinement-thm-sliding (sys :system)
  :h (^ (bst-casep sys) (sliding-window sys))
  (bst-case-refinement-thm-witness sys)
  :hints (("Goal" :use ((:instance bst-case-refinement-thm-sliding-helper)
      (:instance bst-case-refinement-thm-witness-definition-rule))
     :in-theory (enable sliding-window-definition-rule
            bst-case-tran-definition-rule
            bst-refinement-definition-rule
            bst-case-sys-tran-definition-rule
            bst-sliding-window-tran-definition-rule
            sender-rcv-ack-definition-rule))))

(definecd reduce-sender-bst-sys-step-witness (sys :system) :bool
  :ic (^ (bst-casep sys) (sending-window sys))
  (equal (system-sender (bst-case-sys-tran sys))
   (sender-snd-cur (system-sender sys)))
  :body-contracts-hints (("Goal" :in-theory (enable sending-window-definition-rule
                   bst-casep-definition-rule))))

(property reduce-sender-bst-sys-step (sys :system)
  :h (^ (bst-casep sys) (sending-window sys))
  (reduce-sender-bst-sys-step-witness sys)
  :hints (("Goal" :use ((:instance reduce-sender-bst-sys-step-witness-definition-rule)
      (:instance bst-case-sys-tran-definition-rule)
      (:instance sliding-window-definition-rule)
      (:instance sending-window-definition-rule)
      (:instance bst-casep-definition-rule)
      (:instance bst-sending-window-tran-definition-rule)
      (:instance single-step-perfect-r-definition-rule)
      (:instance system-sender-perfect-step)))))

(property bst-case-refinement-thm-sending (sys :system)
  :h (^ (bst-casep sys) (sending-window sys))
  (bst-case-refinement-thm-witness sys)
  :hints (("Goal" :in-theory (enable 
                       bst-case-sys-tran-definition-rule
                       sliding-window-definition-rule
                       sending-window-definition-rule
                       bst-casep-definition-rule
                       bst-case-tran-definition-rule
                       bst-refinement-definition-rule)
     :use ((:instance reduce-sender-bst-sys-step)
     (:instance reduce-sender-bst-sys-step-witness-definition-rule)
     (:instance sender-snd-cur-definition-rule (ss (system-sender sys)))
     (:instance bst-case-refinement-thm-witness-definition-rule)))))

(property bst-case-refinement (sys :system)
  :h (bst-casep sys)
  (bst-case-refinement-thm-witness sys)
  :hints (("Goal" :in-theory (enable bst-casep-definition-rule)
     :use ((:instance bst-case-refinement-thm-sliding)
     (:instance bst-case-refinement-thm-sending)))))

;; Theorem: If the receiver sends ACKs sparingly, and there is a loss, then the sender
;; will be forced to retransmit everything starting with the lost packet.
(property (ack :pos ss :sender-state)
  :h (^ (= (sender-state-hiA ss) ack)
	(= (sender-state-cur ss)
	   (+ (sender-state-hiA ss) (sender-state-N ss))))
  (let* ((ss (sender-rcv-ack ss ack))
	 (ss (sender-timeout ss)) ;; because no NEW acks
	 (cur (sender-state-cur ss)))
    (^ (posp cur) (posp ack) (= cur ack)))
  :hints (("Goal" :in-theory (enable sender-rcv-ack-definition-rule
				     sender-timeout-definition-rule))))
