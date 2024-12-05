(in-package "ACL2S")
(include-book "gobackn")

#|
---------- Define simplification map ----------
|#
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
            (1+ (maxl (system-receiver sys))) ;; assume out of order pkts ignored
            (sender-state-cur (system-sender sys))
            (sender-state-hiA (system-sender sys))
            (sender-state-N (system-sender sys))))

;; Check assumption that all plds have size one
(definecd all-1 (tdgs :tdgs) :bool
  (match tdgs
    (() t)
    ((tdg . rst) (^ (= (length (tdg-pld tdg)) 1) (all-1 rst)))))

(definecd all-1-inductor (tdgs :tdgs) :nat
  (match tdgs
    (() 0)
    ((& . rst) (all-1-inductor rst))))

(propertyd all-1-works-lst (tdgs :tdgs)
  :h (^ (consp tdgs) (all-1 tdgs))
  (^
   (natp (1- (len tdgs)))
   (< (1- (len tdgs)) (len tdgs))
   (tdgp (nth (1- (len tdgs)) tdgs))
   (= (length (tdg-pld (nth (1- (len tdgs)) tdgs))) 1))
  :hints (("Goal" :in-theory (enable all-1-definition-rule)
       :induct (all-1-inductor tdgs))))

;; Note how if all-1 holds, then 1 token = 1 packet.
(propertyd all-1=>1-tkn-to-dlv-lst (tbf :tbf)
	   :h (^ (all-1 (tbf-data tbf))
		 (consp (tbf-data tbf))
		 (posp (tbf-bkt tbf))) ;; could be any positive number, even just 1.
	   (let ((i (1- (len (tbf-data tbf)))))
	     (^ (< i (len (tbf-data tbf)))
		(<= (length (tdg-pld (nth i (tbf-data tbf))))
		    (tbf-bkt tbf))))
	   :hints (("Goal" :use (:instance all-1-works-lst (tdgs (tbf-data tbf))))))

#|
---------- Define "snd 1" transition & its image ----------
|#
(definecd snd-1 (sys :system x :string) :system
  :ic (^ (< (sender-state-cur (system-sender sys))
        (+ (sender-state-hiA (system-sender sys))
           (sender-state-N (system-sender sys))))
     (= (length x) 1))
  ;; Output condition says that snd-1 preserves all-1.
  :oc (if (all-1 (tbf-data (system-s2r sys)))
      (all-1 (tbf-data (system-s2r (snd-1 sys x))))
    t)
  (msets sys
     :s2r (tbf-prc (system-s2r sys) (sender-state-cur (system-sender sys)) x)
     :sender (sender-adv-cur (system-sender sys)))
  :function-contract-hints (("Goal" :in-theory (enable all-1-definition-rule
                               tbf-prc-definition-rule))))

(definecd snd-1-simplified (sm :simplified-model) :simplified-model
  :ic (< (simplified-model-cur sm) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (msets sm
     :chan
     (if (< (len (simplified-model-chan sm)) (simplified-model-d-cap sm))
         (cons (simplified-model-cur sm) (simplified-model-chan sm))
       (simplified-model-chan sm))
     :cur (1+ (simplified-model-cur sm))))

#|
---------- Prove "snd 1" moves thru simplification ----------
|#
(property tdgs->poss-preserves-len (tdgs :tdgs)
  (= (len (tdgs->poss tdgs)) (len tdgs))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
                     |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(encapsulate () (local (in-theory 
  (enable simplify-definition-rule
      snd-1-simplified-definition-rule
      tbf-prc-definition-rule
      snd-1-definition-rule
      tdgs->poss-definition-rule
      |MAP*-*(LAMBDA (D) (TDG-ID D))|
      sender-adv-cur-definition-rule)))

(propertyd snd-1-consts-moves-thru-simplification (sys :system x :string)
       :h (^ (< (sender-state-cur (system-sender sys))
            (+ (sender-state-hiA (system-sender sys))
               (sender-state-N (system-sender sys))))
         (= (length x) 1))
       (^ (= (simplified-model-N (snd-1-simplified (simplify sys)))
         (simplified-model-N (simplify (snd-1 sys x))))
          (= (simplified-model-hiA (snd-1-simplified (simplify sys)))
         (simplified-model-hiA (simplify (snd-1 sys x))))
          (= (simplified-model-cur (snd-1-simplified (simplify sys)))
         (simplified-model-cur (simplify (snd-1 sys x))))
          (= (simplified-model-ack (snd-1-simplified (simplify sys)))
         (simplified-model-ack (simplify (snd-1 sys x))))
          (= (simplified-model-d-cap (snd-1-simplified (simplify sys)))
         (simplified-model-d-cap (simplify (snd-1 sys x))))))

(propertyd snd-1-chan-lhs-simplification (sys :system)
       :h (< (sender-state-cur (system-sender sys))
         (+ (sender-state-hiA (system-sender sys))
            (sender-state-N (system-sender sys))))
       (== (simplified-model-chan (snd-1-simplified (simplify sys)))
           (if (< (len (tdgs->poss (tbf-data (system-s2r sys))))
              (simplified-model-d-cap (simplify sys)))
           (cons (simplified-model-cur (simplify sys))
             (tdgs->poss (tbf-data (system-s2r sys))))
         (tdgs->poss (tbf-data (system-s2r sys))))))

(propertyd sz-len-rule-all-1 (tdgs :tdgs)
       :h (all-1 tdgs)
       (= (sz tdgs) (len tdgs))
       :hints (("Goal" :in-theory (enable sz-definition-rule
                          all-1-definition-rule))))

(propertyd tdgs->poss-cons-step (tdg :tdg tdgs :tdgs)
       (== (tdgs->poss (cons tdg tdgs))
           (cons (tdg-id tdg) (tdgs->poss tdgs)))
       :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
                          |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(propertyd snd-1-chan-moves-thru-simplification (sys :system x :string)
       :h (^ (all-1 (tbf-data (system-s2r sys)))
         (< (sender-state-cur (system-sender sys))
            (+ (sender-state-hia (system-sender sys))
               (sender-state-n (system-sender sys))))
         (= (length x) 1))
       (== (simplified-model-chan (simplify (snd-1 sys x)))
           (simplified-model-chan (snd-1-simplified (simplify sys))))
       :instructions
       ((:use (:instance simplify-definition-rule
                 (sys (snd-1 sys x))))
        (:use (:instance snd-1-definition-rule))
        (:use (:instance tbf-prc-definition-rule
                 (tbf (system-s2r sys))
                 (x (sender-state-cur (system-sender sys)))
                 (pld x)))
        (:in-theory (enable all-1-definition-rule
                sz-definition-rule))
        (:use (:instance sz-len-rule-all-1
                 (tdgs (tbf-data (system-s2r sys)))))
        (:use (:instance snd-1-consts-moves-thru-simplification))
        (:use (:instance snd-1-chan-lhs-simplification))
        (:use (:instance tdgs->poss-preserves-len
                 (tdgs (tbf-data (system-s2r sys)))))
        (:use (:instance tdgs->poss-cons-step
                 (tdg (tdg (sender-state-cur (system-sender sys))
                       (tbf-del (system-s2r sys))
                       x))
                 (tdgs (tbf-data (system-s2r sys)))))
        (:use (:instance simplify-definition-rule))
        :prove))

;; Let sys be a real go-back-n system with sender, tbf_s, receiver, and tbf_r
;; sender--> tbf_s--> receiver -->tbf_r --> sender
;; If I "simplify" the result of having the sender transmit one packet in its window
;; I get the same thing as if I "simplify" the sys and take the simplified sender transmission.
(propertyd snd-1-moves-thru-simplification (sys :system x :string)
       :h (^ (all-1 (tbf-data (system-s2r sys)))
         (< (sender-state-cur (system-sender sys))
            (+ (sender-state-hia (system-sender sys))
               (sender-state-n (system-sender sys))))
         (= (length x) 1))
       (== (simplify (snd-1 sys x)) (snd-1-simplified (simplify sys)))
       :hints (("Goal" :use ((:instance snd-1-consts-moves-thru-simplification)
                 (:instance snd-1-chan-moves-thru-simplification))))))

#|
---------- Define "dlv 1" transition & its image ----------
|#
(propertyd cons-poss (p :pos ps :poss) (possp (cons p ps)))

(propertyd dlv-1-contracts-helper (sys :system) 
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^ (natp (1- (len (tbf-data (system-s2r sys)))))
	      (< (1- (len (tbf-data (system-s2r sys)))) (len (tbf-data (system-s2r sys))))
	      (<= (length (tdg-pld (nth (1- (len (tbf-data (system-s2r sys))))
					(tbf-data (system-s2r sys)))))
		  (tbf-bkt (system-s2r sys)))
	      (tdgp (nth (1- (len (tbf-data (system-s2r sys)))) (tbf-data (system-s2r sys))))
	      (tbfp (tbf-fwd (system-s2r sys) (1- (len (tbf-data (system-s2r sys))))))
	      (posp (tdg-id (nth (1- (len (tbf-data (system-s2r sys)))) (tbf-data (system-s2r sys)))))
	      (possp (system-receiver sys))
	      (boolp (cumackp (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
					   (tbf-data (system-s2r sys))))
			      (system-receiver sys)))
	      (possp (cons (tdg-id (nth (1- (len (tbf-data (system-s2r sys)))) (tbf-data (system-s2r sys))))
			   (system-receiver sys))))
	   :hints (("Goal" :use
		    ((:instance all-1=>1-tkn-to-dlv-lst (tbf (system-s2r sys)))
		     (:instance cons-poss (p (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
							  (tbf-data (system-s2r sys)))))
				(ps (system-receiver sys)))))))

(propertyd take-all-but-last-is-remove-last (ps :poss)
  :h (consp ps)
  (== (remove-ith ps (1- (len ps)))
      (take (1- (len ps)) ps))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(definecd dlv-1 (sys :system) :system
  :ic (^ (all-1 (tbf-data (system-s2r sys)))
	 (posp (tbf-bkt (system-s2r sys)))
	 (consp (tbf-data (system-s2r sys))))
  (let* ((i (1- (len (tbf-data (system-s2r sys)))))
	 (id (tdg-id (nth i (tbf-data (system-s2r sys)))))
	 (s2r (tbf-fwd (system-s2r sys) i))
	 (rcv (if (cumackp id (system-receiver sys))
		  (cons id (system-receiver sys))
		(system-receiver sys))))
    (msets sys :s2r s2r :receiver rcv))
  :function-contract-hints (("Goal" :use (:instance dlv-1-contracts-helper)))
  :body-contracts-hints (("Goal" :use (:instance dlv-1-contracts-helper))))

(propertyd remove-ith-preserves-possp (ps :poss i :nat)
	   :h (< i (len ps))
	   (possp (remove-ith ps i))
	   :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd dlv-1-simplified-contracts-helper (sm :simplified-model)
	   :h (consp (simplified-model-chan sm))
	   (^ (natp (1- (len (simplified-model-chan sm))))
	      (< (1- (len (simplified-model-chan sm)))
		 (len (simplified-model-chan sm)))
	      (possp (remove-ith (simplified-model-chan sm)
				 (1- (len (simplified-model-chan sm)))))
	      (posp (if (= (1+ (simplified-model-ack sm))
			   (nth (1- (len (simplified-model-chan sm)))
				(simplified-model-chan sm)))
			(nth (1- (len (simplified-model-chan sm)))
			     (simplified-model-chan sm))
		      (simplified-model-ack sm)))
	      (simplified-modelp
	       (msets sm :chan (remove-ith (simplified-model-chan sm)
					   (1- (len (simplified-model-chan sm))))
		      :ack (if (= (1+ (simplified-model-ack sm))
				  (nth (1- (len (simplified-model-chan sm)))
				       (simplified-model-chan sm)))
			       (nth (1- (len (simplified-model-chan sm)))
				    (simplified-model-chan sm))
			     (simplified-model-ack sm)))))
	   :hints (("Goal" :use (:instance remove-ith-preserves-possp
					   (ps (simplified-model-chan sm))
					   (i (1- (len (simplified-model-chan sm))))))))

(definecd dlv-1-simplified (sm :simplified-model) :simplified-model
  :ic (consp (simplified-model-chan sm))
  ;; These output contracts form a portion of our simplification proof for dlv-1.
  :oc (^ (= (simplified-model-d-cap (dlv-1-simplified sm))
	    (simplified-model-d-cap sm))
	 (= (simplified-model-N (dlv-1-simplified sm))
	    (simplified-model-N sm))
	 (= (simplified-model-hiA (dlv-1-simplified sm))
	    (simplified-model-hiA sm))
	 (= (simplified-model-cur (dlv-1-simplified sm))
	    (simplified-model-cur sm))
	 (= (len (simplified-model-chan (dlv-1-simplified sm)))
	    (1- (len (simplified-model-chan sm))))
	 (== (simplified-model-chan (dlv-1-simplified sm))
	     (take (1- (len (simplified-model-chan sm)))
		   (simplified-model-chan sm)))
	 (= (simplified-model-ack (dlv-1-simplified sm))
	    (if (= (simplified-model-ack sm)
		   (nth (1- (len (simplified-model-chan sm)))
			(simplified-model-chan sm)))
		(1+ (simplified-model-ack sm))
	      (simplified-model-ack sm))))
  (msets sm :chan (remove-ith (simplified-model-chan sm)
			      (1- (len (simplified-model-chan sm))))
	 :ack (if (= (simplified-model-ack sm)
		     (nth (1- (len (simplified-model-chan sm)))
			  (simplified-model-chan sm)))
		  (1+ (nth (1- (len (simplified-model-chan sm)))
			   (simplified-model-chan sm)))
		(simplified-model-ack sm)))
  :function-contract-hints (("Goal" :use ((:instance dlv-1-simplified-contracts-helper)
					  (:instance take-all-but-last-is-remove-last
						     (ps (simplified-model-chan sm))))))
  :body-contracts-hints (("Goal" :use ((:instance dlv-1-simplified-contracts-helper)
				       (:instance take-all-but-last-is-remove-last
						  (ps (simplified-model-chan sm)))))))

;; This property will be useful later when we try to characterize dlv-b-simplified.
(propertyd dlv-1-simplified-prefix-postfix-helper (sm :simplified-model prefix postfix :poss)
	   :h (^ (consp postfix) (== (simplified-model-chan sm) (append prefix postfix)))
	   (== (simplified-model-chan (dlv-1-simplified sm))
	       (append prefix (take (1- (len postfix)) postfix)))
	   :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
					      take-all-but-last-is-remove-last
					      remove-ith-definition-rule))))
                          
             
#|
---------- Prove "dlv 1" moves thru simplification ----------
Important caveat: We will ignore the bucket in the simplification.
However, later, I will prove that this is acceptable.
Here is the proof sketch.

(simplify (dlv-1 sys)) does 2 things.
1. Update chan/s2r.
2. Update ack/receiver.
We need to prove equivalence for each.  Let's start with (1) the chan.
|#
(propertyd dlv-1-s2r (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (== (tbf-data (system-s2r (dlv-1 sys)))
	       (remove-ith (tbf-data (system-s2r sys))
			   (1- (len (tbf-data (system-s2r sys))))))
	   :hints (("Goal" :in-theory (enable dlv-1-definition-rule
					      tbf-fwd-definition-rule)
		    :use (:instance dlv-1-contracts-helper))))

(propertyd dlv-1-s2r-simplified (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^
	    (natp (1- (len (tbf-data (system-s2r sys)))))
	    (< (1- (len (tbf-data (system-s2r sys))))
	       (len (tbf-data (system-s2r sys))))
	    (== (simplified-model-chan (simplify (dlv-1 sys)))
		(tdgs->poss (remove-ith (tbf-data (system-s2r sys))
					(1- (len (tbf-data (system-s2r sys))))))))
	   :hints (("Goal" :use (:instance dlv-1-s2r)
		    :in-theory (enable simplify-definition-rule))))

(definecd tdgs-remove-ith-to-poss-inductor (tdgs :tdgs i :nat) :nat
  :ic (< i (len tdgs))
  (if (= i 0) 0 (tdgs-remove-ith-to-poss-inductor (cdr tdgs) (1- i))))

(propertyd tdgs-remove-ith-to-poss (tdgs :tdgs i :nat)
	   :h (< i (len tdgs))
	   (== (tdgs->poss (remove-ith tdgs i)) (remove-ith (tdgs->poss tdgs) i))
	   :instructions
	   ((:in-theory (enable tdgs->poss-definition-rule
				|MAP*-*(LAMBDA (D) (TDG-ID D))|
				remove-ith-definition-rule))
	    (:use (:instance tdgs->poss-preserves-len))
	    :prove))

(propertyd dlv-1-simplified-chan (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^
	    ;; contracts
	    (natp (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys))))))
	    (< (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys)))))
	       (len (tdgs->poss (tbf-data (system-s2r sys)))))
	    (consp (simplified-model-chan (simplify sys)))
	    (simplified-modelp (dlv-1-simplified (simplify sys)))
	    ;; thm below
	    (== (simplified-model-chan (dlv-1-simplified (simplify sys)))
		(remove-ith (tdgs->poss (tbf-data (system-s2r sys)))
			    (1- (len (tdgs->poss (tbf-data (system-s2r sys))))))))
	   :instructions
	   ((:use (:instance simplify-definition-rule))
	    (:use (:instance dlv-1-simplified-definition-rule
			     (sm (simplify sys))))
	    (:use (:instance tdgs->poss-preserves-len
			     (tdgs (tbf-data (system-s2r sys)))))
	    :pro
	    (:claim (consp (tdgs->poss (tbf-data (system-s2r sys)))))
	    
	    :prove))

(propertyd dlv-1-chan-eq (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^
	    ;; contracts
	    (natp (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys))))))
	    (< (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys)))))
	       (len (tdgs->poss (tbf-data (system-s2r sys)))))
	    (consp (simplified-model-chan (simplify sys)))
	    (simplified-modelp (dlv-1-simplified (simplify sys)))
	    ;; thm below
	    (== (simplified-model-chan (simplify (dlv-1 sys)))
		(simplified-model-chan (dlv-1-simplified (simplify sys)))))
	   :hints (("Goal" :use ((:instance tdgs->poss-preserves-len
					    (tdgs (tbf-data (system-s2r sys))))
				 (:instance (:instance tdgs-remove-ith-to-poss
						       (tdgs (tbf-data (system-s2r sys)))
						       (i (1- (len (tbf-data (system-s2r sys)))))))
				 (:instance dlv-1-s2r-simplified)
				 (:instance dlv-1-simplified-chan)))))


;; ------------------ Now we can handle (2) ack. ------------------ 

(propertyd dlv-1-ack-lhs-1 (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^
	    ;; contracts
	    (natp (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys))))))
	    (< (+ -1 (len (tdgs->poss (tbf-data (system-s2r sys)))))
	       (len (tdgs->poss (tbf-data (system-s2r sys)))))
	    (consp (simplified-model-chan (simplify sys)))
	    (simplified-modelp (dlv-1-simplified (simplify sys)))
	    ;; thm below
	    (= (simplified-model-ack (simplify (dlv-1 sys)))
	       (1+ (maxl (if (cumackp (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
						   (tbf-data (system-s2r sys))))
				      (system-receiver sys))
			     (cons (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
						(tbf-data (system-s2r sys))))
				   (system-receiver sys))
			   (system-receiver sys))))))
	   :hints (("Goal" :use ((:instance dlv-1-chan-eq)
				 (:instance dlv-1-definition-rule)
				 (:instance simplify-definition-rule
					    (sys (dlv-1 sys)))))))

(definecd top-dn (top :pos rem :nat) :poss
  :ic (<= rem top)
  (cond
   ((= rem 0) nil)
   ((= rem 1) (list top))
   (t (cons top (top-dn (1- top) (1- rem))))))

(check= (top-dn 4 2) '(4 3))
(check= (top-dn 6 6) '(6 5 4 3 2 1))
(check= (top-dn 99 0) nil)

(propertyd maxl-top-dn-top=top (top :pos)
	   (= (maxl (top-dn top top)) top)
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule
					      maxl-definition-rule))))

(propertyd top-dn-doesnt-go-up (top x :pos rem :nat)
	   :h (^ (< top x) (<= rem top))
	   (! (in x (top-dn top rem)))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(propertyd 1+maxl-not-in-top-dn-top (top :pos)
	   (! (in (1+ (maxl (top-dn top top)))
		  (top-dn top top)))
	   :hints (("Goal" :use ((:instance top-dn-doesnt-go-up (x (1+ top)) (rem top))
				 (:instance maxl-top-dn-top=top)))))

(propertyd has-all-cdr (p :pos ps :poss)
	   :h (has-all p (cdr ps))
	   (has-all p ps)
	   :hints (("Goal" :in-theory (enable has-all-definition-rule))))

#|
(has-all top (top-dn top top))
=
(has-all top (cons top (top-dn (1- top) (1- top))))
=
(^ (in top (cons top (top-dn (1- top) (1- top))))
   (has-all (1- top) (cons top (top-dn (1- top) (1- top)))))
<-
(^ (in top (cons top (top-dn (1- top) (1- top))))
   (has-all (1- top) (top-dn (1- top) (1- top))))
qed.
|#
(definecd has-all-top-dn-top-inductor (top :pos) :pos
  (if (= top 1) top (has-all-top-dn-top-inductor (1- top))))

(propertyd has-all-top-dn-top (top :pos)
	   (has-all top (top-dn top top))
	   :hints (("Goal" :induct (has-all-top-dn-top-inductor top)
		    :in-theory (enable has-all-cdr
				       top-dn-definition-rule
				       has-all-definition-rule))))

;; This is the crux of the argument for the refinement to just use ack.
(propertyd cumackp-1+maxl-top-dn-top (top :pos)
	   (cumackp (1+ (maxl (top-dn top top))) (top-dn top top))
	   :hints (("Goal" :use ((:instance cumackp-definition-rule
					    (a (1+ (maxl (top-dn top top))))
					    (ps (top-dn top top)))
				 (:instance has-all-top-dn-top)
				 (:instance 1+maxl-not-in-top-dn-top)
				 (:instance maxl-top-dn-top=top)))))

(propertyd cumackp-nil (p :pos)
	   (iff (cumackp p nil) (= p 1))
	   :hints (("Goal" :in-theory (enable cumackp-definition-rule
					      has-all-definition-rule))))

;; Case where receiver = nil.
(encapsulate () (local (in-theory (enable all-1-definition-rule
					  sz-definition-rule
					  tdgs->poss-definition-rule
					  |MAP*-*(LAMBDA (D) (TDG-ID D))|
					  cumackp-definition-rule
					  has-all-definition-rule)))
	     
	     (propertyd dlv-1-ack-lem1-base (sys :system)
			:h (^ (endp (system-receiver sys))
			      (all-1 (tbf-data (system-s2r sys)))
			      (posp (tbf-bkt (system-s2r sys)))
			      (consp (tbf-data (system-s2r sys))))
			(^ (natp (+ -1 (len (tbf-data (system-s2r sys)))))
			   (tdgp (nth (+ -1 (len (tbf-data (system-s2r sys))))
				      (tbf-data (system-s2r sys))))
			   (iff (cumackp (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
						      (tbf-data (system-s2r sys))))
					 (system-receiver sys))
				(= (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
						(tbf-data (system-s2r sys))))
				   1)))
			:hints (("Goal" :use ((:instance dlv-1-contracts-helper)
					      (:instance cumackp-nil
							 (p (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
									 (tbf-data (system-s2r sys)))))))
				 :in-theory (disable all-1-definition-rule
						     sz-definition-rule
						     tdgs->poss-definition-rule
						     |MAP*-*(LAMBDA (D) (TDG-ID D))|
						     cumackp-definition-rule
						     has-all-definition-rule)))))

(propertyd maxl-nonempty-pos (ps :poss)
	   :h (! (endp ps))
	   (posp (maxl ps))
	   :hints (("Goal" :in-theory (enable maxl-definition-rule))))

(propertyd maxl-top-dn-top-top-reduction (top :pos)
	   (= (maxl (top-dn top top)) top)
	   :hints (("Goal" :in-theory (enable maxl-definition-rule
					      top-dn-definition-rule))))

(defthm dlv-1-ack-lem1-ind-step
  (=> (^ (systemp sys)
         (consp (system-receiver sys))
         (all-1 (tbf-data (system-s2r sys)))
         (posp (tbf-bkt (system-s2r sys)))
         (consp (tbf-data (system-s2r sys)))
         (== (system-receiver sys)
             (top-dn (maxl (system-receiver sys))
                     (maxl (system-receiver sys)))))
      (iff (cumackp (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
                                 (tbf-data (system-s2r sys))))
                    (system-receiver sys))
           (= (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
                           (tbf-data (system-s2r sys))))
              (1+ (maxl (system-receiver sys))))))
  :instructions
  ((:use (:instance cumackp-1+maxl-top-dn-top
                    (top (maxl (system-receiver sys)))))
   (:use (:instance maxl-nonempty-pos (ps (system-receiver sys))))
   (:use (:instance maxl-top-dn-top-top-reduction (top (maxl (system-receiver sys)))))
   (:use (:instance cumack-is-unique
                    (a0 (+ 1
                           (maxl (top-dn (maxl (system-receiver sys))
                                         (maxl (system-receiver sys))))))
                    (a1 (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
                                     (tbf-data (system-s2r sys)))))
                    (ps (system-receiver sys))))
   :pro
   (:casesplit (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
                                     (tbf-data (system-s2r sys))))
                        (system-receiver sys)))
   (:use (:instance dlv-1-contracts-helper))
   :prove :prove))

(in-theory (disable dlv-1-ack-lem1-ind-step))

(propertyd simplify-nth-tdgs->poss (tdgs :tdgs i :nat)
	   :h (< i (len tdgs))
	   (= (nth i (tdgs->poss tdgs))
	      (tdg-id (nth i tdgs)))
	   :hints (("Goal" :in-theory (enable simplify-definition-rule
					      tdgs->poss-definition-rule
					      |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(encapsulate () (local (in-theory (enable simplify-definition-rule
					  tdgs->poss-definition-rule
					  |MAP*-*(LAMBDA (D) (TDG-ID D))|
					  maxl-definition-rule
					  maxl-nonempty-pos)))
	     (propertyd simplify-nth-in-chan (sys :system)
			:h (consp (tbf-data (system-s2r sys)))
			(^ ;; contracts
			 (natp (+ -1 (len (tbf-data (system-s2r sys)))))
			 (tdgp (nth (+ -1 (len (tbf-data (system-s2r sys))))
				    (tbf-data (system-s2r sys))))
			 (posp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
					    (tbf-data (system-s2r sys)))))
			 (natp (+ -1
				  (len (simplified-model-chan (simplify sys)))))
			 (posp (nth (+ -1
				       (len (simplified-model-chan (simplify sys))))
				    (simplified-model-chan (simplify sys))))
			 ;; thm below
			 (= (nth (1- (len (simplified-model-chan (simplify sys))))
				 (simplified-model-chan (simplify sys)))
			    (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
					 (tbf-data (system-s2r sys))))))
			:instructions
			((:use (:instance tdgs->poss-preserves-len
					  (tdgs (tbf-data (system-s2r sys)))))
			 (:use (:instance simplify-nth-tdgs->poss
					  (tdgs (tbf-data (system-s2r sys)))
					  (i (1- (len (simplified-model-chan (simplify sys)))))))
			 (:use (:instance simplify-definition-rule))
			 :pro
			 (:claim (== (simplified-model-chan (simplify sys))
				     (tdgs->poss (tbf-data (system-s2r sys)))))
			 :prove)))

(defthm dlv-1-ack-lem1-unified-step
  (=> (^ (systemp sys)
	 (all-1 (tbf-data (system-s2r sys)))
	 (posp (tbf-bkt (system-s2r sys)))
	 (consp (tbf-data (system-s2r sys)))
	 (== (system-receiver sys)
	     (if (endp (system-receiver sys))
		 nil
	       (top-dn (maxl (system-receiver sys))
		       (maxl (system-receiver sys))))))
      (iff (cumackp (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
				 (tbf-data (system-s2r sys))))
		    (system-receiver sys))
	   (= (tdg-id (nth (1- (len (tbf-data (system-s2r sys))))
			   (tbf-data (system-s2r sys))))
	      (1+ (maxl (system-receiver sys))))))
  :instructions ((:use (:instance dlv-1-ack-lem1-base))
		 (:use (:instance dlv-1-ack-lem1-ind-step))
		 :prove))

#|
Proof Sketch: 

By { dlv-1-ack-lhs-1 } there are two cases.  (A) where cumack holds, (B) where it does not.

By { dlv-1-ack-lem1-unified-step }, these cases are isomorphic to whether the value is ack + 1, or not.

So in general, these cases are isomorphic to whether the value is ack + 1, or not.

Now we tie "the value" to "the value in the channel" according to { simplify-nth-in-chan }.

The resulting formula should simplify by { simplify-definition-rule } and { dlv-1-simplified-definition-rule }
to the expected outcome.
|#
(defthm dlv-1-ack-eq
  (=> (^ (systemp sys)
	 (all-1 (tbf-data (system-s2r sys)))
	 (posp (tbf-bkt (system-s2r sys)))
	 (consp (tbf-data (system-s2r sys)))
	 (if (endp (system-receiver sys)) t
	   (== (system-receiver sys)
	       (top-dn (maxl (system-receiver sys))
		       (maxl (system-receiver sys))))))
      (= (simplified-model-ack (simplify (dlv-1 sys)))
	 (simplified-model-ack (dlv-1-simplified (simplify sys)))))
  :instructions
  ((:use (:instance simplify-definition-rule))
   :pro
   (:claim (= (simplified-model-ack (simplify sys))
	      (+ 1 (maxl (system-receiver sys)))))
   (:claim (== (simplified-model-chan (simplify sys))
	       (tdgs->poss (tbf-data (system-s2r sys)))))
   (:use (:instance dlv-1-simplified-definition-rule
		    (sm (simplify sys))))
   (:use (:instance dlv-1-contracts-helper))
   (:use (:instance tdgs->poss-preserves-len
		    (tdgs (tbf-data (system-s2r sys)))))
   (:use (:instance simplify-nth-in-chan))
   (:use (:instance dlv-1-ack-lhs-1))
   (:use (:instance dlv-1-ack-lem1-unified-step))
   (:in-theory (enable maxl-definition-rule))
   :prove))

(propertyd dlv-1-doesnt-change-d-cap-or-sender (sys :system)
	   :h (^ (all-1 (tbf-data (system-s2r sys)))
		 (posp (tbf-bkt (system-s2r sys)))
		 (consp (tbf-data (system-s2r sys))))
	   (^ (= (tbf-d-cap (system-s2r (dlv-1 sys)))
		 (tbf-d-cap (system-s2r sys)))
	      (== (system-sender (dlv-1 sys))
		  (system-sender sys)))
	   :hints (("Goal" :use ((:instance dlv-1-definition-rule)
				 (:instance tbf-fwd-definition-rule
					    (tbf (system-s2r sys))
					    (i (1- (len (tbf-data (system-s2r sys))))))
				 (:instance dlv-1-contracts-helper)))))

(defthm dlv-1-moves-thru-simplification
  (=> (^ (systemp sys)
         (all-1 (tbf-data (system-s2r sys)))
         (posp (tbf-bkt (system-s2r sys)))
         (consp (tbf-data (system-s2r sys)))
         (if (endp (system-receiver sys))
             t
           (== (system-receiver sys)
               (top-dn (maxl (system-receiver sys))
                       (maxl (system-receiver sys))))))
      (== (simplify (dlv-1 sys))
          (dlv-1-simplified (simplify sys))))
  :instructions
  ((:use (:instance dlv-1-doesnt-change-d-cap-or-sender))
   (:use (:instance dlv-1-ack-eq))
   (:use (:instance dlv-1-chan-eq))
   (:use (:instance dlv-1-definition-rule))
   (:use (:instance simplify-definition-rule
                    (sys (dlv-1 sys))))
   (:use (:instance simplify-definition-rule))
   (:use (:instance dlv-1-simplified-definition-rule
                    (sm (simplify sys))))
   (:use (:instance tdgs->poss-preserves-len
                    (tdgs (tbf-data (system-s2r sys)))))
   :pro
   (:claim (== (simplified-model-chan (simplify sys))
               (tdgs->poss (tbf-data (system-s2r sys)))))
   :prove))

(in-theory (disable dlv-1-moves-thru-simplification))

;; Note, we proved the relation between cumack and the top-dn invariant previously.
;; Since we check the cumack condition before consing onto receiver, this clearly
;; implies that the top-dn invariant is preserved.  We could prove this later, once
;; everything else is done, but it should be pretty clear already from the theorems
;; we have.

#|
---------- Define "snd-r-simplified" and characterize what it does to chan -----------
|#
(definecd snd-R-simplified (sm :simplified-model R :nat) :simplified-model
  :ic (<= (+ (simplified-model-cur sm) R)
      (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (if (= R 0) sm (snd-R-simplified (snd-1-simplified sm) (1- R)))
  :body-contracts-hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

;; Claim that snd-R-simplified and snd-1-simplified commute.
(definecd snd-R-simplify-inductor (sys :system R :nat) :nat
  (if (= R 0) 0 (1+ (snd-R-simplify-inductor sys (1- R)))))

(propertyd snd-R-1-simplified-contracts (sm :simplified-model R :nat)
	   :h (<= (+ (simplified-model-cur sm) (1+ R))
		  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	   (<= (simplified-model-cur (snd-r-simplified sm R))
	       (+ (simplified-model-hia (snd-r-simplified sm R))
		  (simplified-model-n (snd-r-simplified sm R))))
	   :hints (("Goal" :in-theory (enable snd-r-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

(propertyd snd-R-1-simplified-inductor-contracts (sm :simplified-model R :nat)
	   :h (<= (+ (simplified-model-cur sm) (1+ R))
		  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	   (if (= R 0) t
	     (^ (<= (simplified-model-cur sm)
		    (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		(<= (+ (simplified-model-cur (snd-1-simplified sm)) R)
		    (+ (simplified-model-hiA (snd-1-simplified sm))
		       (simplified-model-N (snd-1-simplified sm))))
		(natp (1- R))))
	   :hints (("Goal" :use (:instance snd-R-1-simplified-contracts)
		    :in-theory (enable snd-1-simplified-definition-rule
				       snd-R-simplified-definition-rule))))

(definecd snd-R-1-simplified-inductor (sm :simplified-model R :nat) :nat
  :ic (<= (+ (simplified-model-cur sm) (1+ R))
	  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (if (= R 0) 0 (snd-R-1-simplified-inductor (snd-1-simplified sm) (1- R)))
  :body-contracts-hints (("Goal" :use (:instance snd-R-1-simplified-inductor-contracts)
			  :in-theory (enable snd-1-simplified-definition-rule))))

(propertyd snd-R-1-simplified-commutes-wrapped-contracts (sm :simplified-model R :nat)
	   :h (<= (+ (simplified-model-cur sm) (1+ R))
		  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	   (^ (<= (+ (simplified-model-cur (snd-1-simplified sm)) R)
		  (+ (simplified-model-hiA (snd-1-simplified sm))
		     (simplified-model-N (snd-1-simplified sm))))
	      (< (simplified-model-cur (snd-R-simplified sm R))
		 (+ (simplified-model-hiA (snd-R-simplified sm R))
		    (simplified-model-N (snd-R-simplified sm R)))))
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

;; Note sure why but currently having issues with the body contracts for this one.
(definecd snd-R-1-simplified-commutes-wrapped (sm :simplified-model R :nat) :bool
  :ic (<= (+ (simplified-model-cur sm) (1+ R))
	  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (== (snd-R-simplified (snd-1-simplified sm) R)
      (snd-1-simplified (snd-R-simplified sm R)))
  :body-contracts-hints (("Goal" :use (:instance snd-R-1-simplified-commutes-wrapped-contracts))))
  
(propertyd snd-r-1-simplified-commutes (sm :simplified-model R :nat)
	   :h (<= (+ (simplified-model-cur sm) (1+ R))
		  (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	   (snd-R-1-simplified-commutes-wrapped sm R)
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule
					      snd-R-1-simplified-commutes-wrapped-definition-rule)
		    :induct (snd-R-1-simplified-inductor sm R))))

(definecd snd-r-simplified-effect-filling-inductor (sm :simplified-model R :nat) :nat
  :ic (^ (<= (+ (simplified-model-cur sm) R)
	     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
  (if (= R 0) 0
    (1+ (snd-r-simplified-effect-filling-inductor (snd-1-simplified sm) (1- R))))
  :body-contracts-hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

(propertyd snd-r-doesnt-change-consts (sm :simplified-model R :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (^ (= (simplified-model-d-cap (snd-R-simplified sm R)) (simplified-model-d-cap sm))
	      (= (simplified-model-ack (snd-R-simplified sm R)) (simplified-model-ack sm))
	      (= (simplified-model-hiA (snd-R-simplified sm R)) (simplified-model-hiA sm))
	      (= (simplified-model-N (snd-R-simplified sm R)) (simplified-model-N sm)))
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

(propertyd snd-r-simplified-cur (sm :simplified-model R :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (= (simplified-model-cur (snd-r-simplified sm R))
	      (+ (simplified-model-cur sm) R))
	   :hints (("Goal" :induct (snd-r-simplified-effect-filling-inductor sm r)
		    :in-theory (enable snd-r-simplified-definition-rule
				       snd-r-simplified-definition-rule
				       snd-1-simplified-definition-rule
				       snd-r-1-simplified-commutes-wrapped-definition-rule))))

(check= (append (top-dn (+ 3 8) 8) (top-dn 3 2)) '(11 10 9 8 7 6 5 4 3 2))
(check= (top-dn (+ 3 8) (+ 8 2)) '(11 10 9 8 7 6 5 4 3 2))

#|
Show that snd-r moves through simplification.
|#
(propertyd snd-r-contracts (sys :system R :pos)
	   :h (<= (+ (sender-state-cur (system-sender sys))
		     r)
		  (+ (sender-state-hia (system-sender sys))
		     (sender-state-n (system-sender sys))))
	   (^ (< (sender-state-cur (system-sender sys))
		 (+ (sender-state-hia (system-sender sys))
		    (sender-state-n (system-sender sys))))
	      (= (length "p") 1)
	      (<= (+ (sender-state-cur (system-sender (snd-1 sys "p")))
		     (1- r))
		  (+ (sender-state-hia (system-sender (snd-1 sys "p")))
		     (sender-state-n (system-sender (snd-1 sys "p"))))))
	   :hints (("Goal" :in-theory (enable tbf-prc-definition-rule
					      snd-1-definition-rule
					      sender-adv-cur-definition-rule))))

(definecd snd-r (sys :system R :nat) :system
  :ic (<= (+ (sender-state-cur (system-sender sys)) R)
	  (+ (sender-state-hiA (system-sender sys))
	     (sender-state-N (system-sender sys))))
  (if (= R 0) sys (snd-r (snd-1 sys "p") (1- R)))
  :body-contracts-hints (("Goal" :use (:instance snd-r-contracts))))

(definecd snd-r-inductor (sys :system R :nat) :nat
  :ic (<= (+ (sender-state-cur (system-sender sys)) R)
	  (+ (sender-state-hiA (system-sender sys))
	     (sender-state-N (system-sender sys))))
  (if (= R 0) 0 (snd-r-inductor (snd-1 sys "p") (1- R)))
  :body-contracts-hints (("Goal" :use (:instance snd-r-contracts))))

;; Lift the snd-1 result to snd-R.
(defthm snd-r-moves-thru-simplification
  (=> (^ (systemp sys)
	 (natp r)
	 (<= (+ (sender-state-cur (system-sender sys))
		r)
	     (+ (sender-state-hia (system-sender sys))
		(sender-state-n (system-sender sys))))
	 (all-1 (tbf-data (system-s2r sys))))
      (== (snd-r-simplified (simplify sys) r)
	  (simplify (snd-r sys r))))
  :instructions
  ((:induct (snd-r-inductor sys r))
   :change-goal
   (:in-theory (enable snd-r-definition-rule
		       snd-r-simplified-definition-rule
		       simplify-definition-rule))
   :prove :pro
   (:in-theory (enable snd-1-definition-rule
		       sender-adv-cur-definition-rule))
   (:claim (<= (+ (sender-state-cur (system-sender (snd-1 sys "p")))
		  -1 r)
	       (+ (sender-state-hia (system-sender (snd-1 sys "p")))
		  (sender-state-n (system-sender (snd-1 sys "p"))))))
   (:use (:instance snd-1-definition-rule (x "p")))
   (:use (:instance tbf-prc-definition-rule
		    (tbf (system-s2r sys))
		    (x (sender-state-cur (system-sender sys)))
		    (pld "p")))
   :pro
   (:claim (== (tbf-data (system-s2r (snd-1 sys "p")))
	       (if (<= (+ (sz (tbf-data (system-s2r sys)))
			  (length "p"))
		       (tbf-d-cap (system-s2r sys)))
		   (cons (tdg (sender-state-cur (system-sender sys))
			      (tbf-del (system-s2r sys))
			      "p")
			 (tbf-data (system-s2r sys)))
		 (tbf-data (system-s2r sys)))))
   (:in-theory (enable all-1-definition-rule))
   (:use
    (:instance all-1-definition-rule
	       (tdgs (if (<= (+ (sz (tbf-data (system-s2r sys)))
				(length "p"))
			     (tbf-d-cap (system-s2r sys)))
			 (cons (tdg (sender-state-cur (system-sender sys))
				    (tbf-del (system-s2r sys))
				    "p")
			       (tbf-data (system-s2r sys)))
		       (tbf-data (system-s2r sys))))))
   :pro
   (:claim (all-1 (if (<= (+ (sz (tbf-data (system-s2r sys)))
			     (length "p"))
			  (tbf-d-cap (system-s2r sys)))
		      (cons (tdg (sender-state-cur (system-sender sys))
				 (tbf-del (system-s2r sys))
				 "p")
			    (tbf-data (system-s2r sys)))
		    (tbf-data (system-s2r sys)))))
   (:claim (equal (snd-r-simplified (simplify (snd-1 sys "p"))
				    (+ -1 r))
		  (simplify (snd-r (snd-1 sys "p") (+ -1 r)))))
   (:use (:instance snd-1-moves-thru-simplification
		    (x "p")))
   :pro
   (:claim (equal (simplify (snd-1 sys "p"))
		  (snd-1-simplified (simplify sys))))
   (:use (:instance snd-r-simplified-definition-rule
		    (sm (simplify sys))))
   (:use (:instance simplify-definition-rule))
   :pro
   (:claim (== (snd-r-simplified (simplify sys) r)
	       (snd-r-simplified (snd-1-simplified (simplify sys))
				 (+ -1 r))))
   (:claim (== (snd-r-simplified (simplify sys) r)
	       (snd-r-simplified (simplify (snd-1 sys "p"))
				 (+ -1 r))))
   (:use (:instance snd-r-definition-rule))
   :prove))
                          
(definecd top-dn-append-ind (up :nat mid rem :pos) :nat
  :ic (<= rem mid)
  (if (= up 0) 0 (1+ (top-dn-append-ind (1- up) mid rem))))

(propertyd top-dn-append (up :nat mid rem :pos)
	   :h (<= rem mid)
	   (== (append (top-dn (+ mid up) up) (top-dn mid rem))
	       (top-dn (+ mid up) (+ up rem)))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule)
		    :induct (top-dn-append-ind up mid rem))))

(propertyd snd-1-simplified-chan-effect (sm :simplified-model)
	   :h (^ (< (len (simplified-model-chan sm)) (simplified-model-d-cap sm))
		 (< (simplified-model-cur sm)
		    (+ (simplified-model-hia sm)
		       (simplified-model-n sm))))
	   (== (simplified-model-chan (snd-1-simplified sm))
	       (cons (simplified-model-cur sm) (simplified-model-chan sm)))
	   :hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

;; Suffices to show that snd-1 preserves cumack property when channel isn't full yet.
;; (I have done some proofs about top-dn and cumack elsewhere in this repository ...)
(propertyd snd-1-simplified-chan-effect-when-top-dn (sm :simplified-model)
	   :h (^ (< (len (simplified-model-chan sm)) (simplified-model-d-cap sm))
		 (< (simplified-model-cur sm)
		    (+ (simplified-model-hia sm)
		       (simplified-model-n sm)))
		 (<= (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
		 (< 1 (simplified-model-cur sm))
		 (== (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
							(len (simplified-model-chan sm)))))
	   (== (simplified-model-chan (snd-1-simplified sm))
	       (top-dn (simplified-model-cur sm) (1+ (len (simplified-model-chan sm)))))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule)
		    :use ((:instance snd-1-simplified-chan-effect)
			  (:instance top-dn-append (up 1) (mid (1- (simplified-model-cur sm))))))))

(definecd snd-R-simplified-inductor (sm :simplified-model R :pos) :nat
  (if (= R 1) 0 (1+ (snd-R-simplified-inductor sm (1- R)))))

(property top-dn-len (a :pos b :nat)
  :h (<= a b)
  (= (len (top-dn b a)) a)
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

#|
Theorem: If the channel is full then snd-r does not change the channel.
|#
(propertyd snd-r-does-nothing-when-full (sm :simplified-model R :pos)
	   :h (^ (<= (+ (simplified-model-cur sm) r)
		     (+ (simplified-model-hia sm)
			(simplified-model-n sm)))
		 (= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (== (simplified-model-chan (snd-R-simplified sm R))
	       (simplified-model-chan sm))
	   :instructions
	   ((:in-theory (enable snd-r-simplified-definition-rule
				snd-1-simplified-definition-rule
				snd-r-1-simplified-commutes))
	    (:induct (snd-r-simplified-inductor sm r))
	    (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
			     (r (1- r))))
	    :prove
	    (:use (:instance snd-r-simplified-definition-rule))
	    :prove))

;; Critical invariant which shows that as long as the chan isn't full, snd-r-simplified preserves
;; the top-dn nature of the chan.
(propertyd snd-r-simplified-chan-effect-when-top-dn (sm :simplified-model R :pos)
	   :h (^ (< (1- (+ R (len (simplified-model-chan sm))))
		    (simplified-model-d-cap sm))
		 (<= (+ R (simplified-model-cur sm))
		     (+ (simplified-model-hia sm)
			(simplified-model-n sm)))
		 (<= (len (simplified-model-chan sm))
		     (1- (simplified-model-cur sm)))
		 (< 1 (simplified-model-cur sm))
		 (== (simplified-model-chan sm)
		     (top-dn (1- (simplified-model-cur sm))
			     (len (simplified-model-chan sm)))))
	   (== (simplified-model-chan (snd-R-simplified sm R))
	       (top-dn (1- (+ R (simplified-model-cur sm)))
		       (+ R (len (simplified-model-chan sm)))))
	   :instructions
	   ((:in-theory (enable snd-r-1-simplified-commutes))
	    (:induct (snd-r-simplified-inductor sm r))
	    :change-goal
	    (:in-theory (enable snd-r-simplified-definition-rule
				snd-1-simplified-definition-rule
				top-dn-definition-rule))
	    :prove
	    (:use (:instance snd-r-simplified-definition-rule))
	    (:use (:instance snd-r-1-simplified-commutes (r (1- r))))
	    (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
			     (r (1- r))))
	    (:use (:instance snd-1-simplified-chan-effect-when-top-dn
			     (sm (snd-r-simplified sm (+ -1 r)))))
	    (:use (:instance snd-r-doesnt-change-consts (r (1- r))))
	    (:use (:instance top-dn-len
			     (b (+ -1 (+ -1 r)
				   (simplified-model-cur sm)))
			     (a (+ (+ -1 r)
				   (len (simplified-model-chan sm))))))
	    (:use (:instance snd-r-simplified-cur (r (1- r))))
	    :prove))

(propertyd snd-R-simplified-incrs-len (sm :simplified-model R :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (= (len (simplified-model-chan (snd-R-simplified sm R)))
	      (min (+ (len (simplified-model-chan sm)) R)
		   (simplified-model-d-cap sm)))
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

(propertyd snd-R-simplified-incrs-cur (sm :simplified-model R :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (= (simplified-model-cur (snd-R-simplified sm R))
	      (+ R (simplified-model-cur sm)))
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

(propertyd snd-R-simplified-consts (sm :simplified-model R :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm)))
	   (^ (= (simplified-model-d-cap (snd-R-simplified sm R)) (simplified-model-d-cap sm))
	      (= (simplified-model-ack (snd-R-simplified sm R)) (simplified-model-ack sm))
	      (= (simplified-model-hiA (snd-R-simplified sm R)) (simplified-model-hiA sm))
	      (= (simplified-model-N (snd-R-simplified sm R)) (simplified-model-N sm)))
	   :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
					      snd-1-simplified-definition-rule))))

;; Claim: (snd-r (snd-r sm r0) r1) = (snd-r sm (+ r0 r1))
;; Proof:
;; Induct on r0.
;; Base case: (snd-r (snd-r sm 1) r1) = (snd-r (snd-1 sm 1) r1) = (snd-r sm (1+ r1)) qed.
;; Inductive Step: Suppose (snd-r (snd-r sm r0) r1) = (snd-r sm r0 + r1)
;; Consider (snd-r (snd-r sm r0 + 1) r1)
;; = (snd-r (snd-r (snd-1 sm) r0) r1)
;; = (snd-r (snd-1 (snd-r sm r0)) r1)
;; = (snd-1 (snd-r (snd-r sm r0) r1))
;; = (snd-1 (snd-r sm (+ r0 r1)))
;; = (snd-r sm (1+ r0 r1)) QED.
(definecd snd-r+r-inductor (sm :simplified-model R0 R1 :nat) :nat
  (if (= R0 0) 0 (1+ (snd-r+r-inductor sm (1- R0) R1))))

;; Critical function that says that snd-r commutes with itself.
;; The reason this matters is that if R > the remaining space in the channel, then we
;; can show how it fills the channel for (the remaining space)-amount, after which,
;; it does nothing except for advance cur.
(propertyd snd-r-snd-r=snd-r+r (sm :simplified-model R0 R1 :nat)
	   :h (^ (<= (+ (simplified-model-cur sm) R0 R1)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (<= (len (simplified-model-chan sm))
		     (simplified-model-d-cap sm)))
	   (^ (<= (+ (simplified-model-cur (snd-r-simplified sm r0))
		     r1)
		  (+ (simplified-model-hia (snd-r-simplified sm r0))
		     (simplified-model-n (snd-r-simplified sm r0))))
	      (== (snd-R-simplified (snd-R-simplified sm R0) R1)
		  (snd-R-simplified sm (+ R0 R1))))
	   :instructions
	   ((:use (:instance snd-r-simplified-consts (r r0)))
	    (:use (:instance snd-r-simplified-incrs-cur (r r0)))
	    (:induct (snd-r+r-inductor sm r0 r1))
	    (:use (:instance snd-r-simplified-incrs-cur (r (1- r0))))
	    (:use (:instance snd-r-simplified-consts (r (1- r0))))
	    (:use (:instance snd-r-simplified-definition-rule
			     (r (+ r0 r1))))
	    (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
			     (r (1- (+ r0 r1)))))
	    (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
			     (sm (snd-r-simplified sm (1- r0)))
			     (r r1)))
	    (:in-theory (enable snd-r-1-simplified-commutes
				snd-r-simplified-definition-rule))
	    (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
			     (r (1- r0))))
	    :prove :prove))

#|
---------- Define "dlv-b-simplified" and characterize what it does to chan -----------
|#
(propertyd dlv-1-simplified-decrs-len (sm :simplified-model)
	   :h (consp (simplified-model-chan sm))
	   (= (len (simplified-model-chan (dlv-1-simplified sm)))
	      (1- (len (simplified-model-chan sm))))
	   :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule)
		    :use (:instance remove-ith-sub1
				    (i (1- (len (simplified-model-chan sm))))
				    (ps (simplified-model-chan sm))))))

(propertyd dlv-b-simplified-body-contracts (sm :simplified-model b :pos)
	   :h (<= b (len (simplified-model-chan sm)))
	   (let ((sm (dlv-1-simplified sm)))
	     (<= (1- b) (len (simplified-model-chan sm))))
	   :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
					      remove-ith-definition-rule))))

;; ASSUMPTION: Only ever call with b = b-cap = r_s.
(definecd dlv-b-simplified (sm :simplified-model b :nat) :simplified-model
  :ic (<= b (len (simplified-model-chan sm)))
  (if (= b 0) sm (dlv-b-simplified (dlv-1-simplified sm) (1- b)))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
						    remove-ith-definition-rule))))

(definecd dlv-b-simplified-decrs-inductor (sm :simplified-model b :nat) :nat
  :ic (<= b (len (simplified-model-chan sm)))
  (if (= b 0) 0 (1+ (dlv-b-simplified-decrs-inductor (dlv-1-simplified sm) (1- b))))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule))))

(propertyd dlv-b-simplified-decrs-len (sm :simplified-model b :nat)
	   :h (<= b (len (simplified-model-chan sm)))
	   (= (len (simplified-model-chan (dlv-b-simplified sm b)))
	      (- (len (simplified-model-chan sm)) b))
	   :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule
					      dlv-1-simplified-definition-rule
					      dlv-b-simplified-body-contracts
					      dlv-1-simplified-decrs-len))))

(propertyd dlv-b-1-commute-witness-contracts (sm :simplified-model b :nat)
	   :h (<= (1+ b) (len (simplified-model-chan sm)))
	   (^ (consp (simplified-model-chan sm))
	      (<= b (len (simplified-model-chan (dlv-1-simplified sm))))
	      (<= b (len (simplified-model-chan sm)))
	      (consp (simplified-model-chan (dlv-b-simplified sm b))))
	   :hints (("Goal" :use ((:instance dlv-b-simplified-decrs-len)
				 (:instance dlv-1-simplified-decrs-len)))))

(definecd dlv-b-1-commute-witness (sm :simplified-model b :nat) :bool
  :ic (<= (1+ b) (len (simplified-model-chan sm)))
  (== (dlv-b-simplified (dlv-1-simplified sm) b)
      (dlv-1-simplified (dlv-b-simplified sm b)))
  :body-contracts-hints (("Goal" :use (:instance dlv-b-1-commute-witness-contracts))))

(definecd dlv-b-1-commute-inductor (sm :simplified-model b :nat) :nat
  :ic (<= (1+ b) (len (simplified-model-chan sm)))
  (if (= b 0) 0 (1+ (dlv-b-1-commute-inductor (dlv-1-simplified sm) (1- b))))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
						    dlv-b-simplified-definition-rule
						    remove-ith-definition-rule)
			  :use ((:instance dlv-b-simplified-body-contracts)
				(:instance dlv-b-1-commute-witness-contracts)))))

(check= (take 3 (take 10 '(1 2 3 4 5 6 7 8 9 10 11))) (take 3 '(1 2 3 4 5 6 7 8 9 10 11)))

(propertyd combine-takes (ps :poss i j :nat)
	   :h (^ (< i (len ps)) (< j i))
	   (== (take j (take i ps)) (take j ps)))

(propertyd dlv-b-1-commute (sm :simplified-model b :nat)
	   :h (<= (1+ b) (len (simplified-model-chan sm)))
	   (dlv-b-1-commute-witness sm b)
	   :hints (("Goal" :induct (dlv-b-1-commute-inductor sm b)
		    :in-theory (enable dlv-1-simplified-decrs-len
				       dlv-b-simplified-body-contracts
				       dlv-b-simplified-decrs-len
				       combine-takes
				       take-all-but-last-is-remove-last
				       dlv-b-1-commute-witness-contracts
				       dlv-b-1-commute-witness-definition-rule
				       dlv-1-simplified-definition-rule
				       dlv-b-simplified-definition-rule
				       dlv-b-1-commute-witness-definition-rule))))

;; We want to characterize the effect of dlv-b.
;; The important point is that, if the right-most b elements are all ack, ack + 1, ack + 2, etc.
;; then the effect will be to incr ack by b.
;; On the other hand, if ack isn't in the chan, then it won't do anything.
;; Let's go ahead and prove both of these things.
;; We will also need to show what dlv-b does to the channel (it removes the b things on the right ...).

(definecd dlv-b-simplified-chan-inductor (sm :simplified-model b :pos) :nat
  :ic (<= b (len (simplified-model-chan sm)))
  (if (= b 1) 1 (dlv-b-simplified-chan-inductor sm (1- b))))

(propertyd take-len-rule (x :nat ps :poss)
	   :h (<= x (len ps))
	   (= (len (take x ps)) x))

(propertyd remove-last=take-len-1 (ps :poss)
	   :h (consp ps)
	   (== (remove-ith ps (1- (len ps)))
	       (take (1- (len ps)) ps))
	   :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd remove-last-take=take+1 (x :pos ps :poss)
	   :h (<= x (len ps))
	   (== (remove-ith (take x ps) (1- x))
	       (take (1- x) ps))
	   :hints (("Goal" :use ((:instance remove-last=take-len-1 (ps (take x ps)))
				 (:instance take-len-rule)
				 (:instance combine-takes (i x) (j (1- (1- x))))))))

(propertyd extract-chan (sm :simplified-model a :pos cs :poss)
	   (== (simplified-model-chan (mset :ack a (mset :chan cs sm))) cs))

(propertyd remove-ith-len (ps :poss i :nat)
	   :h (< i (len ps))
	   (== (len (remove-ith ps i)) (1- (len ps)))
	   :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd data-extractor (tbf :tbf D :tdgs bkt :nat)
	   (== (tbf-data (mset :data D (mset :bkt bkt tbf))) D))

(propertyd bkt-extractor (tbf :tbf D :tdgs bkt :nat)
	   (= (tbf-bkt (mset :data D (mset :bkt bkt tbf))) bkt))

(propertyd take-all-but-last-is-remove-last-tdgs (tdgs :tdgs)
	   :h (consp tdgs)
	   (== (remove-ith tdgs (1- (len tdgs)))
	       (take (1- (len tdgs)) tdgs))
	   :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd all-1-implies-all-1 (tdgs :tdgs i :nat)
	   :h (^ (all-1 tdgs) (< i (len tdgs)))
	   (= (length (tdg-pld (nth i tdgs))) 1)
	   :hints (("Goal" :in-theory (enable all-1-definition-rule))))

(propertyd nth-take (tdgs :tdgs i :nat)
	   :h (< (1+ i) (len tdgs))
	   (== (nth i (take (1- (len tdgs)) tdgs))
	       (nth i tdgs)))

(definecd all-1-take-inductor (tdgs :tdgs) :nat
  (match tdgs
    (() 0)
    ((& . rst) (all-1-take-inductor rst))))

(propertyd all-1-take (tdgs :tdgs)
	   :h (^ (all-1 tdgs) (consp tdgs))
	   (all-1 (take (1- (len tdgs)) tdgs))
	   :instructions ((:induct (all-1-take-inductor tdgs))
			  :pro
			  (:in-theory (enable all-1-definition-rule))
			  (:claim (all-1 (take (+ -1 (len (cdr tdgs)))
					       (cdr tdgs))))
			  (:drop 4)
			  (:use (:instance all-1-definition-rule
					   (tdgs (take (+ -1 (len tdgs)) tdgs))))
			  :pro :prove :prove))

(propertyd all-1-remove-ith (tdgs :tdgs)
	   :h (^ (consp tdgs) (all-1 tdgs))
	   (all-1 (remove-ith tdgs (1- (len tdgs))))
	   :hints (("Goal" :in-theory (enable all-1-take
					      take-all-but-last-is-remove-last-tdgs))))

#|
We need to show that dlv-b moves through simplify.
|#
(propertyd dlv-b-contracts (sys :system b :pos)
	   :h (^ (<= (tbf-bkt (system-s2r sys))
		     (len (tbf-data (system-s2r sys))))
		 (all-1 (tbf-data (system-s2r sys)))
		 (= b (tbf-bkt (system-s2r sys))))
	   (^ (posp (tbf-bkt (system-s2r sys)))
	      (consp (tbf-data (system-s2r sys)))
	      (= (len (tbf-data (system-s2r (dlv-1 sys))))
		 (1- (len (tbf-data (system-s2r sys)))))
	      (= (tbf-bkt (system-s2r (dlv-1 sys)))
		 (1- (tbf-bkt (system-s2r sys))))
	      (<= (tbf-bkt (system-s2r (dlv-1 sys)))
		  (len (tbf-data (system-s2r (dlv-1 sys)))))
	      (all-1 (tbf-data (system-s2r (dlv-1 sys)))))
	   
	   :instructions
	   ((:use (:instance dlv-1-definition-rule))
	    :pro
	    (:claim (== (system-s2r (dlv-1 sys))
			(tbf-fwd (system-s2r sys)
				 (+ -1 (len (tbf-data (system-s2r sys)))))))
	    (:use (:instance tbf-fwd-definition-rule
			     (tbf (system-s2r sys))
			     (i (+ -1 (len (tbf-data (system-s2r sys)))))))
	    (:use (:instance all-1-works-lst
			     (tdgs (tbf-data (system-s2r sys)))))
	    (:use
	     (:instance
	      data-extractor (tbf (system-s2r sys))
	      (d (remove-ith (tbf-data (system-s2r sys))
			     (+ -1 (len (tbf-data (system-s2r sys))))))
	      (bkt (+ (tbf-bkt (system-s2r sys))
		      (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					       (tbf-data (system-s2r sys))))))))))
	    :pro
	    (:claim
	     (equal
	      (tbf-fwd (system-s2r sys)
		       (+ -1 (len (tbf-data (system-s2r sys)))))
	      (mset
	       :data
	       (remove-ith (tbf-data (system-s2r sys))
			   (+ -1 (len (tbf-data (system-s2r sys)))))
	       (mset
		:bkt
		(+ (tbf-bkt (system-s2r sys))
		   (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					    (tbf-data (system-s2r sys)))))))
		(system-s2r sys)))))
	    (:claim
	     (natp (+ (tbf-bkt (system-s2r sys))
		      (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					       (tbf-data (system-s2r sys)))))))))
	    (:claim (tdgsp (remove-ith (tbf-data (system-s2r sys))
				       (+ -1 (len (tbf-data (system-s2r sys)))))))
	    (:claim (tbfp (system-s2r sys)))
	    (:claim
	     (equal
	      (tbf-data
	       (mset
		:data
		(remove-ith (tbf-data (system-s2r sys))
			    (+ -1 (len (tbf-data (system-s2r sys)))))
		(mset
		 :bkt
		 (+ (tbf-bkt (system-s2r sys))
		    (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					     (tbf-data (system-s2r sys)))))))
		 (system-s2r sys))))
	      (remove-ith (tbf-data (system-s2r sys))
			  (+ -1 (len (tbf-data (system-s2r sys)))))))
	    (:claim (== (tbf-data (system-s2r (dlv-1 sys)))
			(remove-ith (tbf-data (system-s2r sys))
				    (+ -1 (len (tbf-data (system-s2r sys)))))))
	    (:use
	     (:instance
	      bkt-extractor (tbf (system-s2r sys))
	      (d (remove-ith (tbf-data (system-s2r sys))
			     (+ -1 (len (tbf-data (system-s2r sys))))))
	      (bkt (+ (tbf-bkt (system-s2r sys))
		      (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					       (tbf-data (system-s2r sys))))))))))
	    :pro
	    (:claim
	     (=
	      (tbf-bkt
	       (mset
		:data
		(remove-ith (tbf-data (system-s2r sys))
			    (+ -1 (len (tbf-data (system-s2r sys)))))
		(mset
		 :bkt
		 (+ (tbf-bkt (system-s2r sys))
		    (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					     (tbf-data (system-s2r sys)))))))
		 (system-s2r sys))))
	      (+ (tbf-bkt (system-s2r sys))
		 (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					  (tbf-data (system-s2r sys)))))))))
	    (:claim
	     (= (tbf-bkt (tbf-fwd (system-s2r sys)
				  (+ -1 (len (tbf-data (system-s2r sys))))))
		(+ (tbf-bkt (system-s2r sys))
		   (- (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
					    (tbf-data (system-s2r sys)))))))))
	    (:claim (= (tbf-bkt (system-s2r (dlv-1 sys)))
		       (1- (tbf-bkt (system-s2r sys)))))
	    (:claim (= (len (tbf-data (system-s2r (dlv-1 sys))))
		       (+ -1 (len (tbf-data (system-s2r sys))))))
	    (:claim (<= (tbf-bkt (system-s2r (dlv-1 sys)))
			(len (tbf-data (system-s2r (dlv-1 sys))))))
	    (:use (:instance all-1-remove-ith
			     (tdgs (tbf-data (system-s2r sys)))))
	    :prove))

(definecd dlv-b (sys :system b :nat) :system
  :ic (^ (<= (tbf-bkt (system-s2r sys))
	     (len (tbf-data (system-s2r sys))))
	 (all-1 (tbf-data (system-s2r sys)))
	 (= b (tbf-bkt (system-s2r sys))))
  (if (= b 0) sys (dlv-b (dlv-1 sys) (1- b)))
  :body-contracts-hints (("Goal" :use (:instance dlv-b-contracts))))

(definecd dlv-b-inductor (sys :system b :nat) :nat
  :ic (^ (<= (tbf-bkt (system-s2r sys))
	     (len (tbf-data (system-s2r sys))))
	 (all-1 (tbf-data (system-s2r sys)))
	 (= b (tbf-bkt (system-s2r sys))))
  (if (= b 0) 0 (dlv-b-inductor (dlv-1 sys) (1- b)))
  :body-contracts-hints (("Goal" :use (:instance dlv-b-contracts))))

(propertyd top-dn-cons-prop (p :pos)
	   (== (cons (1+ p) (top-dn p p)) (top-dn (1+ p) (1+ p)))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(defthm preserve-top-dn-receiver
  (=> (^ (systemp sys)
	 (consp (tbf-data (system-s2r sys)))
	 (all-1 (tbf-data (system-s2r sys)))
	 (posp (tbf-bkt (system-s2r sys)))
	 (or (endp (system-receiver sys))
	     (equal (system-receiver sys)
		    (top-dn (maxl (system-receiver sys))
			    (maxl (system-receiver sys))))))
      (or (endp (system-receiver (dlv-1 sys)))
	  (equal (system-receiver (dlv-1 sys))
		 (top-dn (maxl (system-receiver (dlv-1 sys)))
			 (maxl (system-receiver (dlv-1 sys)))))))
  :instructions
  ((:use (:instance dlv-1-definition-rule))
   :pro
   (:claim
    (== (system-receiver (dlv-1 sys))
	(if (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				  (tbf-data (system-s2r sys))))
		     (system-receiver sys))
	    (cons (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
			       (tbf-data (system-s2r sys))))
		  (system-receiver sys))
	  (system-receiver sys))))
   (:drop 1)
   (:use (:instance top-dn-cons-prop
		    (p (maxl (system-receiver sys)))))
   (:use (:instance cumackp-1+maxl-top-dn-top
		    (top (maxl (system-receiver sys)))))
   (:use (:instance cumackp-nil
		    (p (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				    (tbf-data (system-s2r sys)))))))
   :pro
   (:claim (== (cons 1 nil) (top-dn 1 1)))
   (:use (:instance cumackp-1+maxl-top-dn-top
		    (top (maxl (system-receiver sys)))))
   (:use (:instance cumack-is-unique
		    (a0 (+ 1 (maxl (system-receiver sys))))
		    (a1 (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				     (tbf-data (system-s2r sys)))))
		    (ps (system-receiver sys))))
   :pro
   (:casesplit (endp (system-receiver sys)))
   (:casesplit (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				     (tbf-data (system-s2r sys))))
			(system-receiver sys)))
   (:claim (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				 (tbf-data (system-s2r sys))))
		    nil))
   :prove :prove
   (:casesplit (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				     (tbf-data (system-s2r sys))))
			(system-receiver sys)))
   (:drop 3 12)
   (:use (:instance maxl-top-dn-top=top
		    (top (maxl (system-receiver sys)))))
   (:use (:instance maxl-nonempty-pos
		    (ps (system-receiver sys))))
   :pro
   (:claim (equal (cons (+ 1 (maxl (system-receiver sys)))
			(top-dn (maxl (system-receiver sys))
				(maxl (system-receiver sys))))
		  (top-dn (+ 1 (maxl (system-receiver sys)))
			  (+ 1 (maxl (system-receiver sys))))))
   (:drop 6)
   (:claim (cumackp (+ 1
		       (maxl (top-dn (maxl (system-receiver sys))
				     (maxl (system-receiver sys)))))
		    (top-dn (maxl (system-receiver sys))
			    (maxl (system-receiver sys)))))
   (:drop 4 5)
   (:claim (posp (+ 1 (maxl (system-receiver sys)))))
   (:claim (< (+ -1 (len (tbf-data (system-s2r sys))))
	      (len (tbf-data (system-s2r sys)))))
   (:use (:instance all-1-works-lst
		    (tdgs (tbf-data (system-s2r sys)))))
   :pro
   (:claim (= (+ 1 (maxl (system-receiver sys)))
	      (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
			   (tbf-data (system-s2r sys))))))
   (:drop 4)
   (:claim (== (system-receiver (dlv-1 sys))
	       (cons (+ 1 (maxl (system-receiver sys)))
		     (system-receiver sys))))
   (:claim (== (system-receiver (dlv-1 sys))
	       (cons (+ 1 (maxl (system-receiver sys)))
		     (top-dn (maxl (system-receiver sys))
			     (maxl (system-receiver sys))))))
   (:claim (== (system-receiver (dlv-1 sys))
	       (top-dn (+ 1 (maxl (system-receiver sys)))
		       (+ 1 (maxl (system-receiver sys))))))
   (:use (:instance maxl-top-dn-top=top
		    (top (+ 1 (maxl (system-receiver sys))))))
   :prove
   (:claim (== (system-receiver (dlv-1 sys))
	       (system-receiver sys)))
   (:claim (= (maxl (system-receiver (dlv-1 sys)))
	      (maxl (system-receiver sys))))
   (:drop 1 2 3 4 5 7 8 9 11 12 14)
   :prove))

(defthm dlv-b-moves-thru-simplification
  (=> (^ (systemp sys)
	 (natp b)
	 (<= (tbf-bkt (system-s2r sys))
	     (len (tbf-data (system-s2r sys))))
	 (all-1 (tbf-data (system-s2r sys)))
	 (= b (tbf-bkt (system-s2r sys)))
	 (or (endp (system-receiver sys))
	     (equal (system-receiver sys)
		    (top-dn (maxl (system-receiver sys))
			    (maxl (system-receiver sys))))))
      (^ (<= b
	     (len (simplified-model-chan (simplify sys))))
	 (== (simplify (dlv-b sys b))
	     (dlv-b-simplified (simplify sys) b))))
  :instructions
  ((:in-theory (enable simplify-definition-rule
		       tdgs->poss-preserves-len))
   :pro
   (:claim (<= b
	       (len (simplified-model-chan (simplify sys)))))
   (:induct (dlv-b-inductor sys b))
   :change-goal
   (:in-theory (enable dlv-b-definition-rule
		       dlv-b-simplified-definition-rule))
   :prove
   (:use (:instance dlv-b-contracts))
   (:use (:instance dlv-1-ack-lhs-1))
   :pro
   (:claim (and (posp (tbf-bkt (system-s2r sys)))
		(consp (tbf-data (system-s2r sys)))
		(= (len (tbf-data (system-s2r (dlv-1 sys))))
		   (+ -1 (len (tbf-data (system-s2r sys)))))
		(= (tbf-bkt (system-s2r (dlv-1 sys)))
		   (+ -1 (tbf-bkt (system-s2r sys))))
		(<= (tbf-bkt (system-s2r (dlv-1 sys)))
		    (len (tbf-data (system-s2r (dlv-1 sys)))))
		(all-1 (tbf-data (system-s2r (dlv-1 sys))))))
   (:drop 2)
   (:claim
    (and
     (natp (+ -1
	      (len (tdgs->poss (tbf-data (system-s2r sys))))))
     (< (+ -1
	   (len (tdgs->poss (tbf-data (system-s2r sys)))))
	(len (tdgs->poss (tbf-data (system-s2r sys)))))
     (consp (simplified-model-chan (simplify sys)))
     (simplified-modelp (dlv-1-simplified (simplify sys)))
     (=
      (simplified-model-ack (simplify (dlv-1 sys)))
      (+
       1
       (maxl
	(if (cumackp (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
				  (tbf-data (system-s2r sys))))
		     (system-receiver sys))
	    (cons (tdg-id (nth (+ -1 (len (tbf-data (system-s2r sys))))
			       (tbf-data (system-s2r sys))))
		  (system-receiver sys))
	  (system-receiver sys)))))))
   (:drop 1)
   (:use (:instance preserve-top-dn-receiver))
   :pro
   (:claim (or (endp (system-receiver (dlv-1 sys)))
	       (equal (system-receiver (dlv-1 sys))
		      (top-dn (maxl (system-receiver (dlv-1 sys)))
			      (maxl (system-receiver (dlv-1 sys)))))))
   (:drop 1)
   (:claim (^ (systemp (dlv-1 sys))
	      (natp (+ -1 b))))
   (:in-theory (enable dlv-1-definition-rule))
   (:in-theory (enable tbf-fwd-definition-rule))
   (:claim (all-1 (tbf-data (system-s2r (dlv-1 sys)))))
   (:claim (= (+ -1 b)
	      (tbf-bkt (system-s2r (dlv-1 sys)))))
   (:in-theory (enable remove-ith-len
		       tdgs->poss-preserves-len))
   (:in-theory (enable simplify-definition-rule))
   (:claim (<= (+ -1 b)
	       (len (simplified-model-chan (simplify (dlv-1 sys))))))
   (:claim (equal (simplify (dlv-b (dlv-1 sys) (+ -1 b)))
		  (dlv-b-simplified (simplify (dlv-1 sys))
				    (+ -1 b))))
   (:drop 7)
   (:use (:instance dlv-b-definition-rule))
   :pro
   (:claim (== (simplify (dlv-b sys b))
	       (simplify (dlv-b (dlv-1 sys) (+ -1 b)))))
   (:use (:instance dlv-b-simplified-definition-rule
		    (sm (simplify sys))))
   :pro
   (:claim (== (dlv-b-simplified (simplify sys) b)
	       (dlv-b-simplified (dlv-1-simplified (simplify sys))
				 (+ -1 b))))
   (:use (:instance dlv-1-moves-thru-simplification))
   :pro
   (:in-theory (disable dlv-b-definition-rule
			dlv-1-definition-rule
			dlv-b-simplified-definition-rule
			dlv-b-simplified-definition-rule
			simplify-definition-rule))
   (:claim (== (dlv-b-simplified (simplify (dlv-1 sys))
				 (+ -1 b))
	       (dlv-b-simplified (dlv-1-simplified (simplify sys))
				 (+ -1 b))))
   :prove))

;; Characterize the effect of dlv-b-simplified on the channel.
(propertyd dlv-b-simplified-chan (sm :simplified-model b :pos)
	   :h (<= b (len (simplified-model-chan sm)))
	   (== (simplified-model-chan (dlv-b-simplified sm b))
	       (take (- (len (simplified-model-chan sm)) b) (simplified-model-chan sm)))
	   :instructions
	   ((:induct (dlv-b-simplified-chan-inductor sm b))
	    (:use (:instance dlv-b-simplified-definition-rule))
	    (:use (:instance dlv-b-1-commute (b (1- b))))
	    (:use (:instance dlv-b-1-commute-witness-definition-rule (b (1- b))))
	    :pro (:claim (== (dlv-b-simplified (dlv-1-simplified sm) (1- b))
			     (dlv-1-simplified (dlv-b-simplified sm (1- b)))))
	    (:use (:instance dlv-1-simplified-definition-rule
			     (sm (dlv-b-simplified sm (1- b)))))
	    (:in-theory (enable take-len-rule))
	    :pro (:claim (consp (simplified-model-chan (dlv-b-simplified sm (1- b)))))
	    (:claim (== (simplified-model-chan (dlv-b-simplified sm b))
			(simplified-model-chan (dlv-1-simplified (dlv-b-simplified sm (1- b))))))
	    (:in-theory (enable remove-ith-definition-rule))
	    (:use (:instance remove-last-take=take+1 (x (+ (len (simplified-model-chan sm)) (- (1- b))))
			     (ps (simplified-model-chan sm))))
	    (:use
	     (:instance
	      extract-chan
	      (sm (dlv-b-simplified sm (+ -1 b)))
	      (a
	       (if
		   (=
		    (simplified-model-ack (dlv-b-simplified sm (1- b)))
		    (nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			 (simplified-model-chan (dlv-b-simplified sm (1- b)))))
		   (1+ (nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			    (simplified-model-chan (dlv-b-simplified sm (+ -1 b)))))
		 (simplified-model-ack (dlv-b-simplified sm (1- b)))))
	      (cs
	       (remove-ith
		(simplified-model-chan (dlv-b-simplified sm (1- b)))
		(1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))))))
	    :pro
	    (:claim
	     (^ (simplified-modelp (dlv-b-simplified sm (1- b)))
		(posp
		 (if (= (simplified-model-ack (dlv-b-simplified sm (1- b)))
			(nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			     (simplified-model-chan (dlv-b-simplified sm (1- b)))))
		     (1+ (nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			      (simplified-model-chan (dlv-b-simplified sm (1- b)))))
		   (simplified-model-ack (dlv-b-simplified sm (1- b)))))
		(pos-listp
		 (remove-ith
		  (simplified-model-chan (dlv-b-simplified sm (1- b)))
		  (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))))))
	    (:claim
	     (== (simplified-model-chan
		  (mset :ack
			(if (= (simplified-model-ack (dlv-b-simplified sm (1- b)))
			       (nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
				    (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			    (1+ (nth (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b)))))
				     (simplified-model-chan (dlv-b-simplified sm (1- b)))))
			  (simplified-model-ack (dlv-b-simplified sm (1- b))))
			(mset
			 :chan
			 (remove-ith
			  (simplified-model-chan (dlv-b-simplified sm (1- b)))
			  (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b))))))
			 (dlv-b-simplified sm (1- b)))))
		 (remove-ith (simplified-model-chan (dlv-b-simplified sm (1- b)))
			     (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b))))))))
	    (:drop 1)
	    (:claim (== (simplified-model-chan (dlv-b-simplified sm b))
			(remove-ith (simplified-model-chan (dlv-b-simplified sm (1- b)))
				    (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b))))))))
	    :prove
	    (:use (:instance dlv-b-simplified-definition-rule))
	    (:use (:instance dlv-b-simplified-definition-rule (sm (dlv-1-simplified sm)) (b 0)))
	    (:use (:instance dlv-1-simplified-definition-rule))
	    (:use (:instance extract-chan
			     (a (if (= (simplified-model-ack sm)
				       (nth (1- (len (simplified-model-chan sm)))
					    (simplified-model-chan sm)))
				    (1+ (nth (1- (len (simplified-model-chan sm)))
					     (simplified-model-chan sm)))
				  (simplified-model-ack sm)))
			     (cs (remove-ith (simplified-model-chan sm)
					     (1- (len (simplified-model-chan sm)))))))
	    :pro
	    (:claim (consp (simplified-model-chan sm)))
	    (:claim (== (dlv-b-simplified sm b) (dlv-1-simplified sm)))
	    (:claim (== (simplified-model-chan (dlv-b-simplified sm b))
			(remove-ith (simplified-model-chan sm) (1- (len (simplified-model-chan sm))))))
	    (:in-theory (enable remove-last=take-len-1))
	    :prove))

;; Next let's characterize what dlv-b does to the high ack.  To do this, we need to reason about
;; both the "nice" case where the whole chan is [ack + k, ack + k - 1, ..., ack], and the
;; "turbulent" case where it's [ a bunch of nonsense ] ; [ack + k, ack + k - 1, ..., ack].
;; However, we do NOT need to worry about the case where it's inter-mixxed, because we explicitly
;; assume the channel fully drains in sub-RTT time.  As a first step, we need to show what dlv-1
;; does when the right-most element is ack.
(property (sm :simplified-model) ;; Sanity check contracts I skip in dlv-1-simplified-ack-incr
  :h (consp (simplified-model-chan sm))
  (^ (<= 0 (+ -1 (len (simplified-model-chan sm))))
     (possp (simplified-model-chan sm))
     (< (1- (len (simplified-model-chan sm))) (len (simplified-model-chan sm)))
     (posp (nth (1- (len (simplified-model-chan sm))) (simplified-model-chan sm)))))

(propertyd take-top-dn (top rem k :pos)
       :h (^ (<= k rem) (<= rem top))
       (== (take k (top-dn top rem))
           (top-dn top k))
       :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(propertyd app-remove-lst (ps0 ps1 :poss)
       :h (consp ps1)
       (== (remove-ith (app ps0 ps1) (1- (+ (len ps0) (len ps1))))
           (app ps0 (remove-ith ps1 (1- (len ps1)))))
       :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd remove-last-is-take (ps :poss)
       :h (consp ps)
       (== (remove-ith ps (1- (len ps))) (take (1- (len ps)) ps))
       :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(propertyd remove-last-of-app-lousy-stuff-top-dn
       (ack good-postfix-len :pos lousy-prefix :poss)
       (== (remove-ith (app lousy-prefix
                (top-dn (1- (+ ack good-postfix-len)) good-postfix-len))
               (+ -1 (len lousy-prefix) good-postfix-len))
           (app lousy-prefix (if (= good-postfix-len 1) nil
                   (top-dn (1- (+ ack good-postfix-len)) (1- good-postfix-len)))))
       :instructions
       ((:use (:instance top-dn-len (b (1- (+ ack good-postfix-len)))
                 (a good-postfix-len)))
        (:use (:instance app-remove-lst (ps0 lousy-prefix)
                 (ps1 (top-dn (1- (+ ack good-postfix-len))
                      good-postfix-len))))
        (:use (:instance remove-last-is-take
                 (ps (top-dn (1- (+ ack good-postfix-len))
                     good-postfix-len))))
        (:use (:instance take-top-dn
                 (top (1- (+ ack good-postfix-len)))
                 (rem good-postfix-len)
                 (k (1- good-postfix-len))))
        :prove))

(propertyd nth-top-dn-slider (top rem i :pos)
	   :h (^ (<= rem top) (< i rem))
	   (= (nth i (top-dn top rem)) (nth (1- i) (top-dn (1- top) (1- rem))))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(definecd nth-top-dn-slider-inductor (top rem :pos i :nat) :nat
  :ic (^ (<= rem top) (< i rem))
  (if (= i 0) 1 (nth-top-dn-slider-inductor (1- top) (1- rem) (1- i))))

(propertyd last-top-dn=bot (top rem :pos i :nat)
	   :h (^ (<= rem top) (< i rem))
	   (= (nth i (top-dn top rem)) (- top i))
	   :hints (("Goal" :induct (nth-top-dn-slider-inductor top rem i)
		    :in-theory (enable nth-top-dn-slider
				       top-dn-definition-rule
				       top-dn-len))))

(propertyd nth-prefix-postfix (prefix postfix :poss i :nat)
	   :h (^ (<= (len prefix) i)
		 (< i (+ (len prefix) (len postfix))))
	   (= (nth i (app prefix postfix))
	      (nth (- i (len prefix)) postfix)))

;; Suppose we do dlv-b-simplifed on a channel for which the b right-most elements
;; are ack + b, ack + b - 1, ..., ack + 1, ack.  Then the result is an increase in
;; ack of b amount.
(property remove-last-top-dn (top rem :pos)
  :h (<= rem top)
  (^ (< (1- rem) (len (top-dn top rem)))
     (== (remove-ith (top-dn top rem) (1- rem))
	 (top-dn top (1- rem))))
  :hints (("Goal" :use ((:instance take-all-but-last-is-remove-last
				   (ps (top-dn top rem)))
			(:instance top-dn-len (a top) (b rem))
			(:instance take-top-dn (k (1- rem))))
	   :in-theory (enable top-dn-definition-rule remove-ith-definition-rule)
	   :cases ((= rem 1)))))

;; The pattern described above is [prefix];(top-dn (+ (1- b) ack) b).
(propertyd chan-lem-lemma (sm :simplified-model b :pos prefix :poss)
	   :h (== (simplified-model-chan sm)
		  (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
	   (= (len (simplified-model-chan sm))
	      (+ (len prefix) b))
	   :hints (("Goal" :in-theory (enable top-dn-len))))

;; Sanity check (with output contracts) my postfix construction.
(definecd mk-postfix (ack len :pos) :poss
  :oc (^ (= (len (mk-postfix ack len)) len)
	 (= (nth (1- (len (mk-postfix ack len))) (mk-postfix ack len))
	    ack))
  (top-dn (+ (1- len) ack) len)
  :function-contract-hints (("Goal" :in-theory (enable top-dn-definition-rule
						       top-dn-len
						       last-top-dn=bot))))


(check= (mk-postfix 4 2) '(5 4))
(check= (mk-postfix 4 1) '(4))
(check= (mk-postfix 1 10) '(10 9 8 7 6 5 4 3 2 1))

(defthm dlv-b-simplified-effect-top-dn-inductor-contracts
  (=>
   (^ (simplified-modelp sm)
      (posp b)
      (possp prefix)
      (== (simplified-model-chan sm)
	  (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
      (!= b 1))
   (^
    (= (simplified-model-ack (dlv-1-simplified sm))
       (1+ (simplified-model-ack sm)))
    (== (simplified-model-chan (dlv-1-simplified sm))
	(append prefix
		(top-dn (+ (1- (1- b))
			   (simplified-model-ack (dlv-1-simplified sm)))
			(1- b))))))
  :instructions
  ((:use (:instance chan-lem-lemma))
   :pro
   (:claim (= (len (simplified-model-chan sm))
	      (+ (len prefix) b)))
   (:drop 1)
   (:use (:instance nth-prefix-postfix
		    (postfix (top-dn (+ (1- b) (simplified-model-ack sm))
				     b))
		    (i (1- (len (simplified-model-chan sm))))))
   (:use (:instance last-top-dn=bot
		    (top (+ (1- b) (simplified-model-ack sm)))
		    (rem b)
		    (i (1- b))))
   :pro
   (:claim (= (nth (+ -1 b)
		   (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			   b))
	      (simplified-model-ack sm)))
   (:drop 1)
   (:claim (= (nth (+ -1 (len (simplified-model-chan sm)))
		   (simplified-model-chan sm))
	      (nth (1- b)
		   (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			   b))))
   (:claim (= (nth (+ -1 (len (simplified-model-chan sm)))
		   (simplified-model-chan sm))
	      (simplified-model-ack sm)))
   (:drop 1 8 9)
   (:use (:instance dlv-1-simplified-definition-rule))
   :pro
   (:claim (= (simplified-model-ack (dlv-1-simplified sm))
	      (1+ (simplified-model-ack sm))))
   (:use (:instance dlv-1-simplified-prefix-postfix-helper
		    (postfix (top-dn (+ (+ -1 b) (simplified-model-ack sm))
				     b))))
   :pro
   (:claim
    (equal (simplified-model-chan (dlv-1-simplified sm))
	   (app prefix
		(take (+ -1
			 (len (top-dn (+ (+ -1 b) (simplified-model-ack sm))
				      b)))
		      (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			      b)))))
   (:drop 1)
   (:drop 1)
   (:in-theory (enable take-top-dn))
   :prove))

(propertyd consp-helper-top-dn-prefix-chan
	   (sm :simplified-model b :pos prefix :poss)
	   (consp (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
	   :instructions
	   ((:in-theory (enable top-dn-len))
	    :pro
	    (:claim (= (len (app prefix
				 (top-dn (+ (+ -1 b) (simplified-model-ack sm))
					 b)))
		       (+ (len prefix) b)))
	    :prove))

(propertyd dlv-b-simplified-effect-top-dn-inductor-contracts-2
	   (sm :simplified-model b :pos prefix :poss)
	   :h (== (simplified-model-chan sm)
		  (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
	   (if (= b 1)
	       t
	     (^
	      (consp (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
	      (consp (simplified-model-chan sm))
	      (= (simplified-model-ack (dlv-1-simplified sm))
		 (1+ (simplified-model-ack sm)))
	      (<= (1- b)
		  (+ (1- (1- b))
		     (simplified-model-ack (dlv-1-simplified sm))))
	      (== (simplified-model-chan (dlv-1-simplified sm))
		  (append prefix (top-dn (+ (1- (1- b))
					    (simplified-model-ack (dlv-1-simplified sm)))
					 (1- b))))
	      (simplified-modelp (dlv-1-simplified sm))
	      (posp (1- b))
	      (possp prefix)))
	   :hints (("Goal" :use ((:instance dlv-b-simplified-effect-top-dn-inductor-contracts)
				 (:instance consp-helper-top-dn-prefix-chan)))))


(definecd dlv-b-simplified-effect-top-dn-inductor
  (sm :simplified-model b :pos prefix :poss) :nat
  :ic (== (simplified-model-chan sm)
	  (append prefix (top-dn (+ (1- b) (simplified-model-ack sm)) b)))
  (if (= b 1) 1
    (dlv-b-simplified-effect-top-dn-inductor
     (dlv-1-simplified sm)
     (1- b)
     prefix))
  :body-contracts-hints
  (("Goal" :use (:instance dlv-b-simplified-effect-top-dn-inductor-contracts-2))))

(propertyd dlv-1-simplified-outputs-simplified (sm :simplified-model)
	   :h (consp (simplified-model-chan sm))
	   (simplified-modelp (dlv-1-simplified sm)))
                    
(defthm dlv-b-simplified-prefix-top-dn
  (=> (^ (simplified-modelp sm)
	 (posp b)
	 (possp prefix)
	 (== (simplified-model-chan sm)
	     (append prefix
		     (top-dn (+ (1- b) (simplified-model-ack sm))
			     b))))
      (^ (= (simplified-model-ack (dlv-b-simplified sm b))
	    (+ b (simplified-model-ack sm)))
	 (== (simplified-model-chan (dlv-b-simplified sm b))
	     prefix)))
  :instructions
  ((:use (:instance dlv-b-simplified-definition-rule))
   :pro
   (:claim (equal (dlv-b-simplified sm b)
		  (dlv-b-simplified (dlv-1-simplified sm)
				    (+ -1 b))))
   (:drop 1)
   (:induct (dlv-b-simplified-effect-top-dn-inductor sm b prefix))
   :change-goal :pro
   (:in-theory (enable top-dn-definition-rule))
   (:claim (== (simplified-model-chan sm)
	       (app prefix
		    (list (simplified-model-ack sm)))))
   (:use (:instance dlv-1-simplified-definition-rule))
   (:use (:instance dlv-b-simplified-definition-rule (b 0)
		    (sm (dlv-1-simplified sm))))
   (:in-theory (enable remove-ith-definition-rule
		       top-dn-definition-rule))
   :pro
   (:claim (== (dlv-b-simplified sm b)
	       (dlv-1-simplified sm)))
   (:claim (= (simplified-model-ack sm)
	      (nth (1- (len (simplified-model-chan sm)))
		   (simplified-model-chan sm))))
   (:claim (= (simplified-model-ack (dlv-1-simplified sm))
	      (1+ (simplified-model-ack sm))))
   (:claim (= (simplified-model-ack (dlv-b-simplified sm b))
	      (+ b (simplified-model-ack sm))))
   (:claim (== (simplified-model-chan (dlv-1-simplified sm))
	       (take (1- (len (simplified-model-chan sm)))
		     (simplified-model-chan sm))))
   (:claim (== (take (+ -1 (len (simplified-model-chan sm)))
		     (simplified-model-chan sm))
	       prefix))
   (:claim (== (simplified-model-chan (dlv-1-simplified sm))
	       (take (1- (len (simplified-model-chan sm)))
		     (simplified-model-chan sm))))
   :prove
   (:use (:instance remove-last-top-dn
		    (top (+ (1- b) (simplified-model-ack sm)))
		    (rem b)))
   :pro
   (:claim (equal (remove-ith (top-dn (+ (+ -1 b) (simplified-model-ack sm))
				      b)
			      (+ -1 b))
		  (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			  (+ -1 b))))
   (:drop 1)
   (:use (:instance last-top-dn=bot
		    (top (+ (1- b) (simplified-model-ack sm)))
		    (rem b)
		    (i (1- b))))
   :pro
   (:claim (= (nth (+ -1 b)
		   (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			   b))
	      (+ (+ (+ -1 b) (simplified-model-ack sm))
		 (- (+ -1 b)))))
   (:drop 1)
   (:use (:instance nth-prefix-postfix
		    (postfix (top-dn (+ (1- b) (simplified-model-ack sm))
				     b))
		    (i (1- (len (simplified-model-chan sm))))))
   :pro
   (:claim (= (nth (+ -1 (len (simplified-model-chan sm)))
		   (app prefix
			(top-dn (+ (+ -1 b) (simplified-model-ack sm))
				b)))
	      (nth (+ (+ -1 (len (simplified-model-chan sm)))
		      (- (len prefix)))
		   (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			   b))))
   (:drop 1)
   (:use (:instance remove-last-of-app-lousy-stuff-top-dn
		    (ack (simplified-model-ack sm))
		    (good-postfix-len b)
		    (lousy-prefix prefix)))
   :pro
   (:claim (equal (remove-ith (app prefix
				   (top-dn (+ -1 (simplified-model-ack sm) b)
					   b))
			      (+ -1 (len prefix) b))
		  (app prefix
		       (top-dn (+ -1 (simplified-model-ack sm) b)
			       (+ -1 b)))))
   (:drop 1)
   (:in-theory (enable top-dn-len))
   (:use (:instance dlv-b-simplified-chan))
   :pro
   (:claim (equal (simplified-model-chan (dlv-b-simplified sm b))
		  (take (+ (len (simplified-model-chan sm))
			   (- b))
			(simplified-model-chan sm))))
   (:drop 1)
   (:use (:instance dlv-1-simplified-prefix-postfix-helper
		    (postfix (top-dn (+ (+ -1 b) (simplified-model-ack sm))
				     b))))
   :pro
   (:claim
    (equal (simplified-model-chan (dlv-1-simplified sm))
	   (app prefix
		(take (+ -1
			 (len (top-dn (+ (+ -1 b) (simplified-model-ack sm))
				      b)))
		      (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			      b)))))
   (:drop 1)
   (:claim (= (nth (+ (+ -1 (len (simplified-model-chan sm)))
		      (- (len prefix)))
		   (top-dn (+ (+ -1 b) (simplified-model-ack sm))
			   b))
	      (simplified-model-ack sm)))
   (:use (:instance dlv-1-simplified-definition-rule))
   :pro
   (:claim (= (simplified-model-ack (dlv-1-simplified sm))
	      (1+ (simplified-model-ack sm))))
   (:claim
    (equal (simplified-model-chan (dlv-1-simplified sm))
	   (app prefix
		(top-dn (+ (+ -1 -1 b)
			   (simplified-model-ack (dlv-1-simplified sm)))
			(+ -1 b)))))
   (:use (:instance dlv-b-simplified-definition-rule
		    (sm (dlv-1-simplified sm))
		    (b (1- b))))
   :pro
   (:claim (<= (+ -1 b)
	       (len (simplified-model-chan (dlv-1-simplified sm)))))
   (:use (:instance dlv-1-simplified-outputs-simplified))
   :pro
   (:in-theory (disable dlv-1-simplified-definition-rule))
   (:claim (and (simplified-modelp sm)
		(consp (simplified-model-chan sm))))
   (:claim (simplified-modelp (dlv-1-simplified sm)))
   (:drop 1)
   (:claim (and (simplified-modelp (dlv-1-simplified sm))
		(natp (+ -1 b))
		(<= (+ -1 b)
		    (len (simplified-model-chan (dlv-1-simplified sm))))))
   (:claim (equal (dlv-b-simplified (dlv-1-simplified sm)
				    (+ -1 b))
		  (if (= (+ -1 b) 0)
		      (dlv-1-simplified sm)
		    (dlv-b-simplified (dlv-1-simplified (dlv-1-simplified sm))
				      (+ -1 -1 b)))))
   (:drop 1)
   (:claim (equal (dlv-b-simplified (dlv-1-simplified sm)
				    (+ -1 b))
		  (dlv-b-simplified (dlv-1-simplified (dlv-1-simplified sm))
				    (+ -1 -1 b))))
   (:drop 2 3 25 27)
   (:claim
    (and (= (simplified-model-ack (dlv-b-simplified (dlv-1-simplified sm)
						    (+ -1 b)))
	    (+ (+ -1 b)
	       (simplified-model-ack (dlv-1-simplified sm))))
	 (equal (simplified-model-chan (dlv-b-simplified (dlv-1-simplified sm)
							 (+ -1 b)))
		prefix)))
   (:drop 5)
   (:claim (= (simplified-model-ack (dlv-b-simplified sm b))
	      (+ b (simplified-model-ack sm))))
   :prove))

;; Next we want to show that if the churny / yucky bit is all > ack, then none of it will
;; change ack.
(definecd all>ack (ps :poss ack :pos) :bool
  (match ps
    (() t)
    ((p . rst) (^ (< ack p) (all>ack rst ack)))))

(propertyd all>ack->last>ack (ps :poss ack :pos)
       :h (^ (consp ps) (all>ack ps ack))
       (< ack (nth (1- (len ps)) ps))
       :hints (("Goal" :in-theory (enable all>ack-definition-rule))))

;; First show for dlv-1-simplified, then we can lift to dlv-b-simplified.
(propertyd all>ack-chan->does-not-change-ack-1 (sm :simplified-model)
	   :h (^ (consp (simplified-model-chan sm))
		 (all>ack (simplified-model-chan sm) (simplified-model-ack sm)))
	   (= (simplified-model-ack (dlv-1-simplified sm))
	      (simplified-model-ack sm))
	   :hints (("Goal" :use ((:instance dlv-1-simplified-definition-rule)
				 (:instance all>ack->last>ack
					    (ps (simplified-model-chan sm))
					    (ack (simplified-model-ack sm)))))))

(defthm dlv-1-simplified-b-inductor-cons-hint
  (=> (^ (simplified-modelp sm)
         (posp b)
         (consp (simplified-model-chan sm))
         (all>ack (simplified-model-chan sm)
                  (simplified-model-ack sm))
         (<= b (len (simplified-model-chan sm)))
         (!= b 1))
      (consp (simplified-model-chan (dlv-1-simplified sm))))
  :instructions
  (:pro (:use (:instance dlv-1-simplified-definition-rule))
        :pro
        (:claim (== (simplified-model-chan (dlv-1-simplified sm))
                    (remove-ith (simplified-model-chan sm)
                                (+ -1 (len (simplified-model-chan sm))))))
        (:in-theory (enable remove-ith-definition-rule))
        (:use (:instance remove-ith-len
                         (ps (simplified-model-chan sm))
                         (i (+ -1 (len (simplified-model-chan sm))))))
        :pro
        (:claim (= (len (remove-ith (simplified-model-chan sm)
                                    (+ -1 (len (simplified-model-chan sm)))))
                   (+ -1 (len (simplified-model-chan sm)))))
        :prove))

(in-theory (disable dlv-1-simplified-b-inductor-cons-hint))
       
(propertyd all>ack-append (ps0 ps1 :poss ack :pos)
	   (iff (^ (all>ack ps0 ack) (all>ack ps1 ack))
		(all>ack (append ps0 ps1) ack))
	   :hints (("Goal" :in-theory (enable all>ack-definition-rule))))

(propertyd all-but-last-plus-last=all (ps :poss)
	   :h (consp ps)
	   (== (app (take (1- (len ps)) ps) (last ps))
	       ps))

(propertyd all>ack->all-but-last>ack (ps :poss ack :pos)
	   :h (^ (consp ps) (all>ack ps ack))
	   (all>ack (take (1- (len ps)) ps) ack)
	   :instructions ((:casesplit (= (len ps) 1))
			  (:in-theory (enable all>ack-definition-rule))
			  :prove
			  (:use (:instance all>ack-append
					   (ps0 (take (1- (len ps)) ps))
					   (ps1 (last ps))))
			  (:use (:instance all-but-last-plus-last=all))
			  :pro
			  (:claim (== (app (take (+ -1 (len ps)) ps)
					   (last ps))
				      ps))
			  (:drop 1)
			  :prove))

(propertyd b-decrs-with-len-all>ack-hint (sm :simplified-model b :pos)
	   :h (<= b (len (simplified-model-chan sm)))
	   (<= (1- b) (len (simplified-model-chan (dlv-1-simplified sm))))
	   :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
					      remove-ith-definition-rule))))

(defthm dlv-b-simplified-effect-churny-inductor-contracts
  (=> (^ (simplified-modelp sm)
         (posp b)
         (consp (simplified-model-chan sm))
         (all>ack (simplified-model-chan sm)
                  (simplified-model-ack sm))
         (<= b (len (simplified-model-chan sm)))
         (!= b 1))
      (^ (simplified-modelp (dlv-1-simplified sm))
         (posp (1- b))
         (consp (simplified-model-chan (dlv-1-simplified sm)))
         (all>ack (simplified-model-chan (dlv-1-simplified sm))
                  (simplified-model-ack (dlv-1-simplified sm)))
         (<= (1- b)
             (len (simplified-model-chan (dlv-1-simplified sm))))
	 (= (simplified-model-ack (dlv-1-simplified sm))
	    (simplified-model-ack sm))))
  :instructions
  ((:use (:instance dlv-1-simplified-b-inductor-cons-hint))
   :pro
   (:claim (consp (simplified-model-chan (dlv-1-simplified sm))))
   (:drop 1)
   (:use (:instance all>ack->all-but-last>ack
                    (ps (simplified-model-chan sm))
                    (ack (simplified-model-ack sm))))
   :pro
   (:claim (all>ack (take (+ -1 (len (simplified-model-chan sm)))
                          (simplified-model-chan sm))
                    (simplified-model-ack sm)))
   (:drop 1)
   (:use (:instance b-decrs-with-len-all>ack-hint))
   :pro
   (:claim (<= (+ -1 b)
               (len (simplified-model-chan (dlv-1-simplified sm)))))
   (:drop 1)
   (:use (:instance all>ack-chan->does-not-change-ack-1))
   :pro
   (:claim (= (simplified-model-ack (dlv-1-simplified sm))
              (simplified-model-ack sm)))
   (:drop 1)
   (:claim (== (take (+ -1 (len (simplified-model-chan sm)))
                     (simplified-model-chan sm))
               (simplified-model-chan (dlv-1-simplified sm))))
   :prove))

(in-theory (disable dlv-b-simplified-effect-churny-inductor-contracts))

(definecd dlv-b-simplified-effect-churny-inductor
  (sm :simplified-model b :pos) :nat
  :ic (^ (consp (simplified-model-chan sm))
	 (all>ack (simplified-model-chan sm) (simplified-model-ack sm))
	 (<= b (len (simplified-model-chan sm))))
  (if (= b 1) 1
    (dlv-b-simplified-effect-churny-inductor
     (dlv-1-simplified sm)
     (1- b)))
  :body-contracts-hints
  (("Goal" :use (:instance dlv-b-simplified-effect-churny-inductor-contracts))))

;; Now let's lift.  Note, we no longer need to do the prefix/postfix nonsense,
;; because we can just make it an assumption that R-b divides d-cap.
(propertyd dlv-b-simplified-churny (sm :simplified-model b :pos)
	   :h (^ (consp (simplified-model-chan sm))
		 (all>ack (simplified-model-chan sm) (simplified-model-ack sm))
		 (<= b (len (simplified-model-chan sm))))
	   (= (simplified-model-ack (dlv-b-simplified sm b))
	      (simplified-model-ack sm))
	   :instructions
	   ((:induct (dlv-b-simplified-effect-churny-inductor sm b))
	    (:use (:instance dlv-b-simplified-effect-churny-inductor-contracts))
	    (:use (:instance dlv-b-simplified-definition-rule))
	    :prove
	    (:use (:instance dlv-b-simplified-definition-rule))
	    (:use (:instance dlv-b-simplified-definition-rule
			     (sm (dlv-1-simplified sm))
			     (b (1- b))))
	    (:use (:instance all>ack-chan->does-not-change-ack-1))
	    :prove))
