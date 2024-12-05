(in-package "ACL2S")
(include-book "performance-models")

;; ------------ Single Step Simplified -------------------
(definecd single-step-simplified (sm :simplified-model R b :pos) :simplified-model
  ;; 1. The sender transmits R packets.  Then ...
  ;; 2. The sender-to-receiver TBF delivers b of them.
  :ic (^ (<= (+ (simplified-model-cur sm) R)
	     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	 (<= b (min R (simplified-model-d-cap sm)))
	 (<= (len (simplified-model-chan sm))
	     (simplified-model-d-cap sm)))
  ;; This output contract is the crux of the entire efficiency argument.
  :oc (= (len (simplified-model-chan (single-step-simplified sm R b)))
	 (- (min (simplified-model-d-cap sm)
		 (+ (len (simplified-model-chan sm)) R))
	    b))
  (dlv-b-simplified (snd-R-simplified sm R) b)
  :body-contracts-hints
  (("Goal" :use ((:instance snd-R-simplified-incrs-len)
		 (:instance dlv-b-simplified-chan
			    (sm (snd-R-simplified sm R))))))
  :function-contract-hints
  (("Goal" :use ((:instance snd-R-simplified-incrs-len)
		 (:instance dlv-b-simplified-chan
			    (sm (snd-R-simplified sm R)))
		 (:instance take-len-rule
			    (ps (simplified-model-chan (snd-R-simplified sm R)))
			    (x (- (len (simplified-model-chan (snd-R-simplified sm R))) b)))))))

(definecd all-nz (dgs :tdgs) :bool
  (match dgs
    (() t)
    ((dg . rst) (^ (!= 0 (tdg-del dg)) (all-nz rst)))))

(propertyd all-nz->age-all-len=len (dgs :tdgs)
  :h (all-nz dgs)
  (= (len (age-all dgs)) (len dgs))
  :hints (("Goal" :in-theory (enable all-nz-definition-rule
				     age-all-definition-rule))))

(propertyd all-nz->age-all->dgs->poss= (dgs :tdgs)
	   :h (all-nz dgs)
	   (== (tdgs->poss (age-all dgs)) (tdgs->poss dgs))
	   :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
					      |MAP*-*(LAMBDA (D) (TDG-ID D))|
					      age-all-definition-rule
					      all-nz-definition-rule))))

(propertyd all-nz->tbf-tick->dgs->poss= (tbf :tbf)
	   :h (all-nz (tbf-data tbf))
	   (== (tdgs->poss (tbf-data (tbf-tick tbf))) (tdgs->poss (tbf-data tbf)))
	   :hints (("Goal" :in-theory (enable tbf-tick-definition-rule
					      tbf-age-definition-rule
					      all-nz->age-all->dgs->poss=))))

(propertyd snd-1-systemp (sys :system R :pos)
	   :h (^ (!= R 1)
		 (<= (+ (sender-state-cur (system-sender sys)) r)
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys)))))
	   (systemp (snd-1 sys "p")))

(propertyd snd-R-effect-helper (sys :system R :pos)
	   :h (<= (+ (sender-state-cur (system-sender sys)) R)
		  (+ (sender-state-hiA (system-sender sys))
		     (sender-state-N (system-sender sys))))
	   (^ (= (tbf-bkt (system-s2r (snd-R sys R)))
		 (tbf-bkt (system-s2r sys)))
	      (= (tbf-b-cap (system-s2r (snd-R sys R)))
		 (tbf-b-cap (system-s2r sys)))
	      (= (tbf-d-cap (system-s2r (snd-R sys R)))
		 (tbf-d-cap (system-s2r sys)))
	      (= (tbf-rat (system-s2r (snd-R sys R)))
		 (tbf-rat (system-s2r sys)))
	      (== (tbf-del (system-s2r (snd-R sys R)))
		  (tbf-del (system-s2r sys)))
	      (= (sender-state-N (system-sender (snd-R sys R)))
		 (sender-state-N (system-sender sys)))
	      (= (sender-state-hiA (system-sender (snd-R sys R)))
		 (sender-state-hiA (system-sender sys)))
	      (= (sender-state-cur (system-sender (snd-R sys R)))
		 (+ (sender-state-cur (system-sender sys)) R))
	      (== (system-receiver (snd-R sys R))
		  (system-receiver sys)))
	   :instructions
	   ((:induct (snd-r-inductor sys r))
	    :prove
	    (:use (:instance snd-r-contracts))
	    :pro (:casesplit (= r 1))
	    (:in-theory (enable snd-r-definition-rule))
	    (:claim (== (snd-r sys r) (snd-1 sys "p")))
	    (:in-theory (enable snd-1-definition-rule
				tbf-prc-definition-rule
				sender-adv-cur-definition-rule))
	    :prove
	    (:use (:instance snd-r-definition-rule))
	    :pro
	    (:claim (== (snd-r sys r)
			(snd-r (snd-1 sys "p") (+ -1 r))))
	    (:in-theory (enable snd-1-definition-rule
				tbf-prc-definition-rule
				sender-adv-cur-definition-rule))
	    (:claim (= (tbf-bkt (system-s2r (snd-1 sys "p")))
		       (tbf-bkt (system-s2r sys))))
	    (:claim (= (tbf-b-cap (system-s2r (snd-1 sys "p")))
		       (tbf-b-cap (system-s2r sys))))
	    (:claim (= (tbf-d-cap (system-s2r (snd-1 sys "p")))
		       (tbf-d-cap (system-s2r sys))))
	    (:claim (= (tbf-rat (system-s2r (snd-1 sys "p")))
		       (tbf-rat (system-s2r sys))))
	    (:claim (= (sender-state-n (system-sender (snd-1 sys "p")))
		       (sender-state-n (system-sender sys))))
	    (:claim (= (sender-state-hiA (system-sender (snd-1 sys "p")))
		       (sender-state-hiA (system-sender sys))))
	    (:claim (= (sender-state-cur (system-sender (snd-1 sys "p")))
		       (1+ (sender-state-cur (system-sender sys)))))
	    (:claim (== (system-receiver (snd-1 sys "p"))
			(system-receiver sys)))
	    (:drop 1 2)
	    (:claim (<= (+ (sender-state-cur (system-sender (snd-1 sys "p")))
			   -1 r)
			(+ (sender-state-hia (system-sender (snd-1 sys "p")))
			   (sender-state-n (system-sender (snd-1 sys "p"))))))
	    (:claim (posp (1- r)))
	    (:use (:instance snd-1-systemp))
	    :pro (:claim (systemp (snd-1 sys "p")))
	    :prove
	    (:in-theory (enable snd-r-definition-rule))
	    :prove))

(propertyd tbf-tick-effect (tbf :tbf)
	   :h (= (tbf-rat tbf) (tbf-b-cap tbf))
	   (^ (= (tbf-bkt (tbf-tick tbf)) (tbf-b-cap tbf))
	      (= (tbf-d-cap (tbf-tick tbf)) (tbf-d-cap tbf))
	      (= (tbf-b-cap (tbf-tick tbf)) (tbf-b-cap tbf))
	      (= (tbf-rat (tbf-tick tbf)) (tbf-rat tbf))
	      (== (tbf-del (tbf-tick tbf)) (tbf-del tbf)))
	   :hints (("Goal" :in-theory (enable tbf-tick-definition-rule
					      tbf-age-definition-rule
					      age-all-definition-rule))))

(propertyd system-s2r-tick-step-after-snd-r-effect (sys :system R :pos)
	   :h (^ (= (tbf-rat (system-s2r sys)) (tbf-b-cap (system-s2r sys)))
		 (<= (+ (sender-state-cur (system-sender sys)) R)
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys)))))
	   (^ (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-b-cap (system-s2r sys)))
	      (= (tbf-b-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-b-cap (system-s2r sys)))
	      (= (tbf-d-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-d-cap (system-s2r sys)))
	      (= (tbf-rat (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-rat (system-s2r sys)))
	      (== (tbf-del (system-s2r (system-s2r-tick-step (snd-r sys r))))
		  (tbf-del (system-s2r sys)))
	      (= (sender-state-n (system-sender (system-s2r-tick-step (snd-r sys r))))
		 (sender-state-n (system-sender sys)))
	      (= (sender-state-cur (system-sender (system-s2r-tick-step (snd-r sys r))))
		 (+ R (sender-state-cur (system-sender sys))))
	      (== (system-receiver (system-s2r-tick-step (snd-r sys r)))
		  (system-receiver sys)))
	   :instructions
	   ((:use (:instance snd-r-effect-helper))
	    (:use (:instance system-s2r-tick-step-definition-rule
			     (sys (snd-r sys r))))
	    (:use (:instance tbf-tick-effect
			     (tbf (system-s2r (snd-r sys r)))))
	    :pro
	    (:claim (== (system-sender (system-s2r-tick-step (snd-r sys r)))
			(system-sender (snd-r sys r))))
	    (:claim (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
		       (tbf-b-cap (system-s2r sys))))
	    :prove))

(definecd all-inf (tdgs :tdgs) :bool
  (match tdgs
    (() t)
    ((tdg . rst) (^ (! (natp (tdg-del tdg)))
		    (all-inf rst)))))

(propertyd all-inf->all-nz (tdgs :tdgs) :h (all-inf tdgs) (all-nz tdgs)
	   :hints (("Goal" :in-theory (enable all-inf-definition-rule
					      all-nz-definition-rule))))

(propertyd all-inf-cons (tdg :tdg tdgs :tdgs)
	   :h (^ (! (natp (tdg-del tdg)))
		 (all-inf tdgs))
	   (all-inf (cons tdg tdgs))
	   :hints (("Goal" :in-theory (enable all-inf-definition-rule))))

(propertyd all-inf-prc (tbf :tbf i :pos pld :string)
	   :h (^ (all-inf (tbf-data tbf))
		 (! (natp (tbf-del tbf))))
	   (all-inf (tbf-data (tbf-prc tbf i pld)))
	   :hints (("Goal" :in-theory (enable tbf-prc-definition-rule
					      all-inf-cons))))

(propertyd all-1-prc (tbf :tbf i :pos pld :string)
	   :h (^ (all-1 (tbf-data tbf))
		 (= (length pld) 1))
	   (all-1 (tbf-data (tbf-prc tbf i pld)))
	   :hints (("Goal" :in-theory (enable tbf-prc-definition-rule
					      all-1-definition-rule))))

(propertyd inf-1-inv-snd-1 (sys :system pld :string)
	   :h (^ (= (length pld) 1)
		 (! (natp (tbf-del (system-s2r sys))))
		 (all-inf (tbf-data (system-s2r sys)))
		 (all-1 (tbf-data (system-s2r sys)))
		 (< (sender-state-cur (system-sender sys))
		    (+ (sender-state-hia (system-sender sys))
		       (sender-state-n (system-sender sys)))))
	   (^ (! (natp (tbf-del (system-s2r (snd-1 sys pld)))))
	      (all-inf (tbf-data (system-s2r (snd-1 sys pld))))
	      (all-1 (tbf-data (system-s2r (snd-1 sys pld)))))
	   :instructions
	   ((:use (:instance snd-1-definition-rule (x pld)))
	    :pro
	    (:claim (== (system-s2r (snd-1 sys pld))
			(tbf-prc (system-s2r sys)
				 (sender-state-cur (system-sender sys))
				 pld)))
	    (:use (:instance all-inf-prc (tbf (system-s2r sys))
			     (i (sender-state-cur (system-sender sys)))))
	    :pro
	    (:claim (all-inf (tbf-data (tbf-prc (system-s2r sys)
						(sender-state-cur (system-sender sys))
						pld))))
	    (:use (:instance all-1-prc (tbf (system-s2r sys))
			     (i (sender-state-cur (system-sender sys)))))
	    :pro
	    (:claim (all-1 (tbf-data (tbf-prc (system-s2r sys)
					      (sender-state-cur (system-sender sys))
					      pld))))
	    (:claim (all-inf (tbf-data (system-s2r (snd-1 sys pld)))))
	    (:claim (all-1 (tbf-data (system-s2r (snd-1 sys pld)))))
	    (:in-theory (enable tbf-prc-definition-rule))
	    (:drop 1 2)
	    (:claim (== (tbf-del (system-s2r (snd-1 sys pld)))
			(tbf-del (tbf-prc (system-s2r sys)
					  (sender-state-cur (system-sender sys))
					  pld))))
	    (:claim (== (tbf-del (system-s2r (snd-1 sys pld)))
			(tbf-del (system-s2r sys))))
	    :prove))

(propertyd inf-1-inv-snd-R (sys :system R :pos)
	   :h (^ (not (natp (tbf-del (system-s2r sys))))
		 (all-inf (tbf-data (system-s2r sys)))
		 (all-1 (tbf-data (system-s2r sys)))
		 (<= (+ (sender-state-cur (system-sender sys)) R)
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys)))))
	   (^ (all-inf (tbf-data (system-s2r (snd-R sys R))))
	      (all-1 (tbf-data (system-s2r (snd-R sys R)))))
	   :instructions
	   ((:induct (snd-r-inductor sys r))
	    :prove
	    (:use (:instance inf-1-inv-snd-1 (pld "p")))
	    :pro
	    (:claim (and (not (natp (tbf-del (system-s2r (snd-1 sys "p")))))
			 (all-inf (tbf-data (system-s2r (snd-1 sys "p"))))
			 (all-1 (tbf-data (system-s2r (snd-1 sys "p"))))))
	    (:drop 1)
	    (:use (:instance snd-r-contracts))
	    :pro
	    (:claim (and (< (sender-state-cur (system-sender sys))
			    (+ (sender-state-hia (system-sender sys))
			       (sender-state-n (system-sender sys))))
			 (= (length "p") 1)
			 (<= (+ (sender-state-cur (system-sender (snd-1 sys "p")))
				-1 r)
			     (+ (sender-state-hia (system-sender (snd-1 sys "p")))
				(sender-state-n (system-sender (snd-1 sys "p")))))))
	    (:drop 1)
	    (:claim (systemp (snd-1 sys "p")))
	    (:casesplit (= r 1))
	    (:in-theory (enable snd-r-definition-rule))
	    (:claim (== (snd-r sys r) (snd-1 sys "p")))
	    :prove :prove :prove))

(definecd age-all-inductor (tdgs :tdgs) :nat
  (match tdgs
    (() 0)
    ((& . rst) (age-all-inductor rst))))

(propertyd tdgsp-cons (tdg :tdg tdgs :tdgs) (tdgsp (cons tdg tdgs)))

(propertyd age-all-cons (tdg :tdg tdgs :tdgs)
	   (== (age-all (cons tdg tdgs))
	       (if (o< 0 (tdg-del tdg))
		   (cons (mset :del (o- (tdg-del tdg) 1) tdg)
			 (age-all tdgs))
		 (age-all tdgs)))
	   :hints (("Goal" :in-theory (enable age-all-definition-rule))))

(propertyd not-natp-preserved-under-decr (n :nat-ord)
	   :h (! (natp n))
	   (! (natp (o- n 1)))
	   :hints (("Goal" :in-theory (enable o-))))

(propertyd all-1-cons (tdg :tdg tdgs :tdgs)
	   :h (^ (= (length (tdg-pld tdg)) 1) (all-1 tdgs))
	   (all-1 (cons tdg tdgs))
	   :hints (("Goal" :in-theory (enable all-1-definition-rule))))

(propertyd all-1-age (tdgs :tdgs)
	   :h (all-1 tdgs)
	   (all-1 (age-all tdgs))
	   :hints (("Goal" :in-theory (enable all-1-definition-rule
					      age-all-definition-rule))))

(propertyd all-1-car (tdgs :tdgs)
	   :h (^ (consp tdgs) (all-1 tdgs))
	   (= (length (tdg-pld (car tdgs))) 1)
	   :hints (("Goal" :in-theory (enable all-1-definition-rule))))

(propertyd all-inf->age-all-1->all-inf (tdgs :tdgs)
	   :h (^ (all-inf tdgs)
		 (all-1 tdgs))
	   (^ (all-inf (age-all tdgs))
	      (all-1 (age-all tdgs)))
	   :instructions
	   ((:induct (age-all-inductor tdgs))
	    :prove :pro
	    (:in-theory (enable all-inf-definition-rule
				all-1-definition-rule))
	    (:claim (all-inf (age-all (cdr tdgs))))
	    (:claim (all-1 (age-all (cdr tdgs))))
	    (:drop 4)
	    (:use (:instance age-all-cons (tdg (car tdgs))
			     (tdgs (cdr tdgs))))
	    :pro
	    (:claim (o< 0 (tdg-del (car tdgs))))
	    (:claim (== (age-all tdgs)
			(cons (mset :del (o- (tdg-del (car tdgs)) 1)
				    (car tdgs))
			      (age-all (cdr tdgs)))))
	    (:drop 1)
	    (:claim (! (natp (tdg-del (car tdgs)))))
	    (:use (:instance all-inf-cons
			     (tdg (mset :del (o- (tdg-del (car tdgs)) 1)
					(car tdgs)))
			     (tdgs (age-all (cdr tdgs)))))
	    (:use (:instance all-1-cons
			     (tdg (mset :del (o- (tdg-del (car tdgs)) 1)
					(car tdgs)))
			     (tdgs (age-all (cdr tdgs)))))
	    :pro
	    (:claim (tdgp (mset :del (o- (tdg-del (car tdgs)) 1)
				(car tdgs))))
	    (:claim (tdgsp (age-all (cdr tdgs))))
	    (:in-theory (enable o-))
	    (:claim (all-inf (age-all tdgs)))
	    (:drop 2)
	    (:claim (= (length (tdg-pld (mset :del (o- (tdg-del (car tdgs)) 1)
					      (car tdgs))))
		       (length (tdg-pld (car tdgs)))))
	    (:use (:instance all-1-car))
	    :prove :prove))

(propertyd age-doesnt-care-about-bkt (b :pos tbf :tbf)
	   (== (tbf-data (mset :bkt b (tbf-age tbf)))
	       (tbf-data (tbf-age tbf)))
	   :hints (("Goal" :in-theory (enable tbf-age-definition-rule))))

(propertyd tbf-age-preserves-all-inf-all-1 (tbf :tbf)
	   :h (^ (all-inf (tbf-data tbf)) (all-1 (tbf-data tbf)))
	   (^ (all-inf (tbf-data (tbf-age tbf)))
	      (all-1 (tbf-data (tbf-age tbf))))
	   :hints (("Goal" :in-theory (enable tbf-age-definition-rule
					      all-inf->age-all-1->all-inf))))

(propertyd age-all-preserves-tdgs-poss (tdgs :tdgs)
	   :h (all-inf tdgs)
	   (== (tdgs->poss (age-all tdgs))
	       (tdgs->poss tdgs))
	   :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
					      |MAP*-*(LAMBDA (D) (TDG-ID D))|
					      age-all-definition-rule
					      all-inf-definition-rule)
		    :induct (age-all-inductor tdgs))))

(propertyd tdgs->poss-preserves-len (tdgs :tdgs)
	   (= (len (tdgs->poss tdgs)) (len tdgs))
	   :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
					      |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(propertyd tbf-tick-preserves-len-all-inf (tbf :tbf)
	   :h (all-inf (tbf-data tbf))
	   (= (len (tbf-data (tbf-tick tbf))) (len (tbf-data tbf)))
	   :instructions ((:use (:instance tbf-tick-definition-rule))
			  (:use (:instance age-doesnt-care-about-bkt
					   (b (min (+ (tbf-bkt tbf) (tbf-rat tbf))
						   (tbf-b-cap tbf)))))
			  (:use (:instance age-all-preserves-tdgs-poss
					   (tdgs (tbf-data tbf))))
			  (:use (:instance tdgs->poss-preserves-len
					   (tdgs (age-all (tbf-data tbf)))))
			  (:use (:instance tdgs->poss-preserves-len
					   (tdgs (tbf-data tbf))))
			  :pro
			  (:claim (= (len (tdgs->poss (tbf-data tbf)))
				     (len (tbf-data tbf))))
			  (:drop 1)
			  (:claim (= (len (tdgs->poss (age-all (tbf-data tbf))))
				     (len (age-all (tbf-data tbf)))))
			  (:drop 1)
			  (:claim (equal (tdgs->poss (age-all (tbf-data tbf)))
					 (tdgs->poss (tbf-data tbf))))
			  (:drop 1)
			  (:claim (= (len (tbf-data (tbf-tick tbf)))
				     (len (tbf-data (tbf-age tbf)))))
			  (:in-theory (enable tbf-age-definition-rule))
			  :prove))

(propertyd tbf-tick-snd-r-preserves-len<=d-cap (sys :system R b :pos)
	   :h (^ (<= (len (tbf-data (system-s2r sys)))
		     (mget :d-cap (mget :s2r sys)))
		 (<= (+ (sender-state-cur (system-sender sys)) R)
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys))))
		 (all-inf (tbf-data (system-s2r (snd-r sys r))))
		 (all-1 (tbf-data (system-s2r sys))))
	   (<= (len (mget :data (tbf-tick (system-s2r (snd-r sys r)))))
	       (mget :d-cap (mget :s2r sys)))
	   :instructions
	   ((:use (:instance tbf-tick-preserves-len-all-inf
			     (tbf (system-s2r (snd-r sys r)))))
	    :pro
	    (:claim (= (len (tbf-data (tbf-tick (system-s2r (snd-r sys r)))))
		       (len (tbf-data (system-s2r (snd-r sys r))))))
	    (:drop 1)
	    (:use (:instance snd-r-moves-thru-simplification))
	    :pro
	    (:claim (equal (snd-r-simplified (simplify sys) r)
			   (simplify (snd-r sys r))))
	    (:drop 1)
	    (:claim
	     (= (len (simplified-model-chan (snd-r-simplified (simplify sys) r)))
		(len (simplified-model-chan (simplify (snd-r sys r))))))
	    (:use (:instance snd-r-simplified-incrs-len
			     (sm (simplify sys))))
	    :pro
	    (:in-theory (enable simplify-definition-rule
				tdgs->poss-preserves-len))
	    (:claim
	     (= (len (simplified-model-chan (snd-r-simplified (simplify sys) r)))
		(min (+ (len (simplified-model-chan (simplify sys)))
			r)
		     (simplified-model-d-cap (simplify sys)))))
	    (:drop 1)
	    :prove))

(propertyd single-step-input-contracts (sys :system R b :pos) 
	   :h (^ (<= (+ (sender-state-cur (system-sender sys))
			r)
		     (+ (sender-state-hia (system-sender sys))
			(sender-state-n (system-sender sys))))
		 (all-inf (tbf-data (system-s2r sys)))
		 (all-1 (tbf-data (system-s2r sys)))
		 (not (natp (tbf-del (system-s2r sys))))
		 (<= b (min r (tbf-d-cap (system-s2r sys))))
		 (= b (tbf-b-cap (system-s2r sys)))
		 (= b (tbf-rat (system-s2r sys)))
		 (<= (tbf-bkt (system-s2r sys))
		     (tbf-b-cap (system-s2r sys)))
		 (<= (tbf-b-cap (system-s2r sys))
		     (tbf-d-cap (system-s2r sys)))
		 (<= (len (tbf-data (system-s2r sys)))
		     (tbf-d-cap (system-s2r sys))))
	   (^
	    (systemp (snd-r sys r))
	    (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
	       (tbf-b-cap (system-s2r sys)))
	    (= (tbf-b-cap (system-s2r sys)) b)
	    (all-inf (tbf-data (system-s2r (snd-r sys r))))
	    (all-1 (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
	    (all-inf (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
	    (==
	     (tdgs->poss (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
	     (tdgs->poss (tbf-data (system-s2r (snd-r sys r)))))
	    (<= (len (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
		(tbf-d-cap (system-s2r sys)))
	    (= (tbf-d-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
	       (tbf-d-cap (system-s2r sys)))
	    (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r)))) b)
	    (<= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
		(len (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))))
	   :instructions
	   ((:use (:instance inf-1-inv-snd-r))
	    :pro
	    (:claim (and (all-inf (tbf-data (system-s2r (snd-r sys r))))
			 (all-1 (tbf-data (system-s2r (snd-r sys r))))))
	    (:drop 1)
	    (:use (:instance system-s2r-tick-step-after-snd-r-effect))
	    :pro
	    (:claim
	     (and
	      (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-b-cap (system-s2r sys)))
	      (= (tbf-b-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-b-cap (system-s2r sys)))
	      (= (tbf-d-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-d-cap (system-s2r sys)))
	      (= (tbf-rat (system-s2r (system-s2r-tick-step (snd-r sys r))))
		 (tbf-rat (system-s2r sys)))
	      (equal (tbf-del (system-s2r (system-s2r-tick-step (snd-r sys r))))
		     (tbf-del (system-s2r sys)))
	      (= (sender-state-n (system-sender (system-s2r-tick-step (snd-r sys r))))
		 (sender-state-n (system-sender sys)))
	      (=
	       (sender-state-cur (system-sender (system-s2r-tick-step (snd-r sys r))))
	       (+ r
		  (sender-state-cur (system-sender sys))))
	      (equal (system-receiver (system-s2r-tick-step (snd-r sys r)))
		     (system-receiver sys))))
	    (:drop 1)
	    (:use (:instance system-s2r-tick-step-definition-rule
			     (sys (snd-r sys r))))
	    :pro
	    (:claim (equal (system-s2r-tick-step (snd-r sys r))
			   (mset :s2r
				 (tbf-tick (system-s2r (snd-r sys r)))
				 (snd-r sys r))))
	    (:drop 1)
	    (:claim (== (system-s2r (mset :s2r
					  (tbf-tick (system-s2r (snd-r sys r)))
					  (snd-r sys r)))
			(tbf-tick (system-s2r (snd-r sys r)))))
	    (:use (:instance tbf-tick-definition-rule
			     (tbf (system-s2r (snd-r sys r)))))
	    (:use (:instance age-doesnt-care-about-bkt
			     (tbf (system-s2r (snd-r sys r)))
			     (b (min (+ (tbf-bkt (system-s2r (snd-r sys r)))
					(tbf-rat (system-s2r (snd-r sys r))))
				     (tbf-b-cap (system-s2r (snd-r sys r)))))))
	    :pro
	    (:claim (equal (tbf-tick (system-s2r (snd-r sys r)))
			   (mset :bkt
				 (min (+ (tbf-bkt (system-s2r (snd-r sys r)))
					 (tbf-rat (system-s2r (snd-r sys r))))
				      (tbf-b-cap (system-s2r (snd-r sys r))))
				 (tbf-age (system-s2r (snd-r sys r))))))
	    (:drop 2)
	    (:claim
	     (equal (tbf-data (mset :bkt
				    (min (+ (tbf-bkt (system-s2r (snd-r sys r)))
					    (tbf-rat (system-s2r (snd-r sys r))))
					 (tbf-b-cap (system-s2r (snd-r sys r))))
				    (tbf-age (system-s2r (snd-r sys r)))))
		    (tbf-data (tbf-age (system-s2r (snd-r sys r))))))
	    (:drop 1)
	    (:claim (== (tbf-data (tbf-tick (system-s2r (snd-r sys r))))
			(tbf-data (tbf-age (system-s2r (snd-r sys r))))))
	    (:drop 26 27)
	    (:use (:instance tbf-age-preserves-all-inf-all-1
			     (tbf (system-s2r (snd-r sys r)))))
	    (:use (:instance age-all-preserves-tdgs-poss
			     (tdgs (tbf-data (system-s2r (snd-r sys r))))))
	    :pro
	    (:claim
	     (and (all-inf (tbf-data (tbf-age (system-s2r (snd-r sys r)))))
		  (all-1 (tbf-data (tbf-age (system-s2r (snd-r sys r)))))
		  (equal (tdgs->poss (age-all (tbf-data (system-s2r (snd-r sys r)))))
			 (tdgs->poss (tbf-data (system-s2r (snd-r sys r)))))))
	    (:drop 1 2)
	    (:in-theory (enable tbf-age-definition-rule))
	    (:claim (== (tbf-data (tbf-age (system-s2r (snd-r sys r))))
			(age-all (tbf-data (system-s2r (snd-r sys r))))))
	    (:claim
	     (equal (tdgs->poss
		     (mget :data (mget :s2r (system-s2r-tick-step (snd-r sys r)))))
		    (tdgs->poss (mget :data (mget :s2r (snd-r sys r))))))
	    (:claim (= (mget :bkt (tbf-tick (system-s2r (snd-r sys r))))
		       b))
	    (:use (:instance tbf-tick-preserves-len-all-inf
			     (tbf (system-s2r (snd-r sys r)))))
	    :pro
	    (:claim (= (len (tbf-data (tbf-tick (system-s2r (snd-r sys r)))))
		       (len (tbf-data (system-s2r (snd-r sys r))))))
	    (:drop 1)
	    (:claim
	     (all-1 (mget :data (mget :s2r (system-s2r-tick-step (snd-r sys r))))))
	    (:claim
	     (all-inf (mget :data (mget :s2r (system-s2r-tick-step (snd-r sys r))))))
	    (:use (:instance tbf-tick-snd-r-preserves-len<=d-cap))
	    :pro
	    (:claim
	     (<= (len (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
		 (tbf-d-cap (system-s2r sys))))
	    (:drop 1)
	    :s
	    (:claim
	     (= (len (mget :data (mget :s2r (system-s2r-tick-step (snd-r sys r)))))
		(len (tbf-data (system-s2r (snd-r sys r))))))
	    (:use (:instance tdgs->poss-preserves-len
			     (tdgs (tbf-data (system-s2r (snd-r sys r))))))
	    :pro
	    (:claim
	     (= (len (mget :data (mget :s2r (system-s2r-tick-step (snd-r sys r)))))
		(len (tdgs->poss (tbf-data (system-s2r (snd-r sys r)))))))
	    (:use (:instance snd-r-moves-thru-simplification))
	    :pro
	    (:claim
	     (= (len (simplified-model-chan (snd-r-simplified (simplify sys) r)))
		(len (simplified-model-chan (simplify (snd-r sys r))))))
	    (:in-theory (enable simplify-definition-rule
				tdgs->poss-preserves-len))
	    (:use (:instance snd-r-simplified-incrs-len
			     (sm (simplify sys))))
	    :pro
	    (:claim
	     (= (len (simplified-model-chan (snd-r-simplified (simplify sys) r)))
		(min (+ (len (simplified-model-chan (simplify sys)))
			r)
		     (simplified-model-d-cap (simplify sys)))))
	    :prove))

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
  (dlv-b (system-s2r-tick-step (snd-R sys R)) b)
  :body-contracts-hints (("Goal" :use (:instance single-step-input-contracts))))

(propertyd dlv-b-simplified-doesnt-change-cur-hiA-N (sm :simplified-model b :nat)
	   :h (<= b (len (simplified-model-chan sm)))
	   (^ (= (simplified-model-cur (dlv-b-simplified sm b))
		 (simplified-model-cur sm))
	      (= (simplified-model-hiA (dlv-b-simplified sm b))
		 (simplified-model-hiA sm))
	      (= (simplified-model-N (dlv-b-simplified sm b))
		 (simplified-model-N sm)))
	   :instructions
	   ((:induct (dlv-b-simplified-decrs-inductor sm b))
	    :pro
	    (:use (:instance dlv-b-simplified-definition-rule))
	    :pro
	    (:claim (equal (dlv-b-simplified sm b)
			   (dlv-b-simplified (dlv-1-simplified sm)
					     (+ -1 b))))
	    (:drop 1)
	    (:claim (= (len (simplified-model-chan (dlv-1-simplified sm)))
		       (1- (len (simplified-model-chan sm)))))
	    (:claim (<= (+ -1 b)
			(len (simplified-model-chan (dlv-1-simplified sm)))))
	    (:claim
	     (and (= (simplified-model-cur (dlv-b-simplified (dlv-1-simplified sm)
							     (+ -1 b)))
		     (simplified-model-cur (dlv-1-simplified sm)))
		  (= (simplified-model-hia (dlv-b-simplified (dlv-1-simplified sm)
							     (+ -1 b)))
		     (simplified-model-hia (dlv-1-simplified sm)))
		  (= (simplified-model-n (dlv-b-simplified (dlv-1-simplified sm)
							   (+ -1 b)))
		     (simplified-model-n (dlv-1-simplified sm)))))
	    (:claim (= (simplified-model-cur (dlv-b-simplified sm b))
		       (simplified-model-cur (dlv-b-simplified (dlv-1-simplified sm)
							       (+ -1 b)))))
	    (:claim (= (simplified-model-hia (dlv-b-simplified sm b))
		       (simplified-model-hia (dlv-b-simplified (dlv-1-simplified sm)
							       (+ -1 b)))))
	    (:claim (= (simplified-model-n (dlv-b-simplified sm b))
		       (simplified-model-n (dlv-b-simplified (dlv-1-simplified sm)
							     (+ -1 b)))))
	    (:claim (= (simplified-model-cur (dlv-b-simplified sm b))
		       (simplified-model-cur sm)))
	    (:claim (= (simplified-model-hia (dlv-b-simplified sm b))
		       (simplified-model-hia sm)))
	    (:claim (= (simplified-model-n (dlv-b-simplified sm b))
		       (simplified-model-n sm)))
	    :prove
	    (:in-theory (enable dlv-b-simplified-definition-rule))
	    :prove))

;; First, let's handle the best case (b = R).
;; For this we are simply going to show that single-step-simplified increases
;; ack by R amount.
(property best-case-efficiency (sm :simplified-model R :pos)
  :h (^ (endp (simplified-model-chan sm))
	(<= (+ (simplified-model-cur sm) R)
	    (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= R (simplified-model-d-cap sm))
	(= (simplified-model-cur sm) (simplified-model-ack sm))
	(< 1 (simplified-model-cur sm)))
  (^
   ;; Contract checking nonsense
   (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm))
   (<= R (min R (simplified-model-d-cap sm)))
   (simplified-modelp (single-step-simplified sm R R))
   (posp (simplified-model-ack (single-step-simplified sm R R)))
   (posp (simplified-model-cur (single-step-simplified sm R R)))
   (<= (simplified-model-ack sm)
       (simplified-model-ack (single-step-simplified sm R R)))
   (!= (+ (simplified-model-ack (single-step-simplified sm r r))
	  (- (simplified-model-ack sm)))
       0)
   ;; Preserve input contracts
   (endp (simplified-model-chan (single-step-simplified sm R R)))
   (= (simplified-model-cur (single-step-simplified sm R R))
      (simplified-model-ack (single-step-simplified sm R R)))
   ;; Actual efficiency theorem
   (= (/ R (- (simplified-model-ack (single-step-simplified sm R R))
	      (simplified-model-ack sm)))
      1))
  :instructions
 ((:use (:instance single-step-simplified-definition-rule (b r)))
  (:use (:instance snd-r-simplified-cur))
  (:use (:instance snd-r-doesnt-change-consts))
  (:use (:instance snd-r-simplified-chan-effect-when-top-dn))
  :pro
  (:in-theory (enable top-dn-definition-rule))
  (:claim (equal (simplified-model-chan (snd-r-simplified sm r))
                 (top-dn (+ -1 r (simplified-model-cur sm))
                         (+ r (len (simplified-model-chan sm))))))
  (:use (:instance
        dlv-b-simplified-prefix-top-dn (b r)
        (prefix nil)
        (sm (snd-r-simplified sm r))))
  (:in-theory (enable dlv-b-simplified-definition-rule
                      dlv-1-simplified-definition-rule))
  (:use (:instance dlv-b-simplified-doesnt-change-cur-hia-n
                   (sm (snd-r-simplified sm r))
                   (b r)))
  :prove))

(propertyd pos-1+pos=pos (p0 p1 :pos) (posp (+ (1- p0) p1)))

(propertyd ackpos (sm :simplified-model) (posp (simplified-model-ack sm)))

(propertyd overtransmission-filling-contracts (sm :simplified-model R b :pos)
	   :h (^ (<= b R)
		 (<= R (simplified-model-d-cap sm))
		 (<= (+ (len (simplified-model-chan sm)) R)
		     (simplified-model-d-cap sm))
		 (<= (+ (simplified-model-cur sm) R)
		     (+ (simplified-model-hiA sm) (simplified-model-N sm)))
		 (== (simplified-model-chan sm)
		     (if (simplified-model-chan sm)
			 (top-dn (+ (1- (len (simplified-model-chan sm)))
				    (simplified-model-ack sm))
				 (len (simplified-model-chan sm)))
		       nil))
		 (= (simplified-model-cur sm)
		    (+ (len (simplified-model-chan sm))
		       (simplified-model-ack sm))))
	   (^ (simplified-modelp (single-step-simplified sm R b))
	      (if (! (endp (simplified-model-chan (single-step-simplified sm r b))))
		  (posp (+ (1- (len (simplified-model-chan (single-step-simplified sm r b))))
			   (simplified-model-ack (single-step-simplified sm r b))))
		t))
	   :hints (("Goal" :use ((:instance pos-1+pos=pos
					    (p0 (len (simplified-model-chan (single-step-simplified sm r b))))
					    (p1 (simplified-model-ack (single-step-simplified sm r b))))
				 (:instance ackpos (sm (single-step-simplified sm r b)))))))

(propertyd snd-r-simplified-chan-effect-when-empty (sm :simplified-model R :pos)
	   :h (^ (< (1- (+ R (len (simplified-model-chan sm)))) (simplified-model-d-cap sm))
		 (<= (+ R (simplified-model-cur sm))
		     (+ (simplified-model-hia sm)
			(simplified-model-n sm)))
		 (<= (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
		 (endp (simplified-model-chan sm)))
	   (== (simplified-model-chan (snd-R-simplified sm R))
	       (top-dn (1- (+ R (simplified-model-cur sm)))
		       (+ R (len (simplified-model-chan sm)))))
	   :instructions
	   ((:use (:instance snd-r-simplified-definition-rule))
	    (:use (:instance snd-1-simplified-definition-rule))
	    (:casesplit (= r 1))
	    (:use (:instance snd-r-simplified-definition-rule
			     (sm (snd-1-simplified sm))
			     (r (1- r))))
	    (:in-theory (enable top-dn-definition-rule))
	    
	    :prove
	    (:use (:instance snd-r-simplified-chan-effect-when-top-dn
			     (sm (snd-1-simplified sm))
			     (r (1- r))))
	    
	    :prove))

#|
Suppose that the channel is [ack + k, ack + k - 1, ..., ack]
Suppose further that k + R <= d-cap
Then after single-step-simplified, the channel is [ack + k + R, ..., ack + b]
|#
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
       (+ b (simplified-model-ack sm)))))
  :instructions
  ((:use (:instance snd-r-simplified-chan-effect-when-empty))
   (:use (:instance snd-r-simplified-chan-effect-when-top-dn))
   (:use (:instance single-step-simplified-definition-rule))
   (:use (:instance snd-r-simplified-cur))
   (:use (:instance snd-r-doesnt-change-consts))
   (:use (:instance dlv-b-simplified-prefix-top-dn
		    (prefix (top-dn (+ -1 r (simplified-model-cur sm))
				    (+ (len (simplified-model-chan sm))
				       r (- b))))
		    (sm (snd-r-simplified sm r))))
   (:use (:instance top-dn-append (rem b)
		    (mid (+ (+ -1 b)
			    (simplified-model-ack (snd-r-simplified sm r))))
		    (up (+ r (len (simplified-model-chan sm))
			   (- b)))))
   
   (:use (:instance dlv-b-simplified-doesnt-change-cur-hia-n
		    (sm (snd-r-simplified sm r))))
   (:in-theory (enable top-dn-len))
   :prove))

(propertyd car-top-dn (top rem :pos)
	   :h (<= rem top)
	   (^ (consp (top-dn top rem))
	      (= (car (top-dn top rem)) top))
	   :hints (("Goal" :in-theory (enable top-dn-definition-rule))))


;; Next let's look at the step where it over-fills.  What happens then?
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
      (^ (== (simplified-model-chan (single-step-simplified sm r b))
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
	 (! (in (+ (- (simplified-model-d-cap sm)
		      (len (simplified-model-chan sm)))
		   (simplified-model-cur sm))
		(simplified-model-chan (single-step-simplified sm r b))))
	 (< (car (simplified-model-chan (single-step-simplified sm r b)))
	    (+ (- (simplified-model-d-cap sm)
		  (len (simplified-model-chan sm)))
	       (simplified-model-cur sm)))))
  :instructions
  (:pro
   (:claim (! (endp (simplified-model-chan sm))))
   (:use (:instance snd-r-simplified-chan-effect-when-top-dn
		    (r (- (simplified-model-d-cap sm)
			  (len (simplified-model-chan sm))))))
   :pro
   (:claim
    (equal (simplified-model-chan
	    (snd-r-simplified sm
			      (+ (simplified-model-d-cap sm)
				 (- (len (simplified-model-chan sm))))))
	   (top-dn (+ -1
		      (+ (simplified-model-d-cap sm)
			 (- (len (simplified-model-chan sm))))
		      (simplified-model-cur sm))
		   (+ (+ (simplified-model-d-cap sm)
			 (- (len (simplified-model-chan sm))))
		      (len (simplified-model-chan sm))))))
   (:drop 1)
   (:use (:instance
	  snd-r-does-nothing-when-full
	  (sm (snd-r-simplified sm
				(+ (simplified-model-d-cap sm)
				   (- (len (simplified-model-chan sm))))))
	  (r (- r
		(+ (simplified-model-d-cap sm)
		   (- (len (simplified-model-chan sm))))))))
   (:use (:instance snd-r-doesnt-change-consts
		    (r (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm)))))))
   (:use (:instance snd-r-simplified-cur
		    (r (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm)))))))
   :pro
   (:claim
    (equal
     (simplified-model-chan
      (snd-r-simplified
       (snd-r-simplified sm
			 (+ (simplified-model-d-cap sm)
			    (- (len (simplified-model-chan sm)))))
       (+ r
	  (- (+ (simplified-model-d-cap sm)
		(- (len (simplified-model-chan sm))))))))
     (simplified-model-chan
      (snd-r-simplified sm
			(+ (simplified-model-d-cap sm)
			   (- (len (simplified-model-chan sm))))))))
   (:drop 3)
   (:use (:instance snd-r-snd-r=snd-r+r
		    (r0 (+ (simplified-model-d-cap sm)
			   (- (len (simplified-model-chan sm)))))
		    (r1 (- r
			   (+ (simplified-model-d-cap sm)
			      (- (len (simplified-model-chan sm))))))))
   :pro
   (:claim
    (equal (snd-r-simplified
	    (snd-r-simplified sm
			      (+ (simplified-model-d-cap sm)
				 (- (len (simplified-model-chan sm)))))
	    (+ r
	       (- (+ (simplified-model-d-cap sm)
		     (- (len (simplified-model-chan sm)))))))
	   (snd-r-simplified sm r)))
   (:drop 1)
   (:claim (== (simplified-model-chan (snd-r-simplified sm r))
	       (top-dn (+ -1
			  (+ (simplified-model-d-cap sm)
			     (- (len (simplified-model-chan sm))))
			  (simplified-model-cur sm))
		       (simplified-model-d-cap sm))))
   (:use (:instance top-dn-append
		    (up (- (simplified-model-d-cap sm) b))
		    (mid (- (+ -1
			       (- (simplified-model-d-cap sm)
				  (len (simplified-model-chan sm)))
			       (simplified-model-cur sm))
			    (- (simplified-model-d-cap sm) b)))
		    (rem b)))
   :pro
   (:claim (== (simplified-model-chan (snd-r-simplified sm r))
	       (app (top-dn (+ (+ (+ -1
				     (+ (simplified-model-d-cap sm)
					(- (len (simplified-model-chan sm))))
				     (simplified-model-cur sm))
				  (- (+ (simplified-model-d-cap sm) (- b))))
			       (simplified-model-d-cap sm)
			       (- b))
			    (+ (simplified-model-d-cap sm) (- b)))
		    (top-dn (+ (+ -1
				  (+ (simplified-model-d-cap sm)
				     (- (len (simplified-model-chan sm))))
				  (simplified-model-cur sm))
			       (- (+ (simplified-model-d-cap sm) (- b))))
			    b))))
   (:drop 1)
   (:use
    (:instance
     dlv-b-simplified-prefix-top-dn
     (prefix (top-dn (+ (+ (+ -1
			      (+ (simplified-model-d-cap sm)
				 (- (len (simplified-model-chan sm))))
			      (simplified-model-cur sm))
			   (- (+ (simplified-model-d-cap sm) (- b))))
			(simplified-model-d-cap sm)
			(- b))
		     (+ (simplified-model-d-cap sm) (- b))))
     (sm (snd-r-simplified sm r))))
   (:use (:instance dlv-b-simplified-doesnt-change-cur-hia-n
		    (sm (snd-r-simplified sm r))))
   (:in-theory (enable top-dn-len))
   :pro
   (:claim (= (+ (+ (+ -1
		       (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm))))
		       (simplified-model-cur sm))
		    (- (+ (simplified-model-d-cap sm) (- b))))
		 (simplified-model-d-cap sm)
		 (- b))
	      (+ (+ (+ -1
		       (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm))))
		       (simplified-model-cur sm))
		    (- (+ (simplified-model-d-cap sm) (- b))))
		 (simplified-model-d-cap sm)
		 (- b))))
   (:claim (= (simplified-model-cur sm)
	      (+ (len (simplified-model-chan sm))
		 (simplified-model-ack sm))))
   (:use (:instance snd-r-simplified-consts))
   :pro
   (:claim (== (simplified-model-chan (snd-r-simplified sm r))
	       (app (top-dn (+ (+ (+ -1
				     (+ (simplified-model-d-cap sm)
					(- (len (simplified-model-chan sm))))
				     (simplified-model-cur sm))
				  (- (+ (simplified-model-d-cap sm) (- b))))
			       (simplified-model-d-cap sm)
			       (- b))
			    (+ (simplified-model-d-cap sm) (- b)))
		    (top-dn (+ (+ -1 b)
			       (simplified-model-ack (snd-r-simplified sm r)))
			    b))))
   (:claim
    (and
     (= (simplified-model-ack (dlv-b-simplified (snd-r-simplified sm r)
						b))
	(+ b
	   (simplified-model-ack (snd-r-simplified sm r))))
     (equal (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r)
						     b))
	    (top-dn (+ (+ (+ -1
			     (+ (simplified-model-d-cap sm)
				(- (len (simplified-model-chan sm))))
			     (simplified-model-cur sm))
			  (- (+ (simplified-model-d-cap sm) (- b))))
		       (simplified-model-d-cap sm)
		       (- b))
		    (+ (simplified-model-d-cap sm)
		       (- b))))))
   (:use (:instance snd-r-doesnt-change-consts))
   (:use (:instance snd-r-simplified-cur))
   :pro
   (:claim (= (simplified-model-cur (snd-r-simplified sm r))
	      (+ (simplified-model-cur sm) r)))
   (:drop 1)
   (:claim
    (and (= (simplified-model-cur (dlv-b-simplified (snd-r-simplified sm r)
						    b))
	    (simplified-model-cur (snd-r-simplified sm r)))
	 (= (simplified-model-hia (dlv-b-simplified (snd-r-simplified sm r)
						    b))
	    (simplified-model-hia (snd-r-simplified sm r)))
	 (= (simplified-model-n (dlv-b-simplified (snd-r-simplified sm r)
						  b))
	    (simplified-model-n (snd-r-simplified sm r)))))
   (:drop 1)
   (:in-theory (enable single-step-simplified-definition-rule))
   (:claim (== (single-step-simplified sm r b)
	       (dlv-b-simplified (snd-r-simplified sm r)
				 b)))
   (:claim (= (simplified-model-cur (single-step-simplified sm r b))
	      (+ r (simplified-model-cur sm))))
   (:claim (= (simplified-model-ack (single-step-simplified sm r b))
	      (+ b (simplified-model-ack sm))))
   (:claim (< (+ (+ (simplified-model-d-cap sm)
		    (- (len (simplified-model-chan sm))))
		 (simplified-model-cur sm))
	      (simplified-model-cur (single-step-simplified sm r b))))
   (:in-theory (enable top-dn-definition-rule))
   (:claim (< (+ (+ (+ -1
		       (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm))))
		       (simplified-model-cur sm))
		    (- (+ (simplified-model-d-cap sm) (- b))))
		 (simplified-model-d-cap sm)
		 (- b))
	      (+ (+ (simplified-model-d-cap sm)
		    (- (len (simplified-model-chan sm))))
		 (simplified-model-cur sm))))
   (:use (:instance top-dn-doesnt-go-up
		    (top (+ (+ (+ -1
				  (+ (simplified-model-d-cap sm)
				     (- (len (simplified-model-chan sm))))
				  (simplified-model-cur sm))
			       (- (+ (simplified-model-d-cap sm) (- b))))
			    (simplified-model-d-cap sm)
			    (- b)))
		    (rem (+ (simplified-model-d-cap sm) (- b)))
		    (x (+ (+ (simplified-model-d-cap sm)
			     (- (len (simplified-model-chan sm))))
			  (simplified-model-cur sm)))))
   :pro
   (:claim (not (in (+ (+ (simplified-model-d-cap sm)
			  (- (len (simplified-model-chan sm))))
		       (simplified-model-cur sm))
		    (simplified-model-chan (single-step-simplified sm r b)))))
   (:use (:instance car-top-dn
		    (top (+ (+ (+ -1
				  (+ (simplified-model-d-cap sm)
				     (- (len (simplified-model-chan sm))))
				  (simplified-model-cur sm))
			       (- (+ (simplified-model-d-cap sm) (- b))))
			    (simplified-model-d-cap sm)
			    (- b)))
		    (rem (+ (simplified-model-d-cap sm) (- b)))))
   :prove))

(propertyd set-bkt-doesnt-change-d-cap (b :nat tbf :tbf)
	   (= (tbf-d-cap (mset :bkt b tbf)) (tbf-d-cap tbf)))

(propertyd system-s2r-tick-step-moves-thru-simplification (sys :system)
	   :h (^ (! (natp (tbf-del (system-s2r sys))))
		 (all-inf (tbf-data (system-s2r sys))))
	   (== (simplify (system-s2r-tick-step sys)) (simplify sys))
	   :instructions
 ((:use (:instance system-s2r-tick-step-definition-rule))
  (:use (:instance simplify-definition-rule (sys (system-s2r-tick-step sys))))
  (:use (:instance tbf-tick-definition-rule (tbf (system-s2r sys))))
  (:use (:instance tbf-age-definition-rule (tbf (system-s2r sys))))
  (:use (:instance all-nz->age-all->dgs->poss= (dgs (tbf-data (system-s2r sys)))))
  (:use (:instance all-inf->all-nz (tdgs (tbf-data (system-s2r sys)))))
  (:use (:instance simplify-definition-rule))
  :pro
  (:claim (== (system-s2r (system-s2r-tick-step sys))
              (tbf-tick (system-s2r sys))))
  (:claim (== (tdgs->poss (tbf-data (system-s2r (system-s2r-tick-step sys))))
              (tdgs->poss (tbf-data (tbf-tick (system-s2r sys))))))
  (:use (:instance age-doesnt-care-about-bkt
                   (b (min (+ (tbf-bkt (system-s2r sys))
                              (tbf-rat (system-s2r sys)))
                           (tbf-b-cap (system-s2r sys))))
                   (tbf (system-s2r sys))))
  :pro
  (:claim (equal (tbf-data (mset :bkt
                                 (min (+ (tbf-bkt (system-s2r sys))
                                         (tbf-rat (system-s2r sys)))
                                      (tbf-b-cap (system-s2r sys)))
                                 (tbf-age (system-s2r sys))))
                 (tbf-data (tbf-age (system-s2r sys)))))
  (:drop 1)
  (:claim (== (tbf-data (tbf-age (system-s2r sys)))
              (tbf-data (tbf-tick (system-s2r sys)))))
  (:claim (== (tdgs->poss (tbf-data (system-s2r (system-s2r-tick-step sys))))
              (tdgs->poss (tbf-data (system-s2r sys)))))
  (:claim (= (tbf-d-cap (system-s2r (system-s2r-tick-step sys)))
             (tbf-d-cap (tbf-tick (system-s2r sys)))))
  (:use (:instance set-bkt-doesnt-change-d-cap
                   (b (min (+ (tbf-bkt (system-s2r sys))
                              (tbf-rat (system-s2r sys)))
                           (tbf-b-cap (system-s2r sys))))
                   (tbf (tbf-age (system-s2r sys)))))
  :pro
  (:claim (= (tbf-d-cap (mset :bkt
                              (min (+ (tbf-bkt (system-s2r sys))
                                      (tbf-rat (system-s2r sys)))
                                   (tbf-b-cap (system-s2r sys)))
                              (tbf-age (system-s2r sys))))
             (tbf-d-cap (tbf-age (system-s2r sys)))))
  (:drop 1)
  (:claim (= (tbf-d-cap (tbf-tick (system-s2r sys)))
             (tbf-d-cap (tbf-age (system-s2r sys)))))
  (:claim (= (tbf-d-cap (tbf-age (system-s2r sys)))
             (tbf-d-cap (system-s2r sys))))
  (:claim (== (system-sender (system-s2r-tick-step sys))
              (system-sender sys)))
  (:claim (== (system-receiver (system-s2r-tick-step sys))
              (system-receiver sys)))
  :prove))

(propertyd simplify-destructor (sys :system)
	   (^ (= (simplified-model-d-cap (simplify sys))
                            (tbf-d-cap (system-s2r sys)))
                         (= (simplified-model-ack (simplify sys))
                            (+ 1 (maxl (system-receiver sys))))
                         (= (simplified-model-cur (simplify sys))
                            (sender-state-cur (system-sender sys)))
                         (= (simplified-model-hia (simplify sys))
                            (sender-state-hia (system-sender sys)))
                         (= (simplified-model-n (simplify sys))
                            (sender-state-n (system-sender sys))))
	   :hints (("Goal" :in-theory (enable simplify-definition-rule))))

(defthm single-step-moves-thru-simplification
  (=> (^ (systemp sys)
	 (posp R)
	 (or (endp (system-receiver sys))
	     (equal (system-receiver sys)
		    (top-dn (maxl (system-receiver sys))
			    (maxl (system-receiver sys)))))
	 (<= (+ (sender-state-cur (system-sender sys))
		r)
	     (+ (sender-state-hia (system-sender sys))
		(sender-state-n (system-sender sys))))
	 (all-inf (tbf-data (system-s2r sys)))
	 (all-1 (tbf-data (system-s2r sys)))
	 (not (natp (tbf-del (system-s2r sys))))
	 (<= (tbf-b-cap (system-s2r sys))
	     (min r (tbf-d-cap (system-s2r sys))))
	 (= (tbf-b-cap (system-s2r sys))
	    (tbf-rat (system-s2r sys)))
	 (<= (tbf-bkt (system-s2r sys))
	     (tbf-b-cap (system-s2r sys)))
	 (<= (tbf-b-cap (system-s2r sys))
	     (tbf-d-cap (system-s2r sys)))
	 (<= (len (tbf-data (system-s2r sys)))
	     (tbf-d-cap (system-s2r sys))))
      (== (simplify (single-step sys r (tbf-b-cap (system-s2r sys))))
	  (single-step-simplified (simplify sys)
				  r (tbf-b-cap (system-s2r sys)))))
  :instructions
  ((:use (:instance single-step-definition-rule
		    (b (tbf-b-cap (system-s2r sys)))))
   :pro
   (:claim (equal (single-step sys r (tbf-b-cap (system-s2r sys)))
		  (dlv-b (system-s2r-tick-step (snd-r sys r))
			 (tbf-b-cap (system-s2r sys)))))
   (:drop 1)
   (:use (:instance snd-r-moves-thru-simplification))
   :pro
   (:claim (equal (snd-r-simplified (simplify sys) r)
		  (simplify (snd-r sys r))))
   (:drop 1)
   (:use (:instance system-s2r-tick-step-moves-thru-simplification
		    (sys (snd-r sys r))))
   (:use (:instance inf-1-inv-snd-r))
   (:use (:instance snd-r-effect-helper))
   :pro
   (:claim (and (= (tbf-bkt (system-s2r (snd-r sys r)))
		   (tbf-bkt (system-s2r sys)))
		(= (tbf-b-cap (system-s2r (snd-r sys r)))
		   (tbf-b-cap (system-s2r sys)))
		(= (tbf-d-cap (system-s2r (snd-r sys r)))
		   (tbf-d-cap (system-s2r sys)))
		(= (tbf-rat (system-s2r (snd-r sys r)))
		   (tbf-rat (system-s2r sys)))
		(equal (tbf-del (system-s2r (snd-r sys r)))
		       (tbf-del (system-s2r sys)))
		(= (sender-state-n (system-sender (snd-r sys r)))
		   (sender-state-n (system-sender sys)))
		(= (sender-state-hia (system-sender (snd-r sys r)))
		   (sender-state-hia (system-sender sys)))
		(= (sender-state-cur (system-sender (snd-r sys r)))
		   (+ (sender-state-cur (system-sender sys))
		      r))
		(equal (system-receiver (snd-r sys r))
		       (system-receiver sys))))
   (:drop 1)
   (:claim (^ (all-inf (tbf-data (system-s2r (snd-r sys r))))
	      (all-1 (tbf-data (system-s2r (snd-r sys r))))
	      (equal (simplify (system-s2r-tick-step (snd-r sys r)))
		     (simplify (snd-r sys r)))))
   (:drop 1 2)
   (:use (:instance dlv-b-moves-thru-simplification
		    (sys (system-s2r-tick-step (snd-r sys r)))
		    (b (tbf-b-cap (system-s2r sys)))))
   (:use (:instance system-s2r-tick-step-after-snd-r-effect))
   :pro
   (:claim
    (and
     (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-b-cap (system-s2r sys)))
     (= (tbf-b-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-b-cap (system-s2r sys)))
     (= (tbf-d-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-d-cap (system-s2r sys)))
     (= (tbf-rat (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-rat (system-s2r sys)))
     (equal (tbf-del (system-s2r (system-s2r-tick-step (snd-r sys r))))
	    (tbf-del (system-s2r sys)))
     (= (sender-state-n (system-sender (system-s2r-tick-step (snd-r sys r))))
	(sender-state-n (system-sender sys)))
     (=
      (sender-state-cur (system-sender (system-s2r-tick-step (snd-r sys r))))
      (+ r
	 (sender-state-cur (system-sender sys))))
     (equal (system-receiver (system-s2r-tick-step (snd-r sys r)))
	    (system-receiver sys))))
   (:drop 1)
   (:use (:instance single-step-input-contracts
		    (b (tbf-b-cap (system-s2r sys)))))
   :pro
   (:claim
    (and
     (systemp (snd-r sys r))
     (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-b-cap (system-s2r sys)))
     (= (tbf-b-cap (system-s2r sys))
	(tbf-b-cap (system-s2r sys)))
     (all-inf (tbf-data (system-s2r (snd-r sys r))))
     (all-1 (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
     (all-inf (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
     (equal (tdgs->poss
	     (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
	    (tdgs->poss (tbf-data (system-s2r (snd-r sys r)))))
     (<= (len (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r)))))
	 (tbf-d-cap (system-s2r sys)))
     (= (tbf-d-cap (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-d-cap (system-s2r sys)))
     (= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
	(tbf-b-cap (system-s2r sys)))
     (<= (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))
	 (len (tbf-data (system-s2r (system-s2r-tick-step (snd-r sys r))))))))
   (:drop 1)
   (:claim (= (tbf-b-cap (system-s2r sys))
	      (tbf-bkt (system-s2r (system-s2r-tick-step (snd-r sys r))))))
   (:claim
    (or
     (endp (system-receiver (system-s2r-tick-step (snd-r sys r))))
     (equal
      (system-receiver (system-s2r-tick-step (snd-r sys r)))
      (top-dn
       (maxl (system-receiver (system-s2r-tick-step (snd-r sys r))))
       (maxl (system-receiver (system-s2r-tick-step (snd-r sys r))))))))
   (:claim
    (and
     (<= (tbf-b-cap (system-s2r sys))
	 (len (simplified-model-chan
	       (simplify (system-s2r-tick-step (snd-r sys r))))))
     (equal (simplify (dlv-b (system-s2r-tick-step (snd-r sys r))
			     (tbf-b-cap (system-s2r sys))))
	    (dlv-b-simplified (simplify (system-s2r-tick-step (snd-r sys r)))
			      (tbf-b-cap (system-s2r sys))))))
   (:drop 1)
   (:claim
    (== (dlv-b-simplified (simplify (system-s2r-tick-step (snd-r sys r)))
			  (tbf-b-cap (system-s2r sys)))
	(dlv-b-simplified (simplify (snd-r sys r))
			  (tbf-b-cap (system-s2r sys)))))
   (:claim (== (dlv-b-simplified (simplify (snd-r sys r))
				 (tbf-b-cap (system-s2r sys)))
	       (dlv-b-simplified (snd-r-simplified (simplify sys) r)
				 (tbf-b-cap (system-s2r sys)))))
   (:use (:instance single-step-definition-rule
		    (b (tbf-b-cap (system-s2r sys)))))
   (:use (:instance single-step-simplified-definition-rule
		    (sm (simplify sys))
		    (b (tbf-b-cap (system-s2r sys)))))
   :pro
   (:claim (equal (single-step sys r (tbf-b-cap (system-s2r sys)))
		  (dlv-b (system-s2r-tick-step (snd-r sys r))
			 (tbf-b-cap (system-s2r sys)))))
   (:drop 2)
   (:use (:instance simplify-definition-rule))
   (:use (:instance tdgs->poss-preserves-len
		    (tdgs (tbf-data (system-s2r sys)))))
   :pro
   (:claim (<= (len (simplified-model-chan (simplify sys)))
	       (simplified-model-d-cap (simplify sys))))
   (:in-theory (enable simplify-definition-rule))
   (:claim (equal (simplify sys)
		  (simplified-model (tdgs->poss (tbf-data (system-s2r sys)))
				    (tbf-d-cap (system-s2r sys))
				    (+ 1 (maxl (system-receiver sys)))
				    (sender-state-cur (system-sender sys))
				    (sender-state-hia (system-sender sys))
				    (sender-state-n (system-sender sys)))))
   (:drop 2)
   (:claim (^ (= (simplified-model-d-cap (simplify sys))
		 (tbf-d-cap (system-s2r sys)))
	      (= (simplified-model-ack (simplify sys))
		 (+ 1 (maxl (system-receiver sys))))
	      (= (simplified-model-cur (simplify sys))
		 (sender-state-cur (system-sender sys)))
	      (= (simplified-model-hia (simplify sys))
		 (sender-state-hia (system-sender sys)))
	      (= (simplified-model-n (simplify sys))
		 (sender-state-n (system-sender sys)))))
   (:use (:instance simplify-destructor))
   :pro
   (:claim (and (= (simplified-model-d-cap (simplify sys))
		   (tbf-d-cap (system-s2r sys)))
		(= (simplified-model-ack (simplify sys))
		   (+ 1 (maxl (system-receiver sys))))
		(= (simplified-model-cur (simplify sys))
		   (sender-state-cur (system-sender sys)))
		(= (simplified-model-hia (simplify sys))
		   (sender-state-hia (system-sender sys)))
		(= (simplified-model-n (simplify sys))
		   (sender-state-n (system-sender sys)))))
   (:drop 1)
   (:claim (=> (^ (<= (tbf-b-cap (system-s2r sys))
		      (min r (tbf-d-cap (system-s2r sys))))
		  (= (tbf-d-cap (system-s2r sys))
		     (simplified-model-d-cap (simplify sys))))
	       (<= (tbf-b-cap (system-s2r sys))
		   (min r
			(simplified-model-d-cap (simplify sys))))))
   (:claim (<= (tbf-b-cap (system-s2r sys))
	       (min r
		    (simplified-model-d-cap (simplify sys)))))
   :prove))
