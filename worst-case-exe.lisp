(in-package "ACL2S")
(include-book "gobackn")

;; (msets blarg :key0 val0 :key1 val1 ...)

#|
---------- Define simplification map ----------
|#

(defdata simplified-model
  (record (chan . poss)
	  (lcap . nat)
	  (rcvd . poss)
	  (cur . pos)
	  (hiA . pos)
	  (N . pos)))

(definecd simplify (sys :system) :simplified-model
  (simplified-model (dgs->poss (tbf-D (system-s2r sys)))
		    (tbf-l-cap (system-s2r sys))
		    (system-receiver sys)
		    (sender-state-cur (system-sender sys))
		    (sender-state-hiA (system-sender sys))
		    (sender-state-N (system-sender sys))))

#|
---------- Define "snd 1" transition & its image ----------
|#

;; Send just cur
(definecd snd-1 (sys :system) :system
  :ic (< (sender-state-cur (system-sender sys))
	 (+ (sender-state-hiA (system-sender sys))
	    (sender-state-N (system-sender sys))))
  (mset :s2r (tbf-trn (system-s2r sys) (sender-state-cur (system-sender sys)) nil)
	(mset :sender (sender-snd-cur (system-sender sys))
	      sys)))

(definecd snd-1-simplified (sm :simplified-model) :simplified-model
  :ic (< (simplified-model-cur sm) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (mset :chan
	(if (< (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	    (cons (simplified-model-cur sm) (simplified-model-chan sm))
	  (simplified-model-chan sm))
	(mset :cur (1+ (simplified-model-cur sm))
	      sm)))

#|
---------- Prove "snd 1" moves thru simplification ----------
|#

(property simplification-contracts-snd-1 (sys :system)
  :h (< (sender-state-cur (system-sender sys))
	(+ (sender-state-hiA (system-sender sys))
	   (sender-state-N (system-sender sys))))
  (^ (= (sender-state-cur (system-sender sys)) (simplified-model-cur (simplify sys)))
     (= (sender-state-hiA (system-sender sys)) (simplified-model-hiA (simplify sys)))
     (= (sender-state-N (system-sender sys)) (simplified-model-N (simplify sys))))
  :hints (("Goal" :in-theory (enable simplify-definition-rule))))

;; Characterize effect of snd-1
(property snd-1-effect (sys :system)
  :h (< (sender-state-cur (system-sender sys))
	   (+ (sender-state-hiA (system-sender sys))
	      (sender-state-N (system-sender sys))))
  (^ (equal (dgs->poss (tbf-D (system-s2r (snd-1 sys))))
	    (if (< (len (tbf-D (system-s2r sys))) (tbf-l-cap (system-s2r sys)))
		(cons (sender-state-cur (system-sender sys))
		      (dgs->poss (tbf-D (system-s2r sys))))
	      (dgs->poss (tbf-D (system-s2r sys)))))
     (= (len (tbf-D (system-s2r (snd-1 sys))))
	(if (< (len (tbf-D (system-s2r sys))) (tbf-l-cap (system-s2r sys)))
	    (1+ (len (tbf-D (system-s2r sys))))
	  (len (tbf-D (system-s2r sys)))))
     (= (sender-state-cur (system-sender (snd-1 sys)))
	(1+ (sender-state-cur (system-sender sys))))
     (= (sender-state-hiA (system-sender (snd-1 sys)))
	(sender-state-hiA (system-sender sys)))
     (= (sender-state-N (system-sender (snd-1 sys)))
	(sender-state-N (system-sender sys)))
     (equal (tbf-ttl (system-s2r (snd-1 sys))) (tbf-ttl (system-s2r sys)))
     (= (tbf-l-cap (system-s2r (snd-1 sys))) (tbf-l-cap (system-s2r sys)))
     (= (tbf-b-cap (system-s2r (snd-1 sys))) (tbf-b-cap (system-s2r sys)))
     (= (tbf-b (system-s2r (snd-1 sys))) (tbf-b (system-s2r sys)))
     (= (tbf-r (system-s2r (snd-1 sys))) (tbf-r (system-s2r sys))))
  :hints (("Goal" :in-theory (enable snd-1-definition-rule
				     tbf-trn-definition-rule
				     sender-snd-cur-definition-rule))))

(property simplification-preserves-snd-1 (sys :system)
  :h (< (sender-state-cur (system-sender sys))
	(+ (sender-state-hiA (system-sender sys))
	   (sender-state-N (system-sender sys))))
  (^ ;; simplification preserves the precondition
   (< (simplified-model-cur (simplify sys))
      (+ (simplified-model-hia (simplify sys))
	 (simplified-model-n (simplify sys))))
   ;; simplification can move through transition
   (equal (simplify (snd-1 sys)) (snd-1-simplified (simplify sys))))
  :instructions ((:use (:instance simplification-contracts-snd-1))
		 (:use (:instance snd-1-effect))
		 :pro
		 (:in-theory (enable simplify-definition-rule))
		 (:claim (equal (simplified-model-chan (simplify (snd-1 sys)))
				(dgs->poss (tbf-d (system-s2r (snd-1 sys))))))
		 :prove))

#|
---------- Define "dlv 1" transition & its image ----------
|#
(definecd dlv-1 (sys :system) :system
  :ic (^ (posp (tbf-b (system-s2r sys)))
	 (consp (tbf-D (system-s2r sys))))
  (mset :s2r (tbf-dlv (system-s2r sys) (1- (len (tbf-D (system-s2r sys))))) sys))

(definecd dlv-1-simplified (sm :simplified-model) :simplified-model
  :ic (consp (simplified-model-chan sm))
  (mset :chan
	(remove-ith (simplified-model-chan sm)
		    (1- (len (simplified-model-chan sm))))
	sm)
  :function-contract-hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

#|
---------- Prove "dlv 1" moves thru simplification ----------
Important caveat: We will ignore the bucket in the simplification.
However, later, I will prove that this is acceptable.
|#
(property simplification-preserves-dlv-1 (sys :system)
  :h (^ (posp (tbf-b (system-s2r sys)))
	(consp (tbf-D (system-s2r sys))))
  (^ (consp (simplified-model-chan (simplify sys)))
     (equal (simplify (dlv-1 sys))
	    (dlv-1-simplified (simplify sys))))
  :instructions ((:in-theory (enable dlv-1-definition-rule
                                     dlv-1-simplified-definition-rule
                                     simplify-definition-rule
                                     tbf-dlv-definition-rule
                                     remove-ith-definition-rule
                                     dgs->poss-definition-rule))
                 :pro
                 (:claim (equal (simplified-model-chan (simplify sys))
                                (dgs->poss (tbf-d (system-s2r sys)))))
                 :prove))

#|
---------- Define "snd-r-simplified" and characterize what it does to chan -----------
|#
(definecd snd-R-simplified (sm :simplified-model R :nat) :simplified-model
  :ic (< (+ (simplified-model-cur sm) R)
	 (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (if (= R 0) sm (snd-R-simplified (snd-1-simplified sm) (1- R)))
  :body-contracts-hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

;; Claim that snd-R-simplified and snd-1-simplified commute.
(definecd snd-R-simplify-inductor (sys :system R :nat) :nat
  (if (= R 0) 0 (1+ (snd-R-simplify-inductor sys (1- R)))))

(property snd-R-1-simplified-contracts (sm :simplified-model R :nat)
  :h (< (+ (simplified-model-cur sm) (1+ R))
	(+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (< (simplified-model-cur (snd-r-simplified sm R))
     (+ (simplified-model-hia (snd-r-simplified sm R))
	(simplified-model-n (snd-r-simplified sm R))))
  :hints (("Goal" :in-theory (enable snd-r-simplified-definition-rule
				     snd-1-simplified-definition-rule))))

(property snd-R-1-simplified-inductor-contracts (sm :simplified-model R :nat)
  :h (< (+ (simplified-model-cur sm) (1+ R))
	(+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (if (= R 0) t
    (^ (< (simplified-model-cur sm) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
       (< (+ (simplified-model-cur (snd-1-simplified sm)) R)
	  (+ (simplified-model-hiA (snd-1-simplified sm))
	     (simplified-model-N (snd-1-simplified sm))))
       (natp (1- R))))
  :hints (("Goal" :use ((:instance simplification-contracts-snd-1)
			(:instance snd-R-1-simplified-contracts))
	   :in-theory (enable snd-1-simplified-definition-rule
			      snd-R-simplified-definition-rule))))

(definecd snd-R-1-simplified-inductor (sm :simplified-model R :nat) :nat
  :ic (< (+ (simplified-model-cur sm) (1+ R))
	 (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (if (= R 0) 0 (snd-R-1-simplified-inductor (snd-1-simplified sm) (1- R)))
  :body-contracts-hints (("Goal" :use (:instance snd-R-1-simplified-inductor-contracts)
			  :in-theory (enable snd-1-simplified-definition-rule))))

(property snd-R-1-simplified-commutes-wrapped-contracts (sm :simplified-model R :nat)
  :h (< (+ (simplified-model-cur sm) (1+ R))
	(+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (^ (< (+ (simplified-model-cur (snd-1-simplified sm)) R)
	(+ (simplified-model-hiA (snd-1-simplified sm)) (simplified-model-N (snd-1-simplified sm))))
     (< (simplified-model-cur (snd-R-simplified sm R))
	(+ (simplified-model-hiA (snd-R-simplified sm R)) (simplified-model-N (snd-R-simplified sm R)))))
  :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
						    snd-1-simplified-definition-rule))))

;; Note sure why but currently having issues with the body contracts for this one.  Revisit later.
(definecd snd-R-1-simplified-commutes-wrapped (sm :simplified-model R :nat) :bool
  :ic (< (+ (simplified-model-cur sm) (1+ R))
	 (+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (equal (snd-R-simplified (snd-1-simplified sm) R)
	 (snd-1-simplified (snd-R-simplified sm R)))
  :body-contracts-hints (("Goal" :use (:instance snd-R-1-simplified-commutes-wrapped-contracts))))
  
(property snd-r-1-simplified-commutes (sm :simplified-model R :nat)
  :h (< (+ (simplified-model-cur sm) (1+ R))
	(+ (simplified-model-hiA sm) (simplified-model-N sm)))
  (snd-R-1-simplified-commutes-wrapped sm R)
  :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
				     snd-1-simplified-definition-rule
				     snd-R-1-simplified-commutes-wrapped-definition-rule)
	   :induct (snd-R-1-simplified-inductor sm R))))


(definecd top-dn (top :pos rem :nat) :poss
  :ic (<= rem top)
  (cond
   ((= rem 0) nil)
   ((= rem 1) (list top))
   (t (cons top (top-dn (1- top) (1- rem))))))

(check= (top-dn 4 2) '(4 3))
(check= (top-dn 6 6) '(6 5 4 3 2 1))
(check= (top-dn 99 0) nil)

(definecd snd-r-simplified-effect-filling-inductor (sm :simplified-model R :nat) :nat
  :ic (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	 (<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (if (= R 0) 0
    (1+ (snd-r-simplified-effect-filling-inductor (snd-1-simplified sm) (1- R))))
  :body-contracts-hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

(property snd-r-doesnt-change-consts (sm :simplified-model R :nat)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (^ (= (simplified-model-lcap (snd-R-simplified sm R)) (simplified-model-lcap sm))
     (equal (simplified-model-rcvd (snd-R-simplified sm R)) (simplified-model-rcvd sm))
     (= (simplified-model-hiA (snd-R-simplified sm R)) (simplified-model-hiA sm))
     (= (simplified-model-N (snd-R-simplified sm R)) (simplified-model-N sm)))
  :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
				     snd-1-simplified-definition-rule))))

(property snd-r-simplified-cur (sm :simplified-model R :nat)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (= (simplified-model-cur (snd-r-simplified sm R))
     (+ (simplified-model-cur sm) R))
  :instructions
  ((:induct (snd-r-simplified-effect-filling-inductor sm r))
   :change-goal
   (:in-theory (enable snd-r-simplified-definition-rule))
   :prove
   (:use (:instance snd-r-simplified-definition-rule))
   (:use (:instance snd-r-1-simplified-commutes (r (1- r))))
   (:in-theory (enable snd-1-simplified-definition-rule))
   (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
                    (r (1- r))))
   :pro
   (:claim (equal (snd-r-simplified (snd-1-simplified sm)
                                    (+ -1 r))
                  (snd-1-simplified (snd-r-simplified sm (+ -1 r)))))
   (:use (:instance snd-1-simplified-definition-rule
                    (sm (snd-r-simplified sm (+ -1 r)))))
   :pro
   (:claim (= (simplified-model-cur (snd-r-simplified (snd-1-simplified sm)
                                                      (+ -1 r)))
              (+ (simplified-model-cur (snd-1-simplified sm))
                 -1 r)))
   (:drop 1 2 3 10)
   (:claim (= (+ (simplified-model-cur (snd-1-simplified sm))
                 -1 r)
              (+ (1+ (simplified-model-cur sm))
                 -1 r)))
   :prove))

(check= (append (top-dn (+ 3 8) 8) (top-dn 3 2)) '(11 10 9 8 7 6 5 4 3 2))
(check= (top-dn (+ 3 8) (+ 8 2)) '(11 10 9 8 7 6 5 4 3 2))

(definecd top-dn-append-ind (up :nat mid rem :pos) :nat
  :ic (<= rem mid)
  (if (= up 0) 0 (1+ (top-dn-append-ind (1- up) mid rem))))

(property top-dn-append (up :nat mid rem :pos)
  :h (<= rem mid)
  (equal (append (top-dn (+ mid up) up) (top-dn mid rem))
	 (top-dn (+ mid up) (+ up rem)))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule)
	   :induct (top-dn-append-ind up mid rem))))

(property snd-1-simplified-chan-effect (sm :simplified-model)
  :h (^ (< (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	(< (simplified-model-cur sm)
	    (+ (simplified-model-hia sm)
	       (simplified-model-n sm))))
  (equal (simplified-model-chan (snd-1-simplified sm))
	 (cons (simplified-model-cur sm) (simplified-model-chan sm)))
  :hints (("Goal" :in-theory (enable snd-1-simplified-definition-rule))))

;; Suffices to show that snd-1 preserves cumack property when channel isn't full yet.
(property snd-1-simplified-chan-effect-when-top-dn (sm :simplified-model)
  :h (^ (< (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	(< (simplified-model-cur sm)
	   (+ (simplified-model-hia sm)
	      (simplified-model-n sm)))
	(<= (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
	(< 1 (simplified-model-cur sm))
	(equal (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
						  (len (simplified-model-chan sm)))))
  (equal (simplified-model-chan (snd-1-simplified sm))
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
(property snd-r-does-nothing-when-full (sm :simplified-model R :pos)
  :h (^ (< (+ (simplified-model-cur sm) r)
            (+ (simplified-model-hia sm)
               (simplified-model-n sm)))
	(= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (equal (simplified-model-chan (snd-R-simplified sm R))
	 (simplified-model-chan sm))
  :instructions
  ((:in-theory (enable snd-r-simplified-definition-rule
                       snd-1-simplified-definition-rule
                       snd-r-1-simplified-commutes-wrapped-definition-rule))
   (:induct (snd-r-simplified-inductor sm r))
   :change-goal
   (:use (:instance snd-r-simplified-definition-rule))
   :pro
   (:use (:instance snd-1-simplified-definition-rule))
   :prove :pro
   (:claim (equal (simplified-model-chan (snd-r-simplified sm (+ -1 r)))
                  (simplified-model-chan sm)))
   (:drop 3)
   (:use (:instance snd-r-simplified-definition-rule))
   (:use (:instance snd-r-1-simplified-commutes (r (1- r))))
   (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
                    (r (1- r))))
   :prove))

(property snd-r-simplified-chan-effect-when-top-dn (sm :simplified-model R :pos)
  :h (^ (< (1- (+ R (len (simplified-model-chan sm)))) (simplified-model-lcap sm))
	(< (+ R (simplified-model-cur sm))
	   (+ (simplified-model-hia sm)
	      (simplified-model-n sm)))
	(<= (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
	(< 1 (simplified-model-cur sm))
	(equal (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
						  (len (simplified-model-chan sm)))))
  (equal (simplified-model-chan (snd-R-simplified sm R))
	 (top-dn (1- (+ R (simplified-model-cur sm)))
		 (+ R (len (simplified-model-chan sm)))))
 :instructions
 ((:induct (snd-r-simplified-inductor sm r))
  :change-goal
  (:in-theory (enable snd-r-simplified-definition-rule
                      snd-1-simplified-definition-rule
                      top-dn-definition-rule))
  :prove
  (:use (:instance snd-r-simplified-definition-rule))
  (:use (:instance snd-r-1-simplified-commutes (r (1- r))))
  (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
                   (r (1- r))))
  :pro
  (:claim (equal (snd-r-simplified sm r)
                 (snd-1-simplified (snd-r-simplified sm (+ -1 r)))))
  (:drop 1 2 3)
  (:use (:instance snd-1-simplified-chan-effect-when-top-dn
                   (sm (snd-r-simplified sm (+ -1 r)))))
  :pro
  (:use (:instance snd-r-doesnt-change-consts (r (1- r))))
  :pro
  (:claim (equal (simplified-model-chan (snd-r-simplified sm (+ -1 r)))
                 (top-dn (+ -1 (+ -1 r)
                            (simplified-model-cur sm))
                         (+ (+ -1 r)
                            (len (simplified-model-chan sm))))))
  (:drop 6)
  (:use (:instance top-dn-len
                   (b (+ -1 (+ -1 r)
                         (simplified-model-cur sm)))
                   (a (+ (+ -1 r)
                         (len (simplified-model-chan sm))))))
  :pro
  (:claim (= (len (top-dn (+ -1 (+ -1 r)
                             (simplified-model-cur sm))
                          (+ (+ -1 r)
                             (len (simplified-model-chan sm)))))
             (+ (+ -1 r)
                (len (simplified-model-chan sm)))))
  (:claim (< (len (simplified-model-chan (snd-r-simplified sm (+ -1 r))))
             (simplified-model-lcap (snd-r-simplified sm (+ -1 r)))))
  (:use (:instance snd-r-simplified-cur (r (1- r))))
  :pro
  (:claim (< (simplified-model-cur (snd-r-simplified sm (+ -1 r)))
             (+ (simplified-model-hia (snd-r-simplified sm (+ -1 r)))
                (simplified-model-n (snd-r-simplified sm (+ -1 r))))))
  (:claim
   (equal
    (simplified-model-chan (snd-1-simplified (snd-r-simplified sm (+ -1 r))))
    (top-dn
         (simplified-model-cur (snd-r-simplified sm (+ -1 r)))
         (+ 1
            (len (simplified-model-chan (snd-r-simplified sm (+ -1 r))))))))
  :prove))

(property snd-R-simplified-incrs-len (sm :simplified-model R :nat)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (= (len (simplified-model-chan (snd-R-simplified sm R)))
     (min (+ (len (simplified-model-chan sm)) R)
	  (simplified-model-lcap sm)))
  :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
				     snd-1-simplified-definition-rule))))

(property snd-R-simplified-incrs-cur (sm :simplified-model R :nat)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (= (simplified-model-cur (snd-R-simplified sm R))
     (+ R (simplified-model-cur sm)))
  :hints (("Goal" :in-theory (enable snd-R-simplified-definition-rule
				     snd-1-simplified-definition-rule))))

(property snd-R-simplified-consts (sm :simplified-model R :nat)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm)))
  (^ (= (simplified-model-lcap (snd-R-simplified sm R)) (simplified-model-lcap sm))
     (equal (simplified-model-rcvd (snd-R-simplified sm R)) (simplified-model-rcvd sm))
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

(property snd-r-snd-r=snd-r+r (sm :simplified-model R0 R1 :nat)
  :h (^ (< (+ (simplified-model-cur sm) R0 R1)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm))
	    (simplified-model-lcap sm)))
  (^ (< (+ (simplified-model-cur (snd-r-simplified sm r0))
	   r1)
	(+ (simplified-model-hia (snd-r-simplified sm r0))
	   (simplified-model-n (snd-r-simplified sm r0))))
     (equal (snd-R-simplified (snd-R-simplified sm R0) R1)
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
   (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
		    (r (1- r0))))
   (:in-theory (enable snd-r-simplified-definition-rule))
   :prove :prove))
				     

#|
---------- Define "dlv-b-simplified" and characterize what it does to chan -----------
|#
(property dlv-1-simplified-decrs-len (sm :simplified-model)
  :h (consp (simplified-model-chan sm))
  (= (len (simplified-model-chan (dlv-1-simplified sm)))
     (1- (len (simplified-model-chan sm))))
  :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
				     remove-ith-definition-rule))))
      

(property dlv-b-simplified-body-contracts (sm :simplified-model b :pos)
  :h (<= b (len (simplified-model-chan sm)))
  (let ((sm (dlv-1-simplified sm)))
    (<= (1- b) (len (simplified-model-chan sm))))
  :hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
				     remove-ith-definition-rule)
	   :use (:instance dlv-1-simplified-decrs-len))))

;; ASSUMPTION: Only ever call with b = b-cap = r_s.
(definecd dlv-b-simplified (sm :simplified-model b :nat) :simplified-model
  :ic (<= b (len (simplified-model-chan sm)))
  (if (= b 0) sm (dlv-b-simplified (dlv-1-simplified sm) (1- b)))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
						    remove-ith-definition-rule)
			  :use (:instance dlv-b-simplified-body-contracts))))

(definecd dlv-b-simplified-decrs-inductor (sm :simplified-model b :nat) :nat
  :ic (<= b (len (simplified-model-chan sm)))
  (if (= b 0) 0 (1+ (dlv-b-simplified-decrs-inductor (dlv-1-simplified sm) (1- b))))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule)
			  :use (:instance dlv-1-simplified-decrs-len))))

(property dlv-b-simplified-decrs-len (sm :simplified-model b :nat)
  :h (<= b (len (simplified-model-chan sm)))
  (= (len (simplified-model-chan (dlv-b-simplified sm b)))
     (- (len (simplified-model-chan sm)) b))
  :instructions
  ((:in-theory (enable dlv-b-simplified-definition-rule
		       dlv-1-simplified-definition-rule))
   (:induct (dlv-b-simplified-decrs-inductor sm b))
   :change-goal :prove
   (:use (:instance dlv-1-simplified-decrs-len))
   :pro
   (:claim
    (= (len (simplified-model-chan (dlv-b-simplified (dlv-1-simplified sm)
						     (+ -1 b))))
       (+ (len (simplified-model-chan (dlv-1-simplified sm)))
	  (- (+ -1 b)))))
   (:drop 6)
   (:casesplit (consp (simplified-model-chan sm)))
   (:claim (= (len (simplified-model-chan (dlv-1-simplified sm)))
	      (+ -1 (len (simplified-model-chan sm)))))
   (:claim
    (equal (len (simplified-model-chan (dlv-b-simplified (dlv-1-simplified sm)
							 (+ -1 b))))
	   (len (simplified-model-chan (dlv-b-simplified sm b)))))
   :prove :prove))

(property dlv-b-commutes-witness-contracts (sm :simplified-model b :nat)
  :h (<= (1+ b) (len (simplified-model-chan sm)))
  (^ (consp (simplified-model-chan sm))
     (<= b (len (simplified-model-chan (dlv-1-simplified sm))))
     (<= b (len (simplified-model-chan sm)))
     (consp (simplified-model-chan (dlv-b-simplified sm b))))
  :hints (("Goal" :use ((:instance dlv-b-simplified-decrs-len)
			(:instance dlv-1-simplified-decrs-len)))))

(definecd dlv-b-commutes-witness (sm :simplified-model b :nat) :bool
  :ic (<= (1+ b) (len (simplified-model-chan sm)))
  (equal (dlv-b-simplified (dlv-1-simplified sm) b)
	 (dlv-1-simplified (dlv-b-simplified sm b)))
  :body-contracts-hints (("Goal" :use (:instance dlv-b-commutes-witness-contracts))))

(definecd dlv-b-commutes-inductor (sm :simplified-model b :nat) :nat
  :ic (<= (1+ b) (len (simplified-model-chan sm)))
  (if (= b 0) 0 (1+ (dlv-b-commutes-inductor (dlv-1-simplified sm) (1- b))))
  :body-contracts-hints (("Goal" :in-theory (enable dlv-1-simplified-definition-rule
						    dlv-b-simplified-definition-rule
						    remove-ith-definition-rule)
			  :use ((:instance dlv-b-simplified-body-contracts)
				(:instance dlv-b-commutes-witness-contracts)))))

(property take-all-but-last-is-remove-last (ps :poss)
  :h (consp ps)
  (equal (remove-ith ps (1- (len ps)))
	 (take (1- (len ps)) ps))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(check= (take 3 (take 10 '(1 2 3 4 5 6 7 8 9 10 11))) (take 3 '(1 2 3 4 5 6 7 8 9 10 11)))

(property combine-takes (ps :poss i j :nat)
  :h (^ (< i (len ps)) (< j i))
  (equal (take j (take i ps))
	 (take j ps)))

(property dlv-b-commutes (sm :simplified-model b :nat)
  :h (<= (1+ b) (len (simplified-model-chan sm)))
  (dlv-b-commutes-witness sm b)
  :instructions
  ((:induct (dlv-b-commutes-inductor sm b))
   :pro
   (:in-theory (enable dlv-b-commutes-witness-definition-rule))
   (:use (:instance dlv-1-simplified-decrs-len))
   :pro
   (:claim (equal (dlv-b-simplified (dlv-1-simplified (dlv-1-simplified sm))
                                    (1- b))
                  (dlv-1-simplified (dlv-b-simplified (dlv-1-simplified sm)
                                                      (1- b)))))
   (:drop 6)
   (:use (:instance dlv-b-simplified-definition-rule
                    (sm (dlv-1-simplified sm))))
   :pro
   (:claim (equal (dlv-b-simplified (dlv-1-simplified sm)
                                    b)
                  (dlv-1-simplified (dlv-b-simplified (dlv-1-simplified sm)
                                                      (+ -1 b)))))
   (:use (:instance dlv-b-simplified-definition-rule))
   :prove
   (:in-theory (enable dlv-1-simplified-definition-rule
                       dlv-b-simplified-definition-rule
                       dlv-b-commutes-witness-definition-rule))
   :prove))
	


#|
Proof sketch:
(dlv-b sm b)
=
(dlv-b (dlv-1 sm) (1- b))
=
(dlv-1 (dlv-b sm (1- b)))
=
remove-ith the last element of chan of (dlv-b sm (1- b))
=
remove-ith the last element of take |chan| - 1 + b of sm
=
take |chan| + b of sm
|#
(property dlv-b-simplified-effect-0 (sm :simplified-model)
  (equal (dlv-b-simplified sm 0)
	 (mset :chan
	       (take (- (len (simplified-model-chan sm)) 0)
		     (simplified-model-chan sm))
	       sm))
  :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule))))

(property dlv-b-simplified-reduction-1 (sm :simplified-model b :pos)
  :h (<= b (len (simplified-model-chan sm)))
  (^ ;; FOR CONTRACTS
   (<= (1- (len (simplified-model-chan (dlv-b-simplified sm (+ -1 b)))))
       (len (simplified-model-chan (dlv-b-simplified sm (+ -1 b)))))
   (<= (1- b) (len (simplified-model-chan sm)))
   (natp (1- (len (simplified-model-chan (dlv-b-simplified sm (+ -1 b))))))
   ;; ACTUAL THM
   (equal (dlv-b-simplified sm b)
	  (mset :chan (remove-ith (simplified-model-chan (dlv-b-simplified sm (1- b)))
				  (1- (len (simplified-model-chan (dlv-b-simplified sm (1- b))))))
		(dlv-b-simplified sm (1- b)))))
  :hints (("Goal" :use ((:instance dlv-b-simplified-definition-rule)
			(:instance dlv-b-simplified-decrs-len (b (1- b)))
			(:instance dlv-1-simplified-definition-rule
				   (sm (dlv-b-simplified sm (1- b))))
			(:instance dlv-1-simplified-decrs-len)
			(:instance dlv-b-commutes-witness-contracts (b (1- b)))
			(:instance dlv-b-commutes-witness-definition-rule (b (1- b)))
			(:instance dlv-b-commutes (b (1- b)))))))

(property take-len-rule (x :nat ps :poss)
  :h (<= x (len ps))
  (= (len (take x ps)) x))

(property remove-ith-decrs-take (x :pos ps :poss)
  :h (< x (len ps))
  (equal (remove-ith (take x ps) (1- (len (take x ps))))
	 (take (1- x) ps))
  :hints (("Goal" :use (:instance take-all-but-last-is-remove-last (ps (take x ps))))))

(property dlv-b-simplified-reduction-2 (sm :simplified-model b :pos)
  :h (^ (< 1 b) (<= b (len (simplified-model-chan sm))))
  (^
   (natp (1- (len (take (1- b) (simplified-model-chan sm)))))
   (<= (1- (len (take (1- b) (simplified-model-chan sm))))
      (len (take (1- b) (simplified-model-chan sm))))
   (equal (remove-ith (take b (simplified-model-chan sm))
		      (1- (len (take b (simplified-model-chan sm)))))
	  (take (1- b) (simplified-model-chan sm))))
  :hints (("Goal" :use ((:instance take-len-rule (x (1- b)) (ps (simplified-model-chan sm)))
			(:instance remove-ith-decrs-take (x b) (ps (simplified-model-chan sm)))))))

(property dlv-b-simplified-effect (sm :simplified-model b :nat)
  :h (<= b (len (simplified-model-chan sm)))
  (equal (dlv-b-simplified sm b)
	 (mset :chan
	       (take (- (len (simplified-model-chan sm)) b)
		     (simplified-model-chan sm))
	       sm))
  :instructions
  ((:induct (dlv-b-simplified-decrs-inductor sm b))
   (:use (:instance dlv-1-simplified-decrs-len))
   (:use (:instance dlv-b-simplified-definition-rule))
   (:use (:instance dlv-b-simplified-reduction-2))
   (:use (:instance dlv-b-simplified-reduction-1))
   (:use (:instance dlv-b-simplified-decrs-len (b (1- b))))
   :pro (:casesplit (= b 1))
   (:in-theory (enable dlv-b-simplified-definition-rule
		       dlv-1-simplified-definition-rule))
   :prove :prove :prove))

;; If everything not in the "take" gets delivered, then what do we know was delivered?
(definecd remaining (taken :nat ps :poss) :poss
  :ic (<= taken (len ps))
  (if (= taken 0) ps (remaining (1- taken) (cdr ps))))

(check= (remaining 0 '(1 2 3)) '(1 2 3))
(check= (remaining 1 '(1 2 3)) '(2 3))
(check= (remaining 2 '(1 2 3)) '(3))
(check= (remaining 3 '(1 2 3)) nil)

(check= (app (take 3 '(1 2 3 4 5 6))
	     (remaining 3 '(1 2 3 4 5 6)))
	'(1 2 3 4 5 6))

(property take-takes-remaining (b :pos ps :poss)
  :h (<= b (len ps))
  (equal (app (take b ps) (remaining b ps)) ps)
  :hints (("Goal" :in-theory (enable remaining-definition-rule))))

(check= (remaining 3 (top-dn 10 7)) '(7 6 5 4))
;; Formula: (remaining k (top-dn top rem)) = (top-dn (- top k) (- rem k))

(property cdr-top-dn (top rem :pos)
  :h (^ (<= rem top) (< 1 top))
  (equal (cdr (top-dn top rem))
	 (top-dn (1- top) (1- rem)))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(property cdr-top-dn-1 (rem :nat)
  :h (<= rem 1)
  (equal (cdr (top-dn 1 rem)) nil)
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(definecd top-dn-rem-inductor (k top rem :pos) :nat
  :ic (^ (<= rem top) (<= k rem) (< k top))
  (if (= k 1) 0
    (1+ (top-dn-rem-inductor (1- k) (1- top) (1- rem)))))

(property top-dn-rem (k top rem :pos)
  :h (^ (<= rem top) (<= k rem) (< k top))
  (^ (<= k (len (top-dn top rem)))
     (equal (remaining k (top-dn top rem)) (top-dn (- top k) (- rem k))))
  :hints (("Goal" :induct (top-dn-rem-inductor k top rem)
	   :in-theory (enable remaining-definition-rule
			      top-dn-definition-rule))))

(property top-dn-doesnt-go-up (top x :pos rem :nat)
  :h (^ (< top x) (<= rem top))
  (! (in x (top-dn top rem)))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(property top-dn-inclusion (top :pos x rem :nat)
  :h (<= rem top)
  (iff (^ (<= x top) (< (- top rem) x))
       (in x (top-dn top rem)))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(definecd cumackp-top-dn-inductor (top :pos) :nat
  (if (= top 1) 1 (1+ (cumackp-top-dn-inductor (1- top)))))

(property update-cumack (ack :pos pkts :poss)
  :h (^ (cumackp ack pkts) (! (in (1+ ack) pkts)))
  (cumackp (1+ ack) (cons ack pkts))
  :hints (("Goal" :in-theory (enable cumackp-definition-rule
				     has-all-definition-rule))))

(property cons-top-dn (top :pos rem :nat)
  :h (<= rem top)
  (equal (cons (1+ top) (top-dn top rem))
	 (top-dn (1+ top) (1+ rem)))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

;; Ok, if remaining of top-dn is another remaining ...
;; and ack is the bottom of that list ....
;; how does this impact ACK?
(property cumackp-top-dn (top :pos)
  (cumackp (1+ top) (top-dn top top))
  :instructions ((:induct (cumackp-top-dn-inductor top))
                 (:use (:instance cons-top-dn (top (1- top))
                                  (rem (1- top))))
                 :prove :prove))

#|
---------- Define a (trns-R o tick o dlv-b) transition  -----------
Need to prove:
1. That the tick abstraction is fine, because it refills the bucket b to b-cap.
2. That the effect in the first step is to put (top-dn (+ cur R) (- R r_s)) in the channel
   and deliver (top-dn (+ cur r_s) r_s) to the receiver, updating the cumack.
3. That this continues for the entire warmup period.
4. That there is one extra step of delivery after the warmup period which also increases 
   the cumack by r_s amount.
|#
(property full-simplified-step-sending-contracts (R r_s :pos sm :simplified-model)
  :h (^ (< (+ (simplified-model-cur sm) R)
	   (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm))
	    (simplified-model-lcap sm))
	(<= r_s R)
	(< R (simplified-model-lcap sm)))
  (<= r_s (len (simplified-model-chan (snd-R-simplified sm R))))
  :hints (("Goal" :use (:instance snd-R-simplified-incrs-len))))

(definecd full-simplified-step-sending (R r_s :pos sm :simplified-model) :simplified-model
  :ic (^ (< (+ (simplified-model-cur sm) R)
	    (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	 (<= (len (simplified-model-chan sm))
	     (simplified-model-lcap sm))
	 (<= r_s R)
	 (< R (simplified-model-lcap sm)))
  (mset :rcvd
	(append (remaining (- (len (simplified-model-chan (snd-R-simplified sm R))) r_s)
			   (simplified-model-chan (snd-R-simplified sm R)))
		(simplified-model-rcvd sm))
	(dlv-b-simplified (snd-R-simplified sm R) r_s))
  :body-contracts-hints (("Goal" :use (:instance snd-R-simplified-incrs-len)))
  :function-contract-hints (("Goal" :use (:instance snd-R-simplified-incrs-len))))
  

(encapsulate
 ()
 (local (include-book "worst-case"))
 ;; I promised I would prove that it was OK for me to ignore the bucket.  I will do so now.
 ;; The idea here is simple.  The concrete model does snd-R, then tick, then dlv-b.
 ;; The tick increases the bucket again by amount r_s without losing anything.
 (local (property tick-increases-b-by-r
	  (tbf :tbf)
	  :h (all-young (tbf-D tbf))
	  (^ (>= (tbf-b (tbf-tick tbf)) (min (tbf-r tbf) (tbf-b-cap tbf)))
	     (equal (dgs->poss (tbf-D (tbf-tick tbf))) (dgs->poss (tbf-D tbf))))
	  :hints (("Goal" :in-theory (enable tbf-tick-definition-rule
					     tbf-age-definition-rule
					     all-young-definition-rule
					     age-all-definition-rule
					     remove-ith-definition-rule))))))

;; Now let's reason a bit about that full transition and how it updates:
;; (1) the cur value, and (2) the cumack. I will begin with the second part.
;; We could be lazy and just show, well, if we presume everything out-of-order is lost,
;; then rcvd is a top-dn and thus we simply append a top-dn to a matching top-dn and we
;; get a natural increase.  But let's do the more challenging thing.  Suppose that ack
;; is the current cumack for rcvd.  Suppose that we now prepend (top-dn (ack + R)) to rcvd.
;; I claim that this has the effect of increasing the cumack by at least R.
;;
(property cumackp-rcv-ack (ack0 ack1 :pos ps :poss)
  :h (^ (cumackp ack0 ps) (cumackp ack1 (cons ack0 ps)))
  (< ack0 ack1)
  :instructions (:pro (:in-theory (enable has-all-definition-rule
                                          cumackp-definition-rule))
                      (:claim (! (in ack0 ps)))
                      (:use (:instance cumackp-definition-rule (a ack0)))
                      (:casesplit (= ack0 1))
                      :prove :prove))

(property dlv-ack-increases-cumack (ack0 ack1 :pos sm :simplified-model)
  :h (^ (cumackp ack0 (simplified-model-rcvd sm))
	(cumackp ack1 (cons ack0 (simplified-model-rcvd sm))))
  (^ (possp (cons ack0 (simplified-model-rcvd sm)))
     (< ack0 ack1))
  :hints (("Goal" :use (:instance cumackp-rcv-ack (ps (simplified-model-chan sm))))))

#|
For the rest of the proof, what I'd like to do is lower-bound goodput by assuring that the
current high ack is always lower bounded.  The idea here is that we define goodput to be
(high ack - 1) / (# pkts dlvd to the receiver).  If we know the EXACT denominator, and a 
lower bound on the numerator, then we have a lower bound on the whole.  This is kind of an
obvious arithmetic statement about fractions, but I can prove it, just to be safe.
|#
(definecd goodput (ack deliveries :pos) :rational
  (/ (1- ack) deliveries))

(property (lower-ack-bnd actual-ack deliveries :pos)
  :h (<= lower-ack-bnd actual-ack)
  (<= (goodput lower-ack-bnd deliveries)
      (goodput actual-ack deliveries))
  :hints (("Goal" :in-theory (enable goodput-definition-rule))))

#|
Now let's characterize the lower bnd on the ack after a dlv-b.
|#
(definecd prepend-top-dn-incrs-cumack-inductor (ack ln :pos rcvd :poss) :nat
  :ic (cumackp ack rcvd)
  (if (= ln 1) 0 (1+ (prepend-top-dn-incrs-cumack-inductor ack (1- ln) rcvd))))

(property has-all-cdr (p :pos ps :poss)
  :h (has-all p (cdr ps))
  (has-all p ps)
  :hints (("Goal" :in-theory (enable has-all-definition-rule))))

(property prepend-top-dn-incrs-cumack (ack ln :pos rcvd :poss)
  :h (cumackp ack rcvd)
  (has-all (1- (+ ack ln)) (append (top-dn (1- (+ ack ln)) ln) rcvd))
  :instructions ((:induct (prepend-top-dn-incrs-cumack-inductor ack ln rcvd))
		 :change-goal
		 (:in-theory (enable cumackp-definition-rule
				     has-all-definition-rule
				     top-dn-definition-rule))
		 :prove
		 (:claim (equal (cons (+ -1 ack ln)
				      (top-dn (+ -1 ack -1 ln) (+ -1 ln)))
				(top-dn (+ -1 ack ln) ln)))
		 :pro
		 (:use (:instance has-all-definition-rule
				  (p (+ -1 ack ln))
				  (ps (app (top-dn (+ -1 ack ln) ln) rcvd))))
		 :pro
		 (:claim (in (+ -1 ack ln)
			     (app (top-dn (+ -1 ack ln) ln) rcvd)))
		 (:claim (has-all (+ -1 -1 ack ln)
				  (cdr (app (top-dn (+ -1 ack ln) ln) rcvd))))
		 :prove))

(property has-all<cumack (p ack :pos ps :poss)
  :h (^ (has-all p ps) (cumackp ack ps))
  (< p ack)
  :hints (("Goal" :in-theory (enable has-all-definition-rule cumackp-definition-rule))))

(property prepend-top-dn-concretely-lower-bounds-cumack (ack0 ack1 ln :pos rcvd :poss)
  :h (^ (cumackp ack0 rcvd)
	(cumackp ack1 (append (top-dn (1- (+ ack0 ln)) ln) rcvd)))
  (<= (+ ack0 ln) ack1)
  :hints (("Goal" :use ((:instance prepend-top-dn-incrs-cumack (ack ack0))
			(:instance has-all<cumack
				   (p (1- (+ ack0 ln)))
				   (ack ack1)
				   (ps (append (top-dn (1- (+ ack0 ln)) ln) rcvd)))))))

;; Clearing my palette.
(in-theory (disable simplification-contracts-snd-1
		    snd-1-effect
		    simplification-preserves-snd-1
		    simplification-preserves-dlv-1
		    snd-R-1-simplified-contracts
		    snd-R-1-simplified-inductor-contracts
		    snd-R-1-simplified-commutes-wrapped-contracts
		    snd-r-1-simplified-commutes
		    snd-r-doesnt-change-consts
		    snd-r-simplified-cur
		    top-dn-append
		    snd-1-simplified-chan-effect
		    snd-1-simplified-chan-effect-when-top-dn
		    top-dn-len
		    snd-r-simplified-chan-effect-when-top-dn
		    snd-R-simplified-incrs-len
		    dlv-1-simplified-decrs-len
		    dlv-b-simplified-body-contracts
		    dlv-b-simplified-decrs-len
		    dlv-b-commutes-witness-contracts
		    take-all-but-last-is-remove-last
		    combine-takes
		    dlv-b-commutes
		    dlv-b-simplified-effect-0
		    dlv-b-simplified-reduction-1
		    take-len-rule
		    remove-ith-decrs-take
		    dlv-b-simplified-reduction-2
		    dlv-b-simplified-effect
		    take-takes-remaining
		    cdr-top-dn
		    cdr-top-dn-1
		    top-dn-rem
		    top-dn-doesnt-go-up
		    top-dn-inclusion
		    update-cumack
		    cons-top-dn
		    cumackp-top-dn
		    full-simplified-step-sending-contracts
		    cumackp-rcv-ack
		    dlv-ack-increases-cumack
		    has-all-cdr
		    prepend-top-dn-incrs-cumack
		    has-all<cumack
		    prepend-top-dn-concretely-lower-bounds-cumack))

(definecd has-all-top-dn-inductor (top rem :pos ps :poss) :nat
  :ic (^ (< rem top) (has-all (- top rem) ps))
  (if (= rem 1) 0 (1+ (has-all-top-dn-inductor (1- top) (1- rem) ps))))

(property has-all-top-dn (top rem :pos ps :poss)
  :h (^ (< rem top) (has-all (- top rem) ps))
  (has-all top (append (top-dn top rem) ps))
  :hints (("Goal" :in-theory (enable has-all-definition-rule
				     top-dn-definition-rule
				     has-all-cdr)
	   :induct (has-all-top-dn-inductor top rem ps))))

(property lower-bnd-cumack-full-simplified-step-sending (R r_s :pos sm :simplified-model)
  :h (^ (consp (simplified-model-chan sm))
	(<= (+ R (len (simplified-model-chan sm))) (simplified-model-lcap sm))
	(< (+ (simplified-model-cur sm) R) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	(<= r_s R)
	(< 1 (simplified-model-cur sm))
	(< R (simplified-model-lcap sm))
	(< (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
	(equal (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
						  (len (simplified-model-chan sm))))
	(has-all (- (1- (simplified-model-cur sm)) (len (simplified-model-chan sm)))
		 (simplified-model-rcvd sm)))
  (has-all (+ r_s (- (1- (simplified-model-cur sm)) (len (simplified-model-chan sm))))
	   (simplified-model-rcvd (full-simplified-step-sending R r_s sm)))
  :hints (("Goal" :use ((:instance full-simplified-step-sending-definition-rule)
			(:instance snd-r-simplified-chan-effect-when-top-dn)
			(:instance top-dn-rem
				   (k (+ (len (simplified-model-chan (snd-r-simplified sm r)))
					 (- r_s)))
				   (top (+ -1 r (simplified-model-cur sm)))
				   (rem (+ r (len (simplified-model-chan sm)))))
			(:instance snd-r-simplified-incrs-len)
			(:instance has-all-top-dn
				   (top (+ r_s (+ -1 (simplified-model-cur sm))
					   (- (len (simplified-model-chan sm)))))
				   (rem r_s)
				   (ps (simplified-model-rcvd sm)))))))


(property take-top-dn (top rem k :pos)
  :h (^ (<= k rem) (<= rem top))
  (equal (take k (top-dn top rem))
	 (top-dn top k))
  :hints (("Goal" :in-theory (enable top-dn-definition-rule))))

(property full-simplified-step-sending-invariant (R r_s :pos sm :simplified-model)
  :h (^ (consp (simplified-model-chan sm))
	(<= (+ R (len (simplified-model-chan sm))) (simplified-model-lcap sm))
	(< (+ (simplified-model-cur sm) R) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	(<= r_s R)
	(< 1 (simplified-model-cur sm))
	(< R (simplified-model-lcap sm))
	(< (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
	(equal (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
						  (len (simplified-model-chan sm))))
	(has-all (- (1- (simplified-model-cur sm)) (len (simplified-model-chan sm)))
		 (simplified-model-rcvd sm)))
  (^ ;; contracts
   (posp (+ -1
	    (simplified-model-cur (full-simplified-step-sending r r_s sm))))
   (posp (+ (+ -1 (simplified-model-cur sm))
	    (- (len (simplified-model-chan sm)))))
   (<= (len (simplified-model-chan sm))
       (+ -1 (simplified-model-cur sm)))
   (<= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
       (+ -1
	  (simplified-model-cur (full-simplified-step-sending r r_s sm))))
   ;; theorem
   (equal (simplified-model-chan (full-simplified-step-sending R r_s sm))
	  (top-dn (1- (simplified-model-cur (full-simplified-step-sending R r_s sm)))
		  (len (simplified-model-chan (full-simplified-step-sending R r_s sm)))))
   (= (simplified-model-cur (full-simplified-step-sending R r_s sm))
      (+ R (simplified-model-cur sm)))
   (= (len (simplified-model-chan (full-simplified-step-sending R r_s sm)))
      (+ R (- (len (simplified-model-chan sm)) r_s))))
  :instructions
  ((:use (:instance full-simplified-step-sending-definition-rule))
   (:use (:instance snd-r-simplified-chan-effect-when-top-dn))
   (:use (:instance snd-r-simplified-incrs-len))
   (:use (:instance dlv-b-simplified-effect (b r_s)
		    (sm (snd-r-simplified sm r))))
   (:use (:instance snd-r-simplified-consts))
   (:use (:instance snd-r-simplified-incrs-cur))
   :pro
  (:claim
   (^
    (posp (+ -1
             (simplified-model-cur (full-simplified-step-sending r r_s sm))))
    (posp (+ (+ -1 (simplified-model-cur sm))
             (- (len (simplified-model-chan sm)))))
    (<= (len (simplified-model-chan sm))
        (+ -1 (simplified-model-cur sm)))
    (<= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
        (+ -1
           (simplified-model-cur (full-simplified-step-sending r r_s sm))))))
  (:claim
     (= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
        (+ r
           (- (len (simplified-model-chan sm))
              r_s))))
  (:claim (= (simplified-model-cur (full-simplified-step-sending r r_s sm))
             (+ r (simplified-model-cur sm))))
  :s
  (:claim
       (equal (mget :chan (full-simplified-step-sending r r_s sm))
              (take (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                       (- r_s))
                    (top-dn (+ -1 r (simplified-model-cur sm))
                            (+ r (len (simplified-model-chan sm)))))))
  (:use
       (:instance take-top-dn
                  (top (+ -1 r (simplified-model-cur sm)))
                  (rem (+ r (len (simplified-model-chan sm))))
                  (k (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                        (- r_s)))))
  :pro
  (:claim (= (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                (- r_s))
             (len (mget :chan (full-simplified-step-sending r r_s sm)))))
  (:claim
   (equal
    (top-dn
       (if (acl2-numberp (mget :cur (full-simplified-step-sending r r_s sm)))
           (+ -1
              (mget :cur (full-simplified-step-sending r r_s sm)))
         -1)
       (len (mget :chan (full-simplified-step-sending r r_s sm))))
    (top-dn (+ -1 r (simplified-model-cur sm))
            (+ (len (simplified-model-chan (snd-r-simplified sm r)))
               (- r_s)))))
  (:claim (and (posp (+ -1 r (simplified-model-cur sm)))
               (posp (+ r (len (simplified-model-chan sm))))
               (posp (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                        (- r_s)))
               (<= (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                      (- r_s))
                   (+ r (len (simplified-model-chan sm))))
               (<= (+ r (len (simplified-model-chan sm)))
                   (+ -1 r (simplified-model-cur sm)))))
  (:drop 2 3 4 5 6)
  :prove))

(in-theory (disable lower-bnd-cumack-full-simplified-step-sending
		    full-simplified-step-sending-invariant))

#|
Characterize the fact that the next snd-R after filling preserves top-dn.
|#
(definecd first-burst-after-full-inductor (R r_s :pos sm :simplified-model) :nat
  :ic (<= r_s R)
  (if (= R r_s) 0 (1+ (first-burst-after-full-inductor (1- R) r_s sm))))

(property get-set-chan (ps :poss sm :simplified-model)
  (equal (simplified-model-chan (mset :chan ps sm)) ps))

(property chan-same-regardless-of-R>r_s (R r_s :pos sm :simplified-model)
  :h (^ (= (+ (len (simplified-model-chan sm)) r_s) (simplified-model-lcap sm))
	(< (+ (simplified-model-cur sm) R) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= r_s R))
  (equal (simplified-model-chan (snd-R-simplified sm R))
	 (simplified-model-chan (snd-R-simplified sm r_s)))
  :instructions
 ((:induct (first-burst-after-full-inductor r r_s sm))
  :pro
  (:claim (equal (simplified-model-chan (snd-r-simplified sm (+ -1 r)))
                 (simplified-model-chan (snd-r-simplified sm r_s))))
  (:drop 3)
  (:use (:instance snd-r-simplified-definition-rule))
  (:use (:instance snd-r-1-simplified-commutes-wrapped-definition-rule
                   (r (1- r))))
  (:use (:instance snd-r-1-simplified-commutes (r (1- r))))
  (:use (:instance snd-1-simplified-definition-rule
                   (sm (snd-r-simplified sm (+ -1 r)))))
  :pro
  (:claim (equal (snd-r-simplified sm r)
                 (snd-1-simplified (snd-r-simplified sm (+ -1 r)))))
  (:use (:instance snd-r-simplified-incrs-len (r (1- r))))
  :pro
  (:claim (= (len (simplified-model-chan (snd-r-simplified sm (+ -1 r))))
             (simplified-model-lcap sm)))
  (:use (:instance snd-r-simplified-consts (r (1- r))))
  (:use (:instance snd-r-simplified-incrs-cur (r (1- r))))
  :pro
  (:claim (and (simplified-modelp (snd-r-simplified sm (+ -1 r)))
               (< (simplified-model-cur (snd-r-simplified sm (+ -1 r)))
                  (+ (simplified-model-hia (snd-r-simplified sm (+ -1 r)))
                     (simplified-model-n (snd-r-simplified sm (+ -1 r)))))))
  (:claim (! (< (len (simplified-model-chan (snd-r-simplified sm (+ -1 r))))
                (simplified-model-lcap (snd-r-simplified sm (+ -1 r))))))
  (:claim
   (equal
    (snd-1-simplified (snd-r-simplified sm (+ -1 r)))
    (mset :chan
	  (simplified-model-chan (snd-r-simplified sm (+ -1 r)))
	  (mset :cur
		(+ 1
		   (simplified-model-cur (snd-r-simplified sm (+ -1 r))))
		(snd-r-simplified sm (+ -1 r))))))
  (:drop 1 2 3)
  (:use
   (:instance
    get-set-chan
    (ps (simplified-model-chan (snd-r-simplified sm (+ -1 r))))
    (sm (mset :cur
	      (+ 1
		 (simplified-model-cur (snd-r-simplified sm (+ -1 r))))
	      (snd-r-simplified sm (+ -1 r))))))
  :pro
  (:claim
   (equal
    (simplified-model-chan
     (mset :chan
	   (simplified-model-chan (snd-r-simplified sm (+ -1 r)))
	   (mset :cur
		 (+ 1
		    (simplified-model-cur (snd-r-simplified sm (+ -1 r))))
		 (snd-r-simplified sm (+ -1 r)))))
    (simplified-model-chan (snd-r-simplified sm (+ -1 r)))))
  (:claim
   (equal
    (simplified-model-chan (snd-1-simplified (snd-r-simplified sm (+ -1 r))))
    (simplified-model-chan (snd-r-simplified sm (+ -1 r)))))
  :prove :prove))

(property sms-chans=->chans-dlv-b-= (sm0 sm1 :simplified-model b :pos)
  :h (^ (equal (simplified-model-chan sm0) (simplified-model-chan sm1))
	(<= b (len (simplified-model-chan sm0))))
  (equal (simplified-model-chan (dlv-b-simplified sm0 b))
	 (simplified-model-chan (dlv-b-simplified sm1 b)))
  :hints (("Goal" :in-theory (enable dlv-b-simplified-effect))))

(defthm first-burst-after-full
 (=>
  (^ (posp r)
     (posp r_s)
     (simplified-modelp sm)
     (consp (simplified-model-chan sm))
     (= (len (simplified-model-chan sm))
        (- (simplified-model-lcap sm) r_s))
     (< (+ (simplified-model-cur sm) r)
        (+ (simplified-model-hia sm)
           (simplified-model-n sm)))
     (<= r_s r)
     (< 1 (simplified-model-cur sm))
     (< r (simplified-model-lcap sm))
     (< (len (simplified-model-chan sm))
        (1- (simplified-model-cur sm)))
     (equal (simplified-model-chan sm)
            (top-dn (1- (simplified-model-cur sm))
                    (len (simplified-model-chan sm)))))
  (^
    (equal (simplified-model-chan (full-simplified-step-sending r r_s sm))
           (top-dn (+ -1 r_s (simplified-model-cur sm))
                   (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s))))
    (= (simplified-model-cur (full-simplified-step-sending r r_s sm))
       (+ r (simplified-model-cur sm)))
    (= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
       (- (simplified-model-lcap sm) r_s))))
 :instructions
 ((:use (:instance chan-same-regardless-of-r>r_s))
  :pro
  (:claim (equal (simplified-model-chan (snd-r-simplified sm r))
                 (simplified-model-chan (snd-r-simplified sm r_s))))
  (:drop 1)
  (:use (:instance snd-r-simplified-chan-effect-when-top-dn
                   (r r_s)))
  :pro
  (:claim (equal (simplified-model-chan (snd-r-simplified sm r_s))
                 (top-dn (+ -1 r_s (simplified-model-cur sm))
                         (+ r_s (len (simplified-model-chan sm))))))
  (:drop 1)
  (:use (:instance full-simplified-step-sending-definition-rule))
  (:use (:instance dlv-b-simplified-effect (b r_s)
                   (sm (snd-r-simplified sm r_s))))
  :pro
  (:claim
   (equal
    (full-simplified-step-sending r r_s sm)
    (mset
     :rcvd
     (app (remaining (+ (len (simplified-model-chan (snd-r-simplified sm r)))
                        (- r_s))
                     (simplified-model-chan (snd-r-simplified sm r)))
          (simplified-model-rcvd sm))
     (dlv-b-simplified (snd-r-simplified sm r)
                       r_s))))
  (:drop 2)
  (:use (:instance snd-r-simplified-incrs-len (r r_s)))
  :pro
  (:claim
   (equal
       (dlv-b-simplified (snd-r-simplified sm r_s)
                         r_s)
       (mset :chan
             (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s))
                   (simplified-model-chan (snd-r-simplified sm r_s)))
             (snd-r-simplified sm r_s))))
  (:drop 2)
  (:use (:instance snd-r-simplified-chan-effect-when-top-dn
                   (r r_s)))
  :pro
  (:claim (equal (simplified-model-chan (snd-r-simplified sm r_s))
                 (top-dn (+ -1 r_s (simplified-model-cur sm))
                         (+ r_s (len (simplified-model-chan sm))))))
  (:drop 1)
  (:use
     (:instance take-top-dn
                (k (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s)))
                (top (+ -1 r_s (simplified-model-cur sm)))
                (rem (+ r_s (len (simplified-model-chan sm))))))
  :pro
  (:claim
    (equal (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                    (- r_s))
                 (top-dn (+ -1 r_s (simplified-model-cur sm))
                         (+ r_s (len (simplified-model-chan sm)))))
           (top-dn (+ -1 r_s (simplified-model-cur sm))
                   (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s)))))
  (:drop 1)
  (:use
    (:instance
         get-set-chan
         (ps (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s))
                   (simplified-model-chan (snd-r-simplified sm r_s))))
         (sm (snd-r-simplified sm r_s))))
  :pro
  (:claim
   (and (pos-listp
             (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s))
                   (simplified-model-chan (snd-r-simplified sm r_s))))
        (simplified-modelp (snd-r-simplified sm r_s))))
  (:claim
   (equal
    (simplified-model-chan
       (mset :chan
             (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s))
                   (simplified-model-chan (snd-r-simplified sm r_s)))
             (snd-r-simplified sm r_s)))
    (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
             (- r_s))
          (simplified-model-chan (snd-r-simplified sm r_s)))))
  (:drop 1)
  (:claim
    (equal (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r_s)
                                                    r_s))
           (take (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                    (- r_s))
                 (simplified-model-chan (snd-r-simplified sm r_s)))))
  (:claim
      (equal (simplified-model-chan (full-simplified-step-sending r r_s sm))
             (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r)
                                                      r_s))))
  (:use (:instance sms-chans=->chans-dlv-b-=
                   (sm0 (snd-r-simplified sm r))
                   (sm1 (snd-r-simplified sm r_s))
                   (b r_s)))
  :pro
  (:claim
    (equal (simplified-model-chan (full-simplified-step-sending r r_s sm))
           (top-dn (+ -1 r_s (simplified-model-cur sm))
                   (+ (len (simplified-model-chan (snd-r-simplified sm r_s)))
                      (- r_s)))))
  (:claim
     (= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
        (+ (simplified-model-lcap sm) (- r_s))))
  (:use (:instance snd-r-simplified-incrs-cur))
  :pro
  (:claim (= (simplified-model-cur (snd-r-simplified sm r))
             (+ r (simplified-model-cur sm))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-effect
                   (sm (snd-r-simplified sm r))
                   (b r_s)))
  :prove))

#|
Characterize how many delivery steps it takes before we can no longer guarantee
 that we are delivering stuff top-dn from our prior bound.

(= (simplified-model-cur (full-simplified-step-sending R r_s sm))
      (+ R (simplified-model-cur sm)))

(= (len (simplified-model-chan (full-simplified-step-sending R r_s sm)))
   (+ R (- (len (simplified-model-chan sm)) r_s))))

In other words, compute t_warm.

Keep in mind: EVERYTHING in transit gets delivered.  And until twarm is up, it's all goodput.
After that, it's ... badput.  
|#
(definecd num-in-transit (prev R r_s l-cap :nat) :nat
  :ic (^ (< r_s R) (<= prev l-cap) (< R l-cap))
  (- (min (+ prev R) l-cap) r_s))

(definecd num-in-transit* (prev R r_s l-cap N :nat) :nat
  :ic (^ (< r_s R) (<= prev l-cap) (< R l-cap))
  :oc (<= (num-in-transit* prev R r_s l-cap N) l-cap)
  (if (= N 0)
      prev
    (num-in-transit (num-in-transit* prev R r_s l-cap (1- N))
		     R r_s l-cap))
  :body-contracts-hints (("Goal" :in-theory (enable num-in-transit-definition-rule)))
  :function-contract-hints (("Goal" :in-theory (enable num-in-transit-definition-rule))))

(property simplify-num-in-transit* (prev R r_s l-cap N :nat)
  :h (^ (< r_s R) (<= prev l-cap) (< R l-cap))
  (= (num-in-transit* prev R r_s l-cap N)
     (if (= N 0) prev
       (- (min (+ prev (* N R) (* (1- N) -1 r_s)) l-cap) r_s)))
  :hints (("Goal" :in-theory (enable num-in-transit*-definition-rule
				     num-in-transit-definition-rule))))

(property div-mul-rule (a b :int bot :pos)
  (iff (<= (* a bot) b) (<= a (/ b bot))))

;; t_warm proof
;; prev + N*R - (N-1)r_s <= l-cap
;; <->
;; N*R - (N-1)r_s <= l-cap - prev
;; <->
;; R + (N-1)R - (N-1)r_s <= l-cap - prev
;; <->
;; (N-1)(R - r_s) <= l-cap - prev - R
;; <->
;; N-1 <= (l-cap - prev - R)/(R - r_s)
;; <->
;; N <= 1 + (l-cap - prev - R)/(R - r_s)
(property (prev R r_s l-cap N :pos)
  :h (^ (< r_s R) (<= prev l-cap) (< R l-cap))
  (iff (<= (+ prev (* N R) (* (1- N) -1 r_s)) l-cap)
       (<= N (1+ (/ (- l-cap (+ prev R)) (- R r_s)))))
  :hints (("Goal" :use (:instance div-mul-rule
				  (a (1- N))
				  (b (- l-cap (+ prev R)))
				  (bot (- R r_s))))))
				  
;; So, we've shown the following:
;; R ack-incrementing packets make it through at each burst before the channel fills
;; The channel fills after t_warm bursts
;; In the single next burst, r_s ack-incrementing packets make it through
;; This gives us a lower bound of R t_warm + r_s on goodput between ACKs.
;; To totally concretize this, it would be nice if we could tie our results back to
;; the invariants we proved on simplified-model.

(property tie-prior-invariant-to-num-in-transit (R r_s :pos sm :simplified-model)
  :h (^ (consp (simplified-model-chan sm))
	(<= (+ R (len (simplified-model-chan sm))) (simplified-model-lcap sm))
	(< (+ (simplified-model-cur sm) R) (+ (simplified-model-hiA sm) (simplified-model-N sm)))
	(<= (len (simplified-model-chan sm)) (simplified-model-lcap sm))
	(< r_s R)
	(< 1 (simplified-model-cur sm))
	(< R (simplified-model-lcap sm))
	(< (len (simplified-model-chan sm)) (1- (simplified-model-cur sm)))
	(equal (simplified-model-chan sm) (top-dn (1- (simplified-model-cur sm))
						  (len (simplified-model-chan sm))))
	(has-all (- (1- (simplified-model-cur sm)) (len (simplified-model-chan sm)))
		 (simplified-model-rcvd sm)))
  (= (len (simplified-model-chan (full-simplified-step-sending r r_s sm)))
     (num-in-transit (len (simplified-model-chan sm)) R r_s (simplified-model-lcap sm)))
  :hints (("Goal" :in-theory (enable num-in-transit-definition-rule)
	   :use (:instance full-simplified-step-sending-invariant)))) 
