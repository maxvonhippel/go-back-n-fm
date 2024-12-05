(in-package "ACL2S")
(include-book "performance")

#|
In this book we are going to do four things.
<1> Count how many times each the filling overtransmission step can occur,
    before we move to the over-filling step.
<2> Prove that once we enter the over-filling step, we stay in that step until
    full; and count how many repetitions this takes.
<3> Characterize the number of received packets from steps <1> and <2> and use it
    to explicitly compute the efficiency formula.
<4> "Glue" the result back to the original model.

Let's start with step <1>.
|#
(propertyd dlv-b-simplified-doesnt-change-d-cap (sm :simplified-model b :nat)
     :h (<= b (len (simplified-model-chan sm)))
     (= (simplified-model-d-cap (dlv-b-simplified sm b))
        (simplified-model-d-cap sm))
     :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule
                dlv-1-simplified-definition-rule))))

(propertyd dlv-b-simplified-doesnt-change-hiA (sm :simplified-model b :nat)
     :h (<= b (len (simplified-model-chan sm)))
     (= (simplified-model-hiA (dlv-b-simplified sm b))
        (simplified-model-hiA sm))
     :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule
                dlv-1-simplified-definition-rule))))

(propertyd dlv-b-simplified-doesnt-change-cur (sm :simplified-model b :nat)
     :h (<= b (len (simplified-model-chan sm)))
     (= (simplified-model-cur (dlv-b-simplified sm b))
        (simplified-model-cur sm))
     :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule
                dlv-1-simplified-definition-rule))))

(propertyd dlv-b-simplified-doesnt-change-N (sm :simplified-model b :nat)
     :h (<= b (len (simplified-model-chan sm)))
     (= (simplified-model-N (dlv-b-simplified sm b))
        (simplified-model-N sm))
     :hints (("Goal" :in-theory (enable dlv-b-simplified-definition-rule
                dlv-1-simplified-definition-rule))))

(propertyd many-steps-simplified-full-contracts (sm :simplified-model R b steps :pos)
     :h (^ (<= (+ (simplified-model-cur sm) (* R steps))
         (+ (simplified-model-hiA sm) (simplified-model-N sm)))
     (<= b (min R (simplified-model-d-cap sm)))
     (<= (len (simplified-model-chan sm))
         (simplified-model-d-cap sm)))
     (if (= steps 1)
         (^ (<= (+ (simplified-model-cur sm) R)
          (+ (simplified-model-hiA sm) (simplified-model-N sm)))
      (<= b (min R (simplified-model-d-cap sm)))
      (<= (len (simplified-model-chan sm))
          (simplified-model-d-cap sm)))
       (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm))
    ;; outer contracts
    (<= (+ (simplified-model-cur (single-step-simplified sm R b))
           (* R (1- steps)))
        (+ (simplified-model-hiA (single-step-simplified sm R b))
           (simplified-model-N (single-step-simplified sm R b))))
     (<= b (min R (simplified-model-d-cap (single-step-simplified sm R b))))
     (<= (len (simplified-model-chan (single-step-simplified sm R b)))
         (simplified-model-d-cap (single-step-simplified sm R b)))))
     :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
         (:instance snd-r-simplified-incrs-len)
         (:instance snd-r-simplified-cur)
         (:instance snd-r-doesnt-change-consts)
         (:instance dlv-b-simplified-doesnt-change-cur-hia-n
              (sm (snd-r-simplified sm r)))
         (:instance dlv-b-simplified-doesnt-change-d-cap
              (sm (snd-r-simplified sm r)))
         (:instance dlv-b-simplified-decrs-len
              (sm (snd-r-simplified sm r)))))))

(definecd many-steps-simplified (sm :simplified-model R b steps :pos) :simplified-model
   :ic (^ (<= (+ (simplified-model-cur sm) (* R steps))
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (if (= steps 1)
       (single-step-simplified sm R b)
     (many-steps-simplified (single-step-simplified sm R b) R b (1- steps)))
   :body-contracts-hints (("Goal" :use (:instance many-steps-simplified-full-contracts))))

(propertyd all-1-last (tdgs :tdgs)
     :h (^ (all-1 tdgs) (consp tdgs))
     (^ (<= 0 (+ -1 (len tdgs)))
        (tdgp (nth (+ -1 (len tdgs)) tdgs))
        (stringp (tdg-pld (nth (+ -1 (len tdgs)) tdgs)))
        (= (length (tdg-pld (nth (1- (len tdgs)) tdgs))) 1))
     :hints (("Goal" :in-theory (enable all-1-definition-rule))))

(propertyd all-inf-take (tdgs :tdgs)
     :h (^ (all-inf tdgs) (consp tdgs))
     (all-inf (take (1- (len tdgs)) tdgs))
     :instructions ((:induct (all-1-take-inductor tdgs))
        (:in-theory (enable all-inf-definition-rule))
        (:use (:instance all-inf-definition-rule
             (tdgs (take (+ -1 (len tdgs)) tdgs))))
        :pro :prove :prove))

(propertyd all-inf-remove-ith (tdgs :tdgs)
     :h (^ (consp tdgs) (all-inf tdgs))
     (all-inf (remove-ith tdgs (1- (len tdgs))))
     :hints (("Goal" :in-theory (enable all-inf-take
                take-all-but-last-is-remove-last-tdgs))))

(propertyd set-rec-set-s2r-get-s2r (sys :system rcv :poss s2r :tbf)
     (== (system-s2r (mset :receiver rcv (mset :s2r s2r sys))) s2r))

(propertyd tbf-eq->-bkt-eq (tbf0 tbf1 :tbf)
     :h (== tbf0 tbf1)
     (= (tbf-bkt tbf0) (tbf-bkt tbf1)))

(propertyd tbf-eq->-data-eq (tbf0 tbf1 :tbf)
     :h (== tbf0 tbf1)
     (== (tbf-data tbf0) (tbf-data tbf1)))

(propertyd tbf-fwd-extractor (tbf :tbf)
     :h (^ (all-1 (tbf-data tbf))
     (consp (tbf-data tbf))
     (posp (tbf-bkt tbf)))
     (^ (natp (+ -1 (len (tbf-data tbf))))
        (< (+ -1 (len (tbf-data tbf)))
     (len (tbf-data tbf)))
        (<= (length (tdg-pld (nth (+ -1 (len (tbf-data tbf)))
                                      (tbf-data tbf))))
      (tbf-bkt tbf))
        (== (tbf-data (tbf-fwd tbf (1- (len (tbf-data tbf)))))
      (remove-ith (tbf-data tbf)
            (+ -1 (len (tbf-data tbf)))))
        (= (tbf-bkt (tbf-fwd tbf (1- (len (tbf-data tbf)))))
     (1- (tbf-bkt tbf))))
     :hints (("Goal" :use ((:instance tbf-fwd-definition-rule (i (1- (len (tbf-data tbf)))))
         (:instance data-extractor 
              (D (remove-ith (tbf-data tbf)
                 (+ -1 (len (tbf-data tbf)))))
              (bkt (+ (tbf-bkt tbf)
                (- (length (tdg-pld
                (nth (+ -1 (len (tbf-data tbf)))
                     (tbf-data tbf))))))))
         (:instance bkt-extractor
              (D (remove-ith (tbf-data tbf)
                 (+ -1 (len (tbf-data tbf)))))
              (bkt (+ (tbf-bkt tbf)
                (- (length (tdg-pld
                (nth (+ -1 (len (tbf-data tbf)))
                     (tbf-data tbf))))))))
         (:instance all-1-works-lst (tdgs (tbf-data tbf)))))))

(propertyd dlv-1-preserves-all-inf-all-1 (sys :system)
     :h (^ (all-1 (tbf-data (system-s2r sys)))
     (all-inf (tbf-data (system-s2r sys)))
     (posp (tbf-bkt (system-s2r sys)))
     (consp (tbf-data (system-s2r sys))))
     (^ (all-1 (tbf-data (system-s2r (dlv-1 sys))))
        (all-inf (tbf-data (system-s2r (dlv-1 sys))))
        (= (len (tbf-data (system-s2r (dlv-1 sys))))
     (1- (len (tbf-data (system-s2r sys)))))
        (= (tbf-bkt (system-s2r (dlv-1 sys)))
     (1- (tbf-bkt (system-s2r sys)))))
     :instructions
     ((:use (:instance dlv-1-definition-rule))
      :pro
      (:claim (== (system-s2r (dlv-1 sys))
      (tbf-fwd (system-s2r sys)
         (+ -1 (len (tbf-data (system-s2r sys)))))))
      (:drop 1)
      (:claim (== (tbf-data (system-s2r (dlv-1 sys)))
      (tbf-data (tbf-fwd (system-s2r sys)
             (+ -1
                (len (tbf-data (system-s2r sys))))))))
      (:claim (= (tbf-bkt (system-s2r (dlv-1 sys)))
           (tbf-bkt (tbf-fwd (system-s2r sys)
           (+ -1
              (len (tbf-data (system-s2r sys))))))))
      (:use (:instance tbf-fwd-extractor
           (tbf (system-s2r sys))))
      :pro
      (:claim
       (and (natp (+ -1 (len (tbf-data (system-s2r sys)))))
      (< (+ -1 (len (tbf-data (system-s2r sys))))
         (len (tbf-data (system-s2r sys))))
      (<= (length (tdg-pld (nth (+ -1 (len (tbf-data (system-s2r sys))))
              (tbf-data (system-s2r sys)))))
          (tbf-bkt (system-s2r sys)))
      (equal (tbf-data (tbf-fwd (system-s2r sys)
              (+ -1 (len (tbf-data (system-s2r sys))))))
       (remove-ith (tbf-data (system-s2r sys))
             (+ -1 (len (tbf-data (system-s2r sys))))))
      (= (tbf-bkt (tbf-fwd (system-s2r sys)
               (+ -1 (len (tbf-data (system-s2r sys))))))
         (+ -1 (tbf-bkt (system-s2r sys))))))
      (:drop 1)
      (:claim (= (tbf-bkt (system-s2r (dlv-1 sys)))
           (+ -1 (tbf-bkt (system-s2r sys)))))
      (:claim (= (len (tbf-data (system-s2r (dlv-1 sys))))
           (+ -1 (len (tbf-data (system-s2r sys))))))
      (:use (:instance all-inf-remove-ith
           (tdgs (tbf-data (system-s2r sys)))))
      (:use (:instance all-1-remove-ith
           (tdgs (tbf-data (system-s2r sys)))))
      :prove))      

;; How many steps does it take until the channel is R packets away from being full?
(definecd steps-to-fill (R b d-cap :pos) :pos
  :ic (^ (< b R) ;; overtransmission
   (< R d-cap)
   (natp (/ (- d-cap R) (- R b)))) ;; (R - b) needs to divide (dcap - R)
  (/ (- d-cap R) (- R b)))

(check= (steps-to-fill 8 4 100) 23) ;; Example of usage.

;; Prove that after (steps-to-fill R b d-cap) many steps, the ack has been increased by
;; (steps-to-fill R b d-cap) * b, and the channel is [ (steps-to-fill R b d-cap) R + cur_0, ...,
;; ..., (steps-to-fill R b d-cap) b + cur_0 ].  In order to prove this, we are going to need
;; to introducer an inductor that mirrors many-steps-simplified.

(definecd many-steps-inductor (sm :simplified-model R b steps :pos) :pos
  (if (= steps 1) 1 (many-steps-inductor sm R b (1- steps))))

(definecd many-steps-1-inductor (sm :simplified-model R b steps :pos) :pos
  :ic (^ (<= (+ (simplified-model-cur sm) (* R steps))
       (+ (simplified-model-hiA sm) (simplified-model-N sm)))
   (<= b (min R (simplified-model-d-cap sm)))
   (<= (len (simplified-model-chan sm))
       (simplified-model-d-cap sm)))
  (if (= steps 1) 1 (many-steps-1-inductor (single-step-simplified sm R b) R b (1- steps)))
  :body-contracts-hints (("Goal" :use (:instance many-steps-simplified-full-contracts))))

(defthm many-steps-1-commute
 (=> (^ (simplified-modelp sm)
        (posp r)
        (posp b)
        (posp steps)
        (<= (+ (simplified-model-cur sm)
               (* r (1+ steps)))
            (+ (simplified-model-hia sm)
               (simplified-model-n sm)))
        (<= b (min r (simplified-model-d-cap sm)))
        (<= (len (simplified-model-chan sm))
            (simplified-model-d-cap sm)))
     (== (many-steps-simplified (single-step-simplified sm r b)
                                r b steps)
         (single-step-simplified (many-steps-simplified sm r b steps)
                                 r b)))
 :instructions
 ((:induct (many-steps-1-inductor sm r b steps))
  :prove (:casesplit (= steps 1))
  (:in-theory (enable many-steps-simplified-definition-rule))
  :prove
  (:use (:instance single-step-simplified-definition-rule))
  :pro
  (:claim (equal (single-step-simplified sm r b)
                 (dlv-b-simplified (snd-r-simplified sm r)
                                   b)))
  (:drop 1)
  (:use (:instance snd-r-doesnt-change-consts))
  :pro
  (:claim (and (= (simplified-model-d-cap (snd-r-simplified sm r))
                  (simplified-model-d-cap sm))
               (= (simplified-model-ack (snd-r-simplified sm r))
                  (simplified-model-ack sm))
               (= (simplified-model-hia (snd-r-simplified sm r))
                  (simplified-model-hia sm))
               (= (simplified-model-n (snd-r-simplified sm r))
                  (simplified-model-n sm))))
  (:drop 1)
  (:use (:instance snd-r-simplified-cur))
  :pro
  (:claim (= (simplified-model-cur (snd-r-simplified sm r))
             (+ (simplified-model-cur sm) r)))
  (:drop 1)
  (:use (:instance snd-r-simplified-incrs-len))
  :pro
  (:claim (= (len (simplified-model-chan (snd-r-simplified sm r)))
             (min (+ (len (simplified-model-chan sm)) r)
                  (simplified-model-d-cap sm))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-decrs-len
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim
     (= (len (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r)
                                                      b)))
        (+ (len (simplified-model-chan (snd-r-simplified sm r)))
           (- b))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-doesnt-change-d-cap
                   (sm (snd-r-simplified sm r))))
  (:use (:instance dlv-b-simplified-doesnt-change-cur
                   (sm (snd-r-simplified sm r))))
  (:use (:instance dlv-b-simplified-doesnt-change-hia
                   (sm (snd-r-simplified sm r))))
  (:use (:instance dlv-b-simplified-doesnt-change-n
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim (= (simplified-model-n (dlv-b-simplified (snd-r-simplified sm r)
                                                   b))
             (simplified-model-n (snd-r-simplified sm r))))
  (:claim (= (simplified-model-hia (dlv-b-simplified (snd-r-simplified sm r)
                                                     b))
             (simplified-model-hia (snd-r-simplified sm r))))
  (:claim (= (simplified-model-cur (dlv-b-simplified (snd-r-simplified sm r)
                                                     b))
             (simplified-model-cur (snd-r-simplified sm r))))
  (:claim
       (= (simplified-model-d-cap (dlv-b-simplified (snd-r-simplified sm r)
                                                    b))
          (simplified-model-d-cap (snd-r-simplified sm r))))
  (:drop 1 2 3 4)
  (:claim (equal (many-steps-simplified
                      (single-step-simplified (single-step-simplified sm r b)
                                              r b)
                      r b (+ -1 steps))
                 (single-step-simplified
                      (many-steps-simplified (single-step-simplified sm r b)
                                             r b (+ -1 steps))
                      r b)))
  (:drop 9)
  (:use (:instance many-steps-simplified-definition-rule
                   (sm (single-step-simplified sm r b))))
  (:use (:instance many-steps-simplified-definition-rule))
  :pro
  (:claim (== (many-steps-simplified sm r b steps)
              (many-steps-simplified (single-step-simplified sm r b)
                                     r b (+ -1 steps))))
  (:claim (== (single-step-simplified (many-steps-simplified sm r b steps)
                                      r b)
              (single-step-simplified
                   (many-steps-simplified (single-step-simplified sm r b)
                                          r b (+ -1 steps))
                   r b)))
  (:claim (== (many-steps-simplified (single-step-simplified sm r b)
                                     r b steps)
              (many-steps-simplified
                   (single-step-simplified (single-step-simplified sm r b)
                                           r b)
                   r b (+ -1 steps))))
  :prove
  (:use (:instance many-steps-simplified-definition-rule
                   (sm (single-step-simplified sm r b))))
  (:use (:instance many-steps-simplified-definition-rule))
  (:use (:instance single-step-simplified-definition-rule))
  :pro
  (:claim (equal (single-step-simplified sm r b)
                 (dlv-b-simplified (snd-r-simplified sm r)
                                   b)))
  (:drop 1)
  (:use (:instance snd-r-doesnt-change-consts))
  :pro
  (:claim (and (= (simplified-model-d-cap (snd-r-simplified sm r))
                  (simplified-model-d-cap sm))
               (= (simplified-model-ack (snd-r-simplified sm r))
                  (simplified-model-ack sm))
               (= (simplified-model-hia (snd-r-simplified sm r))
                  (simplified-model-hia sm))
               (= (simplified-model-n (snd-r-simplified sm r))
                  (simplified-model-n sm))))
  (:drop 1)
  (:use (:instance snd-r-simplified-cur))
  :pro
  (:claim (= (simplified-model-cur (snd-r-simplified sm r))
             (+ (simplified-model-cur sm) r)))
  (:drop 1)
  (:use (:instance snd-r-simplified-incrs-len))
  :pro
  (:claim (= (len (simplified-model-chan (snd-r-simplified sm r)))
             (min (+ (len (simplified-model-chan sm)) r)
                  (simplified-model-d-cap sm))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-doesnt-change-d-cap
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim
       (= (simplified-model-d-cap (dlv-b-simplified (snd-r-simplified sm r)
                                                    b))
          (simplified-model-d-cap (snd-r-simplified sm r))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-doesnt-change-cur
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim (= (simplified-model-cur (dlv-b-simplified (snd-r-simplified sm r)
                                                     b))
             (simplified-model-cur (snd-r-simplified sm r))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-doesnt-change-hia
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim (= (simplified-model-hia (dlv-b-simplified (snd-r-simplified sm r)
                                                     b))
             (simplified-model-hia (snd-r-simplified sm r))))
  (:drop 1)
  (:use (:instance dlv-b-simplified-doesnt-change-n
                   (sm (snd-r-simplified sm r))))
  :pro
  (:claim (= (simplified-model-n (dlv-b-simplified (snd-r-simplified sm r)
                                                   b))
             (simplified-model-n (snd-r-simplified sm r))))
  (:drop 1)
  (:claim (equal (many-steps-simplified sm r b steps)
                 (single-step-simplified sm r b)))
  (:drop 1)
  (:claim (<= (+ (simplified-model-cur (single-step-simplified sm r b))
                 (* r steps))
              (+ (simplified-model-hia (single-step-simplified sm r b))
                 (simplified-model-n (single-step-simplified sm r b)))))
  (:claim
       (<= b
           (min r
                (simplified-model-d-cap (single-step-simplified sm r b)))))
  (:use (:instance dlv-b-simplified-decrs-len
                   (sm (snd-r-simplified sm r))))
  :prove))

