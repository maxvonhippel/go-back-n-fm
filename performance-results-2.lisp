(in-package "ACL2S")
(include-book "performance-results-1")

(propertyd single-step-simplified-incrs-cur (sm :simplified-model R b :pos)
   :h (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (= (simplified-model-cur (single-step-simplified sm R b))
      (+ (simplified-model-cur sm) R))
   :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
       (:instance snd-r-simplified-cur)
       (:instance snd-r-doesnt-change-consts)
       (:instance snd-r-simplified-incrs-len)
       (:instance dlv-b-simplified-doesnt-change-cur (sm (snd-r-simplified sm R)))))))

(propertyd single-step-simplified-hiA (sm :simplified-model R b :pos)
   :h (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (= (simplified-model-hiA (single-step-simplified sm R b))
      (simplified-model-hiA sm))
   :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
       (:instance snd-r-simplified-cur)
       (:instance snd-r-doesnt-change-consts)
       (:instance snd-r-simplified-incrs-len)
       (:instance dlv-b-simplified-doesnt-change-hiA (sm (snd-r-simplified sm R)))))))

(propertyd single-step-simplified-N (sm :simplified-model R b :pos)
   :h (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (= (simplified-model-N (single-step-simplified sm R b))
      (simplified-model-N sm))
   :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
       (:instance snd-r-simplified-cur)
       (:instance snd-r-doesnt-change-consts)
       (:instance snd-r-simplified-incrs-len)
       (:instance dlv-b-simplified-doesnt-change-N (sm (snd-r-simplified sm R)))))))

(propertyd single-step-simplified-len (sm :simplified-model R b :pos)
   :h (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (= (len (simplified-model-chan (single-step-simplified sm R b)))
      (- (min (simplified-model-d-cap sm) (+ R (len (simplified-model-chan sm)))) b))
   :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
       (:instance snd-r-simplified-cur)
       (:instance snd-r-doesnt-change-consts)
       (:instance snd-r-simplified-incrs-len)
       (:instance dlv-b-simplified-decrs-len
            (sm (snd-r-simplified sm r)))))))

(propertyd single-step-simplified-d-cap (sm :simplified-model R b :pos)
   :h (^ (<= (+ (simplified-model-cur sm) R)
        (+ (simplified-model-hiA sm) (simplified-model-N sm)))
    (<= b (min R (simplified-model-d-cap sm)))
    (<= (len (simplified-model-chan sm))
        (simplified-model-d-cap sm)))
   (= (simplified-model-d-cap (single-step-simplified sm R b))
      (simplified-model-d-cap sm))
   :hints (("Goal" :use ((:instance single-step-simplified-definition-rule)
       (:instance snd-r-simplified-cur)
       (:instance snd-r-doesnt-change-consts)
       (:instance snd-r-simplified-incrs-len)
       (:instance dlv-b-simplified-doesnt-change-d-cap (sm (snd-r-simplified sm R)))))))

(propertyd many-steps-simplified-effect-cur-hiA-N (sm :simplified-model R b steps :pos)
     :h (^ (<= (+ (simplified-model-cur sm) (* R steps))
         (+ (simplified-model-hiA sm) (simplified-model-N sm)))
     (<= b (min R (simplified-model-d-cap sm)))
     (<= (len (simplified-model-chan sm))
         (simplified-model-d-cap sm)))
     (^ (= (simplified-model-cur (many-steps-simplified sm R b steps))
     (+ (* R steps) (simplified-model-cur sm)))
        (= (simplified-model-hiA (many-steps-simplified sm R b steps))
     (simplified-model-hiA sm))
        (= (simplified-model-N (many-steps-simplified sm R b steps))
     (simplified-model-N sm))
        (= (simplified-model-d-cap (many-steps-simplified sm R b steps))
     (simplified-model-d-cap sm)))
        :instructions ((:induct (many-steps-1-inductor sm r b steps))
           (:use (:instance single-step-simplified-incrs-cur))
           (:use (:instance single-step-simplified-hia))
           (:use (:instance single-step-simplified-n))
           (:use (:instance single-step-simplified-len))
           (:use (:instance many-steps-simplified-definition-rule))
           (:use (:instance single-step-simplified-d-cap))
           :pro
           (:claim (!= steps 1))
           :prove
           (:use (:instance many-steps-simplified-definition-rule))
           :pro
           (:claim (== (many-steps-simplified sm r b steps)
           (single-step-simplified sm r b)))
           (:use (:instance single-step-simplified-incrs-cur))
           (:use (:instance single-step-simplified-hia))
           (:use (:instance single-step-simplified-n))
           (:use (:instance single-step-simplified-len))
           (:use (:instance single-step-simplified-d-cap))
           :prove))

(propertyd arith-prop-steps-to-fill (r b steps :pos sm :simplified-model)
     :h (^ (< b R)
     (< R (simplified-model-d-cap sm))
     (<= (len (simplified-model-chan sm)) (simplified-model-d-cap sm))
     (natp (/ (- (simplified-model-d-cap sm) R) (- R b)))
     (<= (+ (simplified-model-cur sm)
      (* R (steps-to-fill R b (simplified-model-d-cap sm))))
         (+ (simplified-model-hia sm)
      (simplified-model-n sm)))
     (<= steps (steps-to-fill R b (simplified-model-d-cap sm)))
     (<= (* (+ r (- b)) (+ -1 steps))
         (* (+ r (- b))
      (+ -1
         (steps-to-fill r b (simplified-model-d-cap sm))))))
     (<= (+ (* (+ r (- b)) (+ -1 steps)) R)
         (simplified-model-d-cap sm))
     :hints (("Goal" :in-theory (enable steps-to-fill-definition-rule))))

(propertyd top-dn-equality (top0 top1 rem0 rem1 :pos)
     :h (^ (= top0 top1) (= rem0 rem1) (<= rem1 top1))
     (== (top-dn top0 rem0) (top-dn top1 rem1)))

(propertyd top-dn-equality-contracts (sm :simplified-model R b steps :pos)
     :h (^ (!= steps 1)
     (< b R)
     (<= (+ (simplified-model-cur sm) (* R steps))
         (+ (simplified-model-hiA sm) (simplified-model-N sm)))
     (<= b (min R (simplified-model-d-cap sm)))
     (<= (len (simplified-model-chan sm))
         (simplified-model-d-cap sm))
     (= (len
         (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
        (* (+ r (- b)) (+ -1 steps))))
     (and
      (posp
       (+
        (+ -1
     (len (simplified-model-chan
           (many-steps-simplified sm r b (+ -1 steps)))))
        (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps)))))
      (posp (+ (simplified-model-cur sm)
         (* r (+ -1 steps))
         -1))
      (posp
       (len
        (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
      (posp (* (+ r (- b)) (+ -1 steps)))))

(propertyd ineq-helper-sm-steps-to-fill (sm :simplified-model R b steps :pos)
     :h (^ (< b R)
     (< R (simplified-model-d-cap sm))
     (natp (/ (- (simplified-model-d-cap sm) R) (- R b)))
     (<= steps (steps-to-fill R b (simplified-model-d-cap sm)))
     (<= (+ (simplified-model-cur sm)
         (* R (steps-to-fill R b (simplified-model-d-cap sm))))
      (+ (simplified-model-hia sm)
         (simplified-model-n sm))))
     (<= (+ (simplified-model-cur sm)
      (* r steps))
         (+ (simplified-model-hia sm)
      (simplified-model-n sm)))
     :hints (("Goal" :in-theory (enable steps-to-fill-definition-rule))))

(propertyd b-bnd-helper (sm :simplified-model R b steps :pos)
     :h (^ (< b R)
     (< R (simplified-model-d-cap sm)))
     (<= b (min r (simplified-model-d-cap sm))))

(propertyd ack-reduction-helper (sm :simplified-model b steps :pos)
     :h (!= steps 1)
     (= (+ b (+ (* b (+ -1 steps))
          (simplified-model-ack sm)))
        (+ (* b steps) (simplified-model-ack sm))))

(propertyd sm-reducer (sm0 sm1 :simplified-model)
     :h (== sm0 sm1)
     (= (simplified-model-ack sm0) (simplified-model-ack sm1)))

(propertyd single-step-simplifiedp (sm :simplified-model R b :pos)
     :h (^ (<= (+ (simplified-model-cur sm) R)
         (+ (simplified-model-hiA sm) (simplified-model-N sm)))
     (<= b (min R (simplified-model-d-cap sm)))
     (<= (len (simplified-model-chan sm))
         (simplified-model-d-cap sm)))
     (simplified-modelp (single-step-simplified sm R b)))

;; We show that after "steps" many (dlv-b (tick (snd-R ...)))'s, ack has increased
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
     ;;(posp steps)
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
        (simplified-model-cur sm))))
     :instructions
     ((:induct (many-steps-inductor sm r b steps))
      :pro
      (:claim
       (and
        (equal
         (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))
         (top-dn (+ (simplified-model-cur sm)
        (* r (+ -1 steps))
        -1)
           (* (+ r (- b)) (+ -1 steps))))
        (= (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps)))
     (+ (* b (+ -1 steps))
        (simplified-model-ack sm)))
        (= (simplified-model-cur (many-steps-simplified sm r b (+ -1 steps)))
     (+ (* r (+ -1 steps))
        (simplified-model-cur sm)))))
      (:drop 3)
      (:use (:instance many-steps-simplified-definition-rule))
      :pro (:claim (!= 1 steps))
      (:claim (== (many-steps-simplified sm r b steps)
      (many-steps-simplified (single-step-simplified sm r b)
                 r b (+ -1 steps))))
      (:claim (== (simplified-model-chan (many-steps-simplified sm r b steps))
      (simplified-model-chan
       (many-steps-simplified (single-step-simplified sm r b)
            r b (+ -1 steps)))))
      (:claim (= (simplified-model-ack (many-steps-simplified sm r b steps))
           (simplified-model-ack
      (many-steps-simplified (single-step-simplified sm r b)
                 r b (+ -1 steps)))))
      (:claim (= (simplified-model-cur (many-steps-simplified sm r b steps))
           (simplified-model-cur
      (many-steps-simplified (single-step-simplified sm r b)
                 r b (+ -1 steps)))))
      (:drop 1)
      (:use (:instance many-steps-1-commute
           (steps (1- steps))))
      :pro
      (:claim
       (== (many-steps-simplified sm r b steps)
     (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
           r b)))
      (:claim
       (^
        (==
         (simplified-model-chan (many-steps-simplified sm r b steps))
         (simplified-model-chan
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b)))
        (=
         (simplified-model-cur (many-steps-simplified sm r b steps))
         (simplified-model-cur
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b)))
        (=
         (simplified-model-ack (many-steps-simplified sm r b steps))
         (simplified-model-ack
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b)))))
      (:drop 24 25 26)
      (:drop 1)
      (:use (:instance many-steps-simplified-effect-cur-hia-n
           (steps (1- steps))))
      :pro
      (:claim
       (and
        (= (simplified-model-cur (many-steps-simplified sm r b (+ -1 steps)))
     (+ (* r (+ -1 steps))
        (simplified-model-cur sm)))
        (= (simplified-model-hia (many-steps-simplified sm r b (+ -1 steps)))
     (simplified-model-hia sm))
        (= (simplified-model-n (many-steps-simplified sm r b (+ -1 steps)))
     (simplified-model-n sm))
        (= (simplified-model-d-cap (many-steps-simplified sm r b (+ -1 steps)))
     (simplified-model-d-cap sm))))
      (:drop 1)
      (:use (:instance single-step-simplified-incrs-cur
           (sm (many-steps-simplified sm r b (1- steps)))))
      (:use (:instance top-dn-len
           (a (* (+ r (- b)) (+ -1 steps)))
           (b (+ (simplified-model-cur sm)
           (* r (+ -1 steps))
           -1))))
      (:use (:instance arith-prop-steps-to-fill))
      :pro
      (:claim
       (<=
        (+
         (len
    (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
         r)
        (simplified-model-d-cap (many-steps-simplified sm r b (+ -1 steps)))))
      (:claim (= (simplified-model-cur (many-steps-simplified sm r b steps))
           (+ (* r steps)
        (simplified-model-cur sm))))
      (:drop 1 2 3)
      (:use (:instance top-dn-len
           (a (* (+ r (- b)) (+ -1 steps)))
           (b (+ (simplified-model-cur sm)
           (* r (+ -1 steps))
           -1))))
      :pro
      (:claim
       (=
        (len (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
        (* (+ r (- b)) (+ -1 steps))))
      (:drop 1)
      (:claim (<= (* (+ r (- b)) (+ -1 steps))
      (+ (simplified-model-cur sm)
         (* r (+ -1 steps))
         -1)))
      (:claim
       (=
        (len (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
        (* (+ r (- b)) (+ -1 steps))))
      (:use
       (:instance
        top-dn-equality
        (top1 (+ (simplified-model-cur sm)
           (* r (+ -1 steps))
           -1))
        (rem1 (* (+ r (- b)) (+ -1 steps)))
        (top0
         (+
    (+
     -1
     (len
      (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
    (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps)))))
        (rem0
         (len
    (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))))
      (:use (:instance top-dn-equality-contracts))
      (:use (:instance b-bnd-helper))
      (:use (:instance ineq-helper-sm-steps-to-fill))
      :pro
      (:claim (<= b (min r (simplified-model-d-cap sm))))
      (:claim (<= (+ (simplified-model-cur sm)
         (* r steps))
      (+ (simplified-model-hia sm)
         (simplified-model-n sm))))
      (:claim
       (and
        (posp
         (+
    (+
     -1
     (len
      (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
    (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps)))))
        (posp (+ (simplified-model-cur sm)
           (* r (+ -1 steps))
           -1))
        (posp
         (len
    (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
        (posp (* (+ r (- b)) (+ -1 steps)))))
      (:drop 3)
      (:drop 1)
      (:drop 1)
      (:claim
       (posp
        (+
         (+
    -1
    (len
     (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
         (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))))
      (:claim (posp (+ (simplified-model-cur sm)
           (* r (+ -1 steps))
           -1)))
      (:claim
       (posp
        (len
         (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))))
      (:claim (posp (* (+ r (- b)) (+ -1 steps))))
      (:claim
       (=
        (+
         (+
    -1
    (len
     (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
         (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))
        (+ (simplified-model-cur sm)
     (* r (+ -1 steps))
     -1)))
      (:claim
       (=
        (len (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
        (* (+ r (- b)) (+ -1 steps))))
      (:claim
       (equal
        (top-dn
         (+
    (+
     -1
     (len
      (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
    (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))
         (len
    (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
        (top-dn (+ (simplified-model-cur sm)
       (* r (+ -1 steps))
       -1)
          (* (+ r (- b)) (+ -1 steps)))))
      (:drop 1)
      (:claim
       (not
        (endp
         (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))))
      (:claim
       (==
        (and
         (not
    (endp
     (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
         (top-dn
    (+ (+ -1
          (len (simplified-model-chan
          (many-steps-simplified sm r b (+ -1 steps)))))
       (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))
    (len
     (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))))
        (top-dn (+ (simplified-model-cur sm)
       (* r (+ -1 steps))
       -1)
          (* (+ r (- b)) (+ -1 steps)))))
      (:claim
       (==
        (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))
        (and
         (not
    (endp
     (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps)))))
         (top-dn
    (+ (+ -1
          (len (simplified-model-chan
          (many-steps-simplified sm r b (+ -1 steps)))))
       (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))
    (len (simplified-model-chan
          (many-steps-simplified sm r b (+ -1 steps))))))))
      (:claim (simplified-modelp (many-steps-simplified sm r b (+ -1 steps))))
      (:claim
       (=
        (simplified-model-cur (many-steps-simplified sm r b (+ -1 steps)))
        (+
         (len
    (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
         (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps))))))
      (:use (:instance overtransmission-filling
           (sm (many-steps-simplified sm r b (1- steps)))))
      :pro
      (:claim
       (and
        (equal
         (simplified-model-chan
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b))
         (top-dn
    (+
     (+
      -1
      (len
       (simplified-model-chan
        (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
              r b))))
     (simplified-model-ack
      (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
            r b)))
    (len
     (simplified-model-chan
      (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
            r b)))))
        (equal
         (simplified-model-chan
    (dlv-b-simplified
     (snd-r-simplified (many-steps-simplified sm r b (+ -1 steps))
           r)
     b))
         (top-dn
    (+ -1 r
       (simplified-model-cur (many-steps-simplified sm r b (+ -1 steps))))
    (+
     (len
      (simplified-model-chan (many-steps-simplified sm r b (+ -1 steps))))
     r (- b))))
        (=
         (simplified-model-cur
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b))
         (+
    (len
     (simplified-model-chan
      (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
            r b)))
    (simplified-model-ack
     (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
           r b))))
        (=
         (simplified-model-ack
    (single-step-simplified (many-steps-simplified sm r b (+ -1 steps))
          r b))
         (+
    b
    (simplified-model-ack (many-steps-simplified sm r b (+ -1 steps)))))))
      (:drop 1)
      (:claim (equal (simplified-model-chan (many-steps-simplified sm r b steps))
         (top-dn (+ (simplified-model-cur sm)
              (* r steps)
              -1)
           (* (+ r (- b)) steps))))
      (:claim (= (simplified-model-ack (many-steps-simplified sm r b steps))
           (+ (* b steps)
        (simplified-model-ack sm))))
      :prove
      (:use (:instance many-steps-simplified-definition-rule))
      :pro
      (:claim (equal (many-steps-simplified sm r b steps)
         (single-step-simplified sm r b)))
      (:drop 1)
      (:use (:instance single-step-simplified-definition-rule))
      :pro
      (:claim (equal (single-step-simplified sm r b)
         (dlv-b-simplified (snd-r-simplified sm r)
               b)))
      (:drop 1)
      (:use (:instance overtransmission-filling))
      :pro
      (:claim (endp (simplified-model-chan sm)))
      (:claim
       (and
        (equal
         (simplified-model-chan (single-step-simplified sm r b))
         (top-dn
    (+ (+ -1
          (len (simplified-model-chan (single-step-simplified sm r b))))
       (simplified-model-ack (single-step-simplified sm r b)))
    (len (simplified-model-chan (single-step-simplified sm r b)))))
        (equal (simplified-model-chan (dlv-b-simplified (snd-r-simplified sm r)
                    b))
         (top-dn (+ -1 r (simplified-model-cur sm))
           (+ (len (simplified-model-chan sm))
        r (- b))))
        (= (simplified-model-cur (single-step-simplified sm r b))
     (+ (len (simplified-model-chan (single-step-simplified sm r b)))
        (simplified-model-ack (single-step-simplified sm r b))))
        (= (simplified-model-ack (single-step-simplified sm r b))
     (+ b (simplified-model-ack sm)))))
      (:drop 1)
      :prove))

