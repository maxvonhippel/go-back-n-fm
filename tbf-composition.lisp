(in-package "ACL2S")

;; Import theory of tbf
(include-book "tbf")

;; Next up, I claim that the serial composition of two TBFs _is_
;; (in some sense) just another TBF.  Let's formalize that claim,
;; via simulation.  First we need to define the composition.
;;
;;         sender ---> tbfA ---> tbfB ---> receiver
;;
(defdata two-tbf (list tbf tbf))

(check= (o-finp 4) t)
(check= (o-finp (make-ord 1 1 0)) nil)
(check= (o-finp (omega)) nil)

(definecd incr-ttl (tdgs :tdgs del :nat-ord) :tdgs
  (match tdgs
    (() ())
    ((tdg . rst) (cons (mset :del (o+ (tdg-del tdg) del) tdg)
		       (incr-ttl rst del)))))

(property incr-ttl-len (tdgs :tdgs del :nat-ord)
  (= (len (incr-ttl tdgs del)) (len tdgs))
  :hints (("Goal" :in-theory (enable incr-ttl-definition-rule))))

;; Given a pair of tbfs, we can come up with a new (third) tbf which in
;; some sense is equivalent to the serial composition of the prior two.
(definecd [+] (ttbf :two-tbf) :tbf
  (tbf
   ;; bucket capacity (b-cap)
   (tbf-b-cap (cadr ttbf))
   ;; link capacity (d-cap)
   (+ (tbf-d-cap (car ttbf)) (tbf-d-cap (cadr ttbf)))
   ;; bucket (b)
   (tbf-bkt (cadr ttbf))
   ;; rate (r)
   (tbf-rat (cadr ttbf))
   ;; time-to-live (ttl)
   (o+ (tbf-del (car ttbf)) (tbf-del (cadr ttbf)))
   ;; queue of data (D) -- timed 
   (append (incr-ttl (tbf-data (car ttbf)) (tbf-del (cadr ttbf)))
	   (tbf-data (cadr ttbf)))))

;; We say two TBFs are equivalent if they match everywhere except their
;; buckets and expiries.
;; Note, we will revisit this notion a little later in a more nuanced way.
(definecd ~= (t1 t2 :tbf) :bool
  (^ (= (tbf-b-cap t1) (tbf-b-cap t2))
     (= (tbf-d-cap t1) (tbf-d-cap t2))
     (= (tbf-rat t1) (tbf-rat t2))
     (== (tbf-del t1) (tbf-del t2))
     (== (tdgs->poss (tbf-data t1))
	 (tdgs->poss (tbf-data t2)))))

(property tdgs->poss-ignore-incr (tdgs :tdgs del :nat-ord)
  (== (tdgs->poss (incr-ttl tdgs del))
      (tdgs->poss tdgs))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
				     incr-ttl-definition-rule
				     |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(property tdgs->poss-app (tdgs0 tdgs1 :tdgs)
  (== (tdgs->poss (append tdgs0 tdgs1))
      (append (tdgs->poss tdgs0) (tdgs->poss tdgs1)))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
				     |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(property tdgs->poss-o+-car-ttl (p :pos del0 del1 :nat-ord pld :string tdgs :tdgs)
  (== (tdgs->poss (cons (tdg p (o+ del0 del1) pld) tdgs))
      (tdgs->poss (cons (tdg p del0 pld) tdgs)))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
				     |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(propertyd tdgs->poss-cons (tdg :tdg tdgs :tdgs)
	   (== (tdgs->poss (cons tdg tdgs))
	       (cons (tdg-id tdg) (tdgs->poss tdgs)))
	   :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
					      |MAP*-*(LAMBDA (D) (TDG-ID D))|))))

(property tricky-tdgs-append-step (ttbf :two-tbf p :pos pld :string)
  (== (tdgs->poss (append (cons (tdg p (o+ (tbf-del (car ttbf)) (tbf-del (cadr ttbf))) pld)
				(incr-ttl (tbf-data (car ttbf)) (tbf-del (cadr ttbf))))
			  (tbf-data (cadr ttbf))))
      (tdgs->poss (append (cons (tdg p (tbf-del (car ttbf)) pld) (tbf-data (car ttbf))) 
			  (tbf-data (cadr ttbf)))))
  :hints (("Goal" :use ((:instance tdgs->poss-app
				   (tdgs0 (cons (tdg p
						     (o+ (tbf-del (car ttbf))
							 (tbf-del (cadr ttbf)))
						     pld)
						(incr-ttl (tbf-data (car ttbf))
							  (tbf-del (cadr ttbf)))))
				   (tdgs1 (tbf-data (cadr ttbf))))
			(:instance tdgs->poss-app
				   (tdgs0 (cons (tdg p (tbf-del (car ttbf)) pld)
						(tbf-data (car ttbf))))
				   (tdgs1 (tbf-data (cadr ttbf))))
			(:instance tdgs->poss-cons
				   (tdg (tdg p
					    (o+ (tbf-del (car ttbf))
						(tbf-del (cadr ttbf)))
					    pld))
				   (tdgs (incr-ttl (tbf-data (car ttbf))
						   (tbf-del (cadr ttbf)))))
			(:instance tdgs->poss-cons
				   (tdg (tdg p (tbf-del (car ttbf)) pld))
				   (tdgs (tbf-data (car ttbf))))))))

(property tricky-dgs-re-arrange-step (ttbf :two-tbf p :pos pld :string)
  (== (tdgs->poss (append (cons (tdg p (o+ (tbf-del (car ttbf)) (tbf-del (cadr ttbf))) pld)
				(incr-ttl (tbf-data (car ttbf)) (tbf-del (cadr ttbf))))
			  (tbf-data (cadr ttbf))))
      (tdgs->poss (cons (tdg p (o+ (tbf-del (car ttbf)) (tbf-del (cadr ttbf))) pld)
			(append (incr-ttl (tbf-data (car ttbf)) (tbf-del (cadr ttbf)))
				(tbf-data (cadr ttbf))))))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule))))

(property sz-app (tdgs0 tdgs1 :tdgs) (= (+ (sz tdgs0) (sz tdgs1)) (sz (append tdgs0 tdgs1)))
  :hints (("Goal" :in-theory (enable sz-definition-rule))))

(property sz-incr-ttl (tdgs :tdgs o :nat-ord) (= (sz (incr-ttl tdgs o)) (sz tdgs))
  :hints (("Goal" :in-theory (enable sz-definition-rule incr-ttl-definition-rule))))

(property sz-[+]-D=len-+-Ds (ttbf :two-tbf)
  (= (sz (tbf-data ([+] ttbf))) (+ (sz (tbf-data (car ttbf))) (sz (tbf-data (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     incr-ttl-definition-rule
				     sz-definition-rule)
	   :use ((:instance sz-incr-ttl (tdgs (tbf-data (car ttbf)))
			    (o (tbf-del (cadr ttbf))))
		 (:instance sz-app
			   (tdgs0 (incr-ttl (tbf-data (car ttbf))
					    (tbf-del (cadr ttbf))))
			   (tdgs1 (tbf-data (cadr ttbf))))))))

(property if-car-tbf-not-full-then-ttbf-not-full (ttbf :two-tbf)
  :h (^ (< (sz (tbf-data (car ttbf))) (tbf-d-cap (car ttbf)))
	(<= (sz (tbf-data (cadr ttbf))) (tbf-d-cap (cadr ttbf))))
  (< (sz (tbf-data ([+] ttbf))) (tbf-d-cap ([+] ttbf)))
  :instructions ((:use (:instance sz-[+]-d=len-+-ds))
                 (:use (:instance [+]-definition-rule))
                 :pro
                 (:claim (= (sz (tbf-data ([+] ttbf)))
                            (+ (sz (tbf-data (car ttbf)))
                               (sz (tbf-data (cadr ttbf))))))
                 (:drop 2)
                 (:claim (= (tbf-d-cap ([+] ttbf))
                            (+ (tbf-d-cap (car ttbf))
                               (tbf-d-cap (cadr ttbf)))))
                 (:drop 1)
                 :prove))

(property ~=-D[+]-trn-lem1
  (ttbf :two-tbf p :pos pld :string)
  :h (^ (< (sz (tbf-data (car ttbf))) (tbf-d-cap (car ttbf)))
	(<= (sz (tbf-data (cadr ttbf))) (tbf-d-cap (cadr ttbf))))
  (== (tdgs->poss (tbf-data ([+] (list (tbf-prc (car ttbf) p pld) (cadr ttbf)))))
      (tdgs->poss (append (tbf-data (tbf-prc (car ttbf) p pld)) (tbf-data (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule))))

(property ~=-D[+]-trn-lem2-nodrop
  (ttbf :two-tbf p :pos pld :string)
  :h (^ (<= (+ (sz (tbf-data (car ttbf))) (length pld)) (tbf-d-cap (car ttbf)))
	(<= (sz (tbf-data (cadr ttbf))) (tbf-d-cap (cadr ttbf))))
  (== (tdgs->poss (append (tbf-data (tbf-prc (car ttbf) p pld)) (tbf-data (cadr ttbf))))
      (tdgs->poss (append (cons (tdg p (tbf-del (car ttbf)) pld) (tbf-data (car ttbf))) 
			  (tbf-data (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable tbf-prc-definition-rule))))

(property ~=-D[+]-trn-lem3-nodrop
  (ttbf :two-tbf p :pos pld :string)
  :h (^ (<= (+ (sz (tbf-data (car ttbf))) (length pld)) (tbf-d-cap (car ttbf)))
	(<= (sz (tbf-data (cadr ttbf))) (tbf-d-cap (cadr ttbf))))
  (== (tdgs->poss (append (cons (tdg p (tbf-del (car ttbf)) pld) (tbf-data (car ttbf))) 
			  (tbf-data (cadr ttbf))))
      (tdgs->poss (tbf-data (tbf-prc ([+] ttbf) p pld))))
  :instructions
  ((:use (:instance tricky-tdgs-append-step))
   (:use (:instance tricky-dgs-re-arrange-step))
   (:use (:instance tbf-prc-definition-rule (tbf ([+] ttbf)) (x p)))
   (:use (:instance [+]-definition-rule))
   (:use (:instance sz-[+]-d=len-+-ds))
   :pro
   (:claim (<= (+ (+ (sz (tbf-data (car ttbf)))
                     (sz (tbf-data (cadr ttbf))))
                  (length pld))
               (+ (tbf-d-cap (car ttbf))
                  (tbf-d-cap (cadr ttbf)))))
   (:in-theory (enable tbf-prc-definition-rule
                       sz-definition-rule [+]-definition-rule))
   :prove))

;; If (T1 |> T2) does a transmit, this is equivalent to (T1 [+] T2) doing
;; a transmit.
(encapsulate () (local (in-theory (enable sz-definition-rule)))
	     (propertyd transmission-rule (ttbf :two-tbf p :pos pld :string) 
			:h (^ (<= (+ (sz (tbf-data (car ttbf))) (length pld))
				  (tbf-d-cap (car ttbf)))
			      (<= (sz (tbf-data (cadr ttbf)))
				  (tbf-d-cap (cadr ttbf))))
			(~= ([+] (list (tbf-prc (car ttbf) p pld)
				       (cadr ttbf)))
			    (tbf-prc ([+] ttbf) p pld))
			:instructions
			((:use (:instance [+]-definition-rule))
			 (:use (:instance [+]-definition-rule
					  (ttbf (list (tbf-prc (car ttbf) p pld)
						      (cadr ttbf)))))
			 (:use (:instance tbf-prc-definition-rule (tbf (car ttbf))
					  (x p)))
			 (:use (:instance tbf-prc-definition-rule (tbf ([+] ttbf))
					  (x p)))
			 (:use (:instance ~=-definition-rule
					  (t1 ([+] (list (tbf-prc (car ttbf) p pld)
							 (cadr ttbf))))
					  (t2 (tbf-prc ([+] ttbf) p pld))))
			 (:in-theory (enable incr-ttl-definition-rule))
			 (:use (:instance ~=-d[+]-trn-lem3-nodrop))
			 :pro
			 (:claim (= (tbf-b-cap ([+] (list (tbf-prc (car ttbf) p pld)
							  (cadr ttbf))))
				    (tbf-b-cap (tbf-prc ([+] ttbf) p pld))))
			 
			 (:claim (== (tbf-del ([+] (list (tbf-prc (car ttbf) p pld)
							 (cadr ttbf))))
				     (tbf-del (tbf-prc ([+] ttbf) p pld))))
			 (:claim (== (tbf-data ([+] (list (tbf-prc (car ttbf) p pld)
							  (cadr ttbf))))
				     (app (incr-ttl (tbf-data (car (list (tbf-prc (car ttbf) p pld)
									 (cadr ttbf))))
						    (tbf-del (cadr (list (tbf-prc (car ttbf) p pld)
									 (cadr ttbf)))))
					  (tbf-data (cadr (list (tbf-prc (car ttbf) p pld)
								(cadr ttbf)))))))
			 (:use (:instance sz-[+]-d=len-+-ds))
			 :pro
			 (:claim (<= (+ (+ (sz (tbf-data (car ttbf))) (length pld))
					(sz (tbf-data (cadr ttbf))))
				     (+ (tbf-d-cap (car ttbf))
					(tbf-d-cap (cadr ttbf)))))
			 (:claim (<= (+ (sz (tbf-data ([+] ttbf))) (length pld))
				     (tbf-d-cap ([+] ttbf))))
			 :prove)))

(in-theory (disable ~=-d[+]-trn-lem1
		    ~=-d[+]-trn-lem2-nodrop
		    ~=-d[+]-trn-lem3-nodrop))

(propertyd nth-incr-ttl (tdgs :tdgs i :nat o :nat-ord)
	   :h (< i (len tdgs))
	   (^ (== (tdg-pld (nth i (incr-ttl tdgs o)))
		  (tdg-pld (nth i tdgs)))
	      (== (tdg-id (nth i (incr-ttl tdgs o)))
		  (tdg-id (nth i tdgs))))
	   :hints (("Goal" :in-theory (enable incr-ttl-definition-rule))))

(property [+]-dlv-contracts (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (^ (= (len (tbf-data ([+] ttbf)))
	(+ (len (tbf-data (car ttbf)))
	   (len (tbf-data (cadr ttbf)))))
     (< i (len (tbf-data ([+] ttbf))))
     (two-tbfp (list (tbf-fwd (car ttbf) i)
		     (cadr ttbf)))
     (<= (length (tdg-pld (nth i (tbf-data ([+] ttbf)))))
	 (tbf-bkt ([+] ttbf)))
     (recordp (cadr ttbf)))
  :hints (("Goal" :use ((:instance nth-incr-ttl
				   (tdgs (tbf-data (car ttbf)))
				   (o (tbf-del (cadr ttbf))))
			(:instance [+]-definition-rule))
	   :in-theory (enable incr-ttl-definition-rule))))

(definecd t1-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (~= ([+] (list (tbf-fwd (car ttbf) i) (cadr ttbf)))
      (tbf-fwd ([+] ttbf) i))
  :body-contracts-hints (("Goal" :use (:instance [+]-dlv-contracts))))

(property remove-ith-incr-ttl-commute (tdgs :tdgs i :nat del :nat-ord)
  :h (< i (len tdgs))
  (== (remove-ith (incr-ttl tdgs del) i)
      (incr-ttl (remove-ith tdgs i) del))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule
				     incr-ttl-definition-rule))))

(propertyd tdgs-nth-pld-app (tdgs0 tdgs1 :tdgs i :nat del :nat-ord)
	   :h (< i (len tdgs0))
	   (== (tdg-pld (nth i (append (incr-ttl tdgs0 del) tdgs1)))
	       (tdg-pld (nth i tdgs0)))
	   :hints (("Goal" :in-theory (enable incr-ttl-definition-rule))))

(property T1>T2-dlv-helper-1
  (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (^
   ;; contracts
   (< i (len (tbf-data ([+] ttbf))))
   (<= (length (tdg-pld (nth i (tbf-data ([+] ttbf)))))
       (tbf-bkt ([+] ttbf)))
   ;; thm 
   (= (tbf-b-cap ([+] (list (tbf-fwd (car ttbf) i)
			    (cadr ttbf))))
      (tbf-b-cap (tbf-fwd ([+] ttbf) i)))
   (= (tbf-d-cap ([+] (list (tbf-fwd (car ttbf) i)
			    (cadr ttbf))))
      (tbf-d-cap (tbf-fwd ([+] ttbf) i)))
   (= (tbf-rat ([+] (list (tbf-fwd (car ttbf) i)
			 (cadr ttbf))))
      (tbf-rat (tbf-fwd ([+] ttbf) i)))
   (== (tbf-del ([+] (list (tbf-fwd (car ttbf) i)
			   (cadr ttbf))))
       (tbf-del (tbf-fwd ([+] ttbf) i))))
  :hints (("Goal"
	   :use (:instance tdgs-nth-pld-app
			   (tdgs0 (tbf-data (car ttbf)))
			   (tdgs1 (tbf-data (cadr ttbf)))
			   (del (tbf-del (cadr ttbf))))
	   :in-theory (enable tbf-fwd-definition-rule
				     remove-ith-definition-rule
				     [+]-definition-rule
				     incr-ttl-definition-rule))))

(property T1>T2-dlv-helper-2 (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (^
   ;; contracts
   (< i (len (tbf-data ([+] ttbf))))
   (<= (length (tdg-pld (nth i (tbf-data ([+] ttbf)))))
       (tbf-bkt ([+] ttbf)))
   ;; thm
   (== (tbf-data ([+] (list (tbf-fwd (car ttbf) i)
			    (cadr ttbf))))
       (tbf-data (tbf-fwd ([+] ttbf) i))))
  :hints (("Goal" :in-theory (enable tbf-fwd-definition-rule
				     remove-ith-definition-rule
				     [+]-definition-rule)
	   :use ((:instance tdgs-nth-pld-app
			    (tdgs0 (tbf-data (car ttbf)))
			    (tdgs1 (tbf-data (cadr ttbf)))
			    (del (tbf-del (cadr ttbf))))
		 (:instance remove-ith-incr-ttl-commute
			    (tdgs (tbf-data (car ttbf)))
			    (del (tbf-del (cadr ttbf))))
		 (:instance remove-prefix
			    (ps0 (incr-ttl (tbf-data (car ttbf))
					   (tbf-del (cadr ttbf))))
			    (ps1 (tbf-data (cadr ttbf))))))))

(property T1>T2-dlv (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (t1-dlv-witness ttbf i)
  :hints (("Goal" :use ((:instance t1-dlv-witness-definition-rule)
			(:instance ~=-definition-rule
                                  (t1 ([+] (list (tbf-fwd (car ttbf) i)
                                                 (cadr ttbf))))
                                  (t2 (tbf-fwd ([+] ttbf) i)))
			(:instance t1>t2-dlv-helper-2)
			(:instance t1>t2-dlv-helper-1)))))

;; If (T1 |> T2) does a delivery in T1, but nothing in T2, this is
;; equivalent to (T1 [+] T2) doing a delivery (to loss).
(property (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (tbf-bkt (car ttbf)) (tbf-bkt (cadr ttbf))))
  (t1-dlv-witness ttbf i)
  :hints (("Goal" :use (:instance T1>T2-dlv))))

(propertyd tdgs-nth-pld-app-2 (tdgs0 tdgs1 :tdgs i :nat del :nat-ord)
	   :h (< i (len tdgs1))
	   (== (tdg-pld (nth (+ (len tdgs0) i) (append (incr-ttl tdgs0 del) tdgs1)))
	       (tdg-pld (nth i tdgs1)))
	   :hints (("Goal" :in-theory (enable incr-ttl-definition-rule))))

(property [+]-dlv-2-body-contracts (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (cadr ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	    (tbf-bkt (cadr ttbf))))
  (^ (< (+ (len (tbf-data (car ttbf))) i)
	(len (tbf-data ([+] ttbf))))
     (tbfp (cadr ttbf))
     (= (tbf-bkt (cadr ttbf)) (tbf-bkt ([+] ttbf)))
     (<= (length (tdg-pld (nth (+ i (len (tbf-data (car ttbf))))
			    (tbf-data ([+] ttbf)))))
	 (tbf-bkt ([+] ttbf)))
     (two-tbfp (list (car ttbf)
		     (tbf-fwd (cadr ttbf) i)))
     (recordp (cadr ttbf)))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     incr-ttl-definition-rule)
	   :use (:instance tdgs-nth-pld-app-2
			   (tdgs0 (tbf-data (car ttbf)))
			   (tdgs1 (tbf-data (cadr ttbf)))
			   (del (tbf-del (cadr ttbf)))))))

(definecd t2-dlv-witness (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (cadr ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	     (tbf-bkt (cadr ttbf))))
  (~= ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i)))
      (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i)))
  :body-contracts-hints (("Goal" :use (:instance [+]-dlv-2-body-contracts))))

(propertyd t2-dlv-witness-helper-1-contracts (ttbf :two-tbf i :nat)
	   :h (^ (< i (len (tbf-data (cadr ttbf))))
		 (<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
		     (tbf-bkt (cadr ttbf))))
	   (^ (< (+ (len (tbf-data (car ttbf))) i)
		 (len (tbf-data ([+] ttbf))))
	      (tbfp (cadr ttbf))
	      (<= (length (tdg-pld (nth (+ (len (tbf-data (car ttbf))) i)
					(tbf-data ([+] ttbf)))))
		  (tbf-bkt ([+] ttbf)))
	      (tbfp (cadr ttbf))
	      (tlp (tbf-data (cadr ttbf)))
	      (rationalp (tbf-bkt (cadr ttbf)))
	      (tdgp (nth i (tbf-data (cadr ttbf))))
	      (stringp (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	      (acl2-numberp (tbf-b-cap (tbf-fwd ([+] ttbf)
						(+ (len (tbf-data (car ttbf))) i))))
	      (two-tbfp (list (car ttbf) (tbf-fwd (cadr ttbf) i)))
	      (acl2-numberp (tbf-d-cap (tbf-fwd ([+] ttbf)
						(+ (len (tbf-data (car ttbf))) i))))
	      (acl2-numberp (tbf-rat (tbf-fwd ([+] ttbf)
					      (+ (len (tbf-data (car ttbf))) i))))
	      (tbfp (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i))))
	   :instructions
	   (:pro
	    (:use (:instance [+]-definition-rule))
	    :pro
	    (:claim (< (+ (len (tbf-data (car ttbf))) i)
		       (len (tbf-data ([+] ttbf)))))
	    (:claim (tbfp (cadr ttbf)))
	    (:claim (<= (length (tdg-pld (nth (+ (len (tbf-data (car ttbf))) i)
					      (tbf-data ([+] ttbf)))))
			(tbf-bkt ([+] ttbf))))
	    (:claim (tlp (tbf-data (cadr ttbf))))
	    (:claim (rationalp (tbf-bkt (cadr ttbf))))
	    (:claim (tdgp (nth i (tbf-data (cadr ttbf)))))
	    (:claim (stringp (tdg-pld (nth i (tbf-data (cadr ttbf))))))
	    (:claim
	     (acl2-numberp (tbf-b-cap (tbf-fwd ([+] ttbf)
					       (+ (len (tbf-data (car ttbf))) i)))))
	    (:claim (two-tbfp (list (car ttbf)
				    (tbf-fwd (cadr ttbf) i))))
	    (:claim
	     (acl2-numberp (tbf-rat (tbf-fwd ([+] ttbf)
					     (+ (len (tbf-data (car ttbf))) i)))))
	    :s))


(property t2-dlv-witness-helper-1 (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (cadr ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	    (tbf-bkt (cadr ttbf))))
  (^
   ;; contracts
   (< (+ (len (tbf-data (car ttbf))) i)
      (len (tbf-data ([+] ttbf))))
   (tbfp (cadr ttbf))
   (<= (length (tdg-pld (nth (+ (len (tbf-data (car ttbf))) i)
			     (tbf-data ([+] ttbf)))))
       (tbf-bkt ([+] ttbf)))
   (tbfp (cadr ttbf))
   (tlp (tbf-data (cadr ttbf)))
   (rationalp (tbf-bkt (cadr ttbf)))
   (tdgp (nth i (tbf-data (cadr ttbf))))
   (stringp (tdg-pld (nth i (tbf-data (cadr ttbf)))))
   (acl2-numberp (tbf-b-cap (tbf-fwd ([+] ttbf)
				     (+ (len (tbf-data (car ttbf))) i))))
   (two-tbfp (list (car ttbf) (tbf-fwd (cadr ttbf) i)))
   (acl2-numberp (tbf-d-cap (tbf-fwd ([+] ttbf)
				     (+ (len (tbf-data (car ttbf))) i))))
   (acl2-numberp (tbf-rat (tbf-fwd ([+] ttbf)
				   (+ (len (tbf-data (car ttbf))) i))))
   (tbfp (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i)))
   ;; actual theorem
   (= (tbf-b-cap ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i))))
      (tbf-b-cap (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i))))
   (= (tbf-d-cap ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i))))
      (tbf-d-cap (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i))))
   (= (tbf-rat ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i))))
      (tbf-rat (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i))))
   (== (tbf-del ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i))))
       (tbf-del (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i)))))
  :instructions ((:use (:instance t2-dlv-witness-helper-1-contracts))
		 (:use (:instance tbf-fwd-definition-rule
                                  (tbf (cadr ttbf))))
                 (:use (:instance tbf-fwd-definition-rule (tbf ([+] ttbf))
                                  (i (+ (len (tbf-data (car ttbf))) i))))
                 (:use (:instance [+]-definition-rule))
                 (:use (:instance [+]-definition-rule
                                  (ttbf (list (car ttbf)
                                              (tbf-fwd (cadr ttbf) i)))))
                 :prove))

(property t2-dlv-witness-helper-2 (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (cadr ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (cadr ttbf)))))
	    (tbf-bkt (cadr ttbf))))
  (^
   ;; contracts
   (< (+ (len (tbf-data (car ttbf))) i)
      (len (tbf-data ([+] ttbf))))
   (tbfp (cadr ttbf))
   (<= (length (tdg-pld (nth (+ (len (tbf-data (car ttbf))) i)
			     (tbf-data ([+] ttbf)))))
       (tbf-bkt ([+] ttbf)))
   (tbfp (cadr ttbf))
   (tlp (tbf-data (cadr ttbf)))
   (rationalp (tbf-bkt (cadr ttbf)))
   (tdgp (nth i (tbf-data (cadr ttbf))))
   (stringp (tdg-pld (nth i (tbf-data (cadr ttbf)))))
   (acl2-numberp (tbf-b-cap (tbf-fwd ([+] ttbf)
				     (+ (len (tbf-data (car ttbf))) i))))
   (two-tbfp (list (car ttbf) (tbf-fwd (cadr ttbf) i)))
   (acl2-numberp (tbf-d-cap (tbf-fwd ([+] ttbf)
				     (+ (len (tbf-data (car ttbf))) i))))
   (acl2-numberp (tbf-rat (tbf-fwd ([+] ttbf)
				   (+ (len (tbf-data (car ttbf))) i))))
   (tbfp (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i)))
   ;; actual theorem
   (== (tbf-data ([+] (list (car ttbf) (tbf-fwd (cadr ttbf) i))))
       (tbf-data (tbf-fwd ([+] ttbf) (+ (len (tbf-data (car ttbf))) i)))))
  :instructions ((:use (:instance t2-dlv-witness-helper-1-contracts))
		 (:use (:instance remove-postfix
                                  (ps0 (incr-ttl (tbf-data (car ttbf))
                                                 (tbf-del (cadr ttbf))))
                                  (ps1 (tbf-data (cadr ttbf)))))
                 :pro
                 (:use (:instance [+]-definition-rule))
                 (:use (:instance [+]-definition-rule
                                  (ttbf (list (car ttbf)
                                              (tbf-fwd (cadr ttbf) i)))))
                 (:use (:instance tbf-fwd-definition-rule (tbf ([+] ttbf))
                                  (i (+ (len (tbf-data (car ttbf))) i))))
                 (:use (:instance tbf-fwd-definition-rule
                                  (tbf (cadr ttbf))))
                 :prove))

;; If (T1 |> T2) does a delivery in T2, but nothing in T1, this is
;; equivalent to (T1 [+] T2) doing a delivery (which might or might not
;; be a loss depending on whether or not any endpoint synchronizes with
;; the delivery event).
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

;; If (T1 |> T2) does a delivery in T1 and a matching transmission in T2,
;; this is equivalent to a noop.  We can prove this by defining permutations.
(check= (count 1 '(1 2 1 2)) 2)
(check= (count 2 '(1 2 1 2)) 2)
(check= (count 3 '(1 2 1 2)) 0)

(property decrement-count-nth (ps :tl i :nat)
  :h (< i (len ps))
  (= (count (nth i ps) ps)
      (1+ (count (nth i ps) (remove-ith ps i))))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property decrement-count-other (ps :tl i :nat p :all)
  :h (^ (< i (len ps)) (!= (nth i ps) p))
  (= (count p ps) (count p (remove-ith ps i)))
  :hints (("Goal" :in-theory (enable remove-ith-definition-rule))))

(property increment-count-nth (ps :tl p :all)
  (= (1+ (count p ps)) (count p (cons p ps))))

(property increment-count-other (ps :tl p0 p1 :all)
  :h (!= p0 p1)
  (= (count p1 ps) (count p1 (cons p0 ps))))

(property count-app (p :all ps0 ps1 :tl)
  (= (+ (count p ps0) (count p ps1))
     (count p (append ps0 ps1))))

(in-theory (disable decrement-count-nth
		    decrement-count-other
		    increment-count-nth
		    increment-count-other
		    count-app))

(property mv-is-a-permutation (ps0 ps1 :tl i :nat p :all)
  :h (< i (len ps0))
  (= (count p (append (remove-ith ps0 i)
		      (cons (nth i ps0) ps1)))
     (count p (append ps0 ps1)))
  :hints
  (("Goal":use ((:instance count-app)
		(:instance count-app (ps0 (remove-ith ps0 i))
			   (ps1 (cons (nth i ps0) ps1)))
		(:instance decrement-count-nth (ps ps0))
		(:instance decrement-count-other (ps ps0))
		(:instance increment-count-nth (ps ps1) (p (nth i ps0)))
		(:instance increment-count-other (ps ps1) (p0 (nth i ps0)) (p1 p)))
    :cases ((= p (nth i ps0))))))

#|
Future work - prove equivalence with perm library ...

(include-book :dir :system "perm")

(property (ps0 ps1 :poss p :pos)
  :h (not-a-permutation p ps0 ps1)
  (! (perm ps0 ps1)))
|#
(definecd v= (tdgs0 tdgs1 :tdgs) :bool
  :ic (= (len tdgs0) (len tdgs1))
  (match tdgs0
    (() t)
    ((tdg . rst) (^ (= (tdg-id tdg) (tdg-id (car tdgs1)))
		    (v= rst (cdr tdgs1))))))

(definecd swap-dgs-inner (tdgs0 tdgs1 :tdgs i :nat) :tdgs
  :ic (< i (len tdgs0))
  (append (remove-ith tdgs0 i)
	  (cons (nth i tdgs0) tdgs1)))

(property swap-dgs-inner-len (tdgs0 tdgs1 :tdgs i :nat)
  :h (< i (len tdgs0))
  (= (len (swap-dgs-inner tdgs0 tdgs1 i))
     (+ (len tdgs0) (len tdgs1)))
  :hints (("Goal" :in-theory (enable swap-dgs-inner-definition-rule))))

(definecd swap-dgs (ttbf :two-tbf i :nat) :tdgs
  :ic (< i (len (tbf-data (car ttbf))))
  (swap-dgs-inner (tbf-data (car ttbf))
		  (tbf-data (cadr ttbf))
		  i))

(property swap-dgs-len (ttbf :two-tbf i :nat)
  :h (< i (len (tbf-data (car ttbf))))
  (= (len (swap-dgs ttbf i)) (len (tbf-data ([+] ttbf))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     swap-dgs-definition-rule))))

(property ~=/mvd-i-v-contracts (ttbf0 ttbf1 :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf0))))
	(= (len (tbf-data ([+] ttbf1)))
	   (len (tbf-data ([+] ttbf0)))))
  (= (len (tbf-data ([+] ttbf1)))
     (len (swap-dgs ttbf0 i)))
  :hints (("Goal" :in-theory (enable [+]-definition-rule))))

;; Say that they're equivalent modulo the move if they're equivalent
;; except for the fact that we moved the nth element from one data queue
;; to the other.  We can do this explicitly, since we just proved that
;; this operation does, indeed, constitute a permutation.
(definecd ~=/mvd-i (ttbf0 ttbf1 :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (car ttbf0))))
	 (= (len (tbf-data ([+] ttbf1)))
	    (len (tbf-data ([+] ttbf0)))))
  (^ (= (tbf-d-cap ([+] ttbf0)) (tbf-d-cap ([+] ttbf1)))
     (= (tbf-b-cap ([+] ttbf0)) (tbf-b-cap ([+] ttbf1)))
     (= (tbf-rat ([+] ttbf0)) (tbf-rat ([+] ttbf1)))
     (== (tbf-del ([+] ttbf0)) (tbf-del ([+] ttbf1)))
     (v= (tbf-data ([+] ttbf1))
	 (swap-dgs ttbf0 i)))
  :body-contracts-hints (("Goal" :use (:instance ~=/mvd-i-v-contracts))))

(property nth-dg-is-record (ttbf :two-tbf i :nat)
  :h (< i (len (tbf-data (car ttbf))))
  (recordp (nth i (tbf-data (car ttbf))))
  :instructions (:pro (:claim (tdgsp (tbf-data (car ttbf)))) :prove))

(property nth-val-is-pos (ttbf :two-tbf i :nat)
  :h (< i (len (mget :data (car ttbf))))
  (posp (tdg-id (nth i (tbf-data (car ttbf)))))
  :instructions (:pro (:claim (tdgsp (tbf-data (car ttbf)))) :prove))

(property contracts-lem (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (= (len (tbf-data ([+] (list (tbf-fwd (car ttbf) i)
			       (tbf-prc (cadr ttbf)
					(tdg-id (nth i (tbf-data (car ttbf))))
					(tdg-pld (nth i (tbf-data (car ttbf)))))))))
     (len (tbf-data ([+] ttbf))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     sz-definition-rule
				     tbf-fwd-definition-rule
				     tbf-prc-definition-rule))))

(definecd mv-tbf-0 (ttbf :two-tbf i :nat) :tbf
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf))))
  (tbf-fwd (car ttbf) i)
  :body-contracts-hints (("Goal" :in-theory (enable tbf-fwd-definition-rule
						    sz-definition-rule)
			  :use (:instance remove-ith-decreases-sz
					  (tdgs (tbf-data (car ttbf)))))))

(propertyd mv-tbf-1-body-contracts (ttbf :two-tbf i :nat)
  :h (< i (len (tbf-data (car ttbf))))
  (^ (tbfp (cadr ttbf))
     (tdgp (nth i (tbf-data (car ttbf))))
     (posp (tdg-id (nth i (tbf-data (car ttbf)))))
     (stringp (tdg-pld (nth i (tbf-data (car ttbf)))))))

(definecd mv-tbf-1 (ttbf :two-tbf i :nat) :tbf
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (tbf-prc (cadr ttbf)
	   (tdg-id (nth i (tbf-data (car ttbf))))
	   (tdg-pld (nth i (tbf-data (car ttbf)))))
  :body-contracts-hints (("Goal" :use (:instance mv-tbf-1-body-contracts))))

(definecd mv-ttbf (ttbf :two-tbf i :nat) :two-tbf
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (list (mv-tbf-0 ttbf i)
	(mv-tbf-1 ttbf i)))

(propertyd contracts-lem-2a (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (< i (len (tbf-data (car ttbf)))))

(propertyd contracts-lem-2b (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (= (len (tbf-data ([+] (mv-ttbf ttbf i))))
     (len (tbf-data ([+] ttbf))))
  :hints (("Goal" :use ((:instance contracts-lem)
			(:instance [+]-definition-rule)
			(:instance [+]-definition-rule (ttbf (mv-ttbf ttbf i)))
			(:instance mv-ttbf-definition-rule)
			(:instance mv-tbf-0-definition-rule)
			(:instance mv-tbf-1-definition-rule)))))

(definecd mv-lem-witness (ttbf :two-tbf i :nat) :bool
  :timeout 40000
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (~=/mvd-i ttbf (mv-ttbf ttbf i) i)
  :body-contracts-hints (("Goal" :use ((:instance contracts-lem-2a)
				       (:instance contracts-lem-2b)))))

(property v=-dgs-reduction (dgs0 dgs1 :tdgs dg :tdg ttl :nat-ord)
  (v= (append (incr-ttl dgs0 ttl) (cons (tdg (tdg-id dg) ttl (tdg-pld dg)) dgs1))
      (append dgs0 (cons dg dgs1)))
  :hints (("Goal" :in-theory (enable v=-definition-rule
				     incr-ttl-definition-rule))))

(property mv-lem-1 (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (^ (= (tbf-d-cap ([+] ttbf))
	(tbf-d-cap ([+] (mv-ttbf ttbf i))))
     (= (tbf-b-cap ([+] ttbf))
	(tbf-b-cap ([+] (mv-ttbf ttbf i))))
     (= (tbf-rat ([+] ttbf))
	(tbf-rat ([+] (mv-ttbf ttbf i)))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     mv-ttbf-definition-rule
				     mv-tbf-0-definition-rule
				     mv-tbf-1-definition-rule
				     tbf-prc-definition-rule
				     remove-ith-definition-rule
				     tbf-fwd-definition-rule))))

(property mv-lem-2 (ttbf :two-tbf i :nat)
  :proof-timeout 100000 
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (== (tbf-del ([+] ttbf))
      (tbf-del ([+] (mv-ttbf ttbf i))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule
				     mv-ttbf-definition-rule
				     mv-tbf-0-definition-rule
				     mv-tbf-1-definition-rule
				     tbf-prc-definition-rule
				     remove-ith-definition-rule
				     tbf-fwd-definition-rule))))

(definecd mv-lem-3-helper (ttbf :two-tbf i :nat) :bool
  :ic (^ (< i (len (tbf-data (car ttbf))))
	 (<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	     (tbf-bkt (car ttbf)))
	 (<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	     (tbf-d-cap (cadr ttbf))))
  (v= (tbf-data ([+] (mv-ttbf ttbf i)))
      (swap-dgs ttbf i))
  :body-contracts-hints (("Goal" :use (:instance contracts-lem-2b))))

(property mv-lem-3 (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (mv-lem-3-helper ttbf i)
  :hints (("Goal" :in-theory (enable mv-lem-3-helper-definition-rule
				     mv-lem-witness-definition-rule
				     ~=/mvd-i-definition-rule
				     [+]-definition-rule
				     mv-ttbf-definition-rule
				     mv-tbf-0-definition-rule
				     mv-tbf-1-definition-rule
				     tbf-fwd-definition-rule
				     tbf-prc-definition-rule
				     swap-dgs-definition-rule
				     swap-dgs-inner-definition-rule)
	   :use ((:instance contracts-lem-2a)
		 (:instance contracts-lem-2b)
		 (:instance v=-dgs-reduction
			    (dgs0 (remove-ith (tbf-data (car ttbf)) i))
			    (dgs1 (tbf-data (cadr ttbf)))
			    (ttl (tbf-del (cadr (mv-ttbf ttbf i))))
			    (dg (nth i (tbf-data (car ttbf)))))))))

;; There is one important difference, which we highlight right here.
;; Namely, stuff in the second queue cannot go "back" to the first one.
;; Why would this matter?  Well, what if we have the second queue have size 1,
;; and the first have size 2.  Now consider this scenario.
;; [a _ _][_] = [a _ _ _]
;; [b a _][_] = [b a _ _]
;; [c b a][_] = [c b a _]
;; Now I try to insert d.  There is no way to insert it on the left
;; and then deliver it, because in order to make room for it, I need to
;; move c, b, or a into the second queue.
;; However, on the right I could insert it and then immediately deliver it.
;; Thus, the equivalence does NOT capture scenarios where messages are
;; reordered by swaps of the form (i, j) where i < j (WLOG), i < len(t1),
;; and j >= len(t1).  In other words, t1 [+] t2 has _strictly more_ behaviors
;; than t1 |> t2.
(property mv-theorem (ttbf :two-tbf i :nat)
  :h (^ (< i (len (tbf-data (car ttbf))))
	(<= (length (tdg-pld (nth i (tbf-data (car ttbf)))))
	    (tbf-bkt (car ttbf)))
	(<= (+ (sz (tbf-data (cadr ttbf))) (length (tdg-pld (nth i (tbf-data (car ttbf))))))
	    (tbf-d-cap (cadr ttbf))))
  (mv-lem-witness ttbf i)
  :instructions ((:use (:instance mv-lem-witness-definition-rule))
                 :pro
                 (:use (:instance mv-lem-3-helper-definition-rule))
                 (:use (:instance mv-lem-3))
                 (:use (:instance mv-lem-2))
                 (:use (:instance mv-lem-1))
                 (:use (:instance ~=/mvd-i-definition-rule (ttbf0 ttbf)
                                  (ttbf1 (mv-ttbf ttbf i))))
                 :pro (:use (:instance contracts-lem-2b))
                 :pro
                 (:claim (= (len (tbf-data ([+] (mv-ttbf ttbf i))))
                            (len (tbf-data ([+] ttbf)))))
                 (:drop 1)
                 (:claim (and (= (tbf-d-cap ([+] ttbf))
                                 (tbf-d-cap ([+] (mv-ttbf ttbf i))))
                              (= (tbf-b-cap ([+] ttbf))
                                 (tbf-b-cap ([+] (mv-ttbf ttbf i))))
                              (= (tbf-rat ([+] ttbf))
                                 (tbf-rat ([+] (mv-ttbf ttbf i))))))
                 (:drop 2)
                 (:claim (equal (tbf-del ([+] ttbf))
                                (tbf-del ([+] (mv-ttbf ttbf i)))))
                 (:drop 2)
                 (:claim (v= (tbf-data ([+] (mv-ttbf ttbf i)))
                             (swap-dgs ttbf i)))
                 (:drop 2 3)
                 (:claim (and (two-tbfp ttbf)
                              (two-tbfp (mv-ttbf ttbf i))
                              (natp i)
                              (< i (len (tbf-data (car ttbf))))
                              (= (len (tbf-data ([+] (mv-ttbf ttbf i))))
                                 (len (tbf-data ([+] ttbf))))))
                 (:claim (equal (~=/mvd-i ttbf (mv-ttbf ttbf i) i)
                                (and (= (tbf-d-cap ([+] ttbf))
                                        (tbf-d-cap ([+] (mv-ttbf ttbf i))))
                                     (= (tbf-b-cap ([+] ttbf))
                                        (tbf-b-cap ([+] (mv-ttbf ttbf i))))
                                     (= (tbf-rat ([+] ttbf))
                                        (tbf-rat ([+] (mv-ttbf ttbf i))))
                                     (equal (tbf-del ([+] ttbf))
                                            (tbf-del ([+] (mv-ttbf ttbf i))))
                                     (v= (tbf-data ([+] (mv-ttbf ttbf i)))
                                         (swap-dgs ttbf i)))))
                 (:drop 1)
                 :prove))

;; Here is where we begin reasoning about scenarios where we can guarantee
;; a datagram will not expire while in-transit.
(definecd all-nz (dgs :tdgs) :bool
  (match dgs
    (() t)
    ((dg . rst) (^ (!= 0 (tdg-del dg)) (all-nz rst)))))

(property all-nz->age-all-len=len (dgs :tdgs)
  :h (all-nz dgs)
  (= (len (age-all dgs)) (len dgs))
  :hints (("Goal" :in-theory (enable all-nz-definition-rule
				     age-all-definition-rule))))

(property all-nz->age-all->dgs->poss= (dgs :tdgs)
  :h (all-nz dgs)
  (== (tdgs->poss (age-all dgs)) (tdgs->poss dgs))
  :hints (("Goal" :in-theory (enable tdgs->poss-definition-rule
				     |MAP*-*(LAMBDA (D) (TDG-ID D))|
				     age-all-definition-rule
				     all-nz-definition-rule))))

(property all-nz->tbf-tick->dgs->poss= (tbf :tbf)
  :h (all-nz (tbf-data tbf))
  (== (tdgs->poss (tbf-data (tbf-tick tbf))) (tdgs->poss (tbf-data tbf)))
  :hints (("Goal" :in-theory (enable tbf-tick-definition-rule
				     tbf-age-definition-rule))))

(property data-helper-for-tick-1 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (== (tdgs->poss (tbf-data ([+] ttbf)))
      (tdgs->poss (tbf-data ([+] (list (tbf-tick (car ttbf)) (cadr ttbf))))))
  :hints (("Goal":in-theory (enable [+]-definition-rule)
	   :use ((:instance tdgs->poss-app
			    (tdgs0 (incr-ttl (tbf-data (car (list (tbf-tick (car ttbf))
								 (cadr ttbf))))
					    (tbf-del (cadr (list (tbf-tick (car ttbf))
								 (cadr ttbf))))))
			    (tdgs1 (tbf-data (cadr (list (tbf-tick (car ttbf))
							(cadr ttbf))))))
		 (:instance all-nz->tbf-tick->dgs->poss=
			    (tbf (car ttbf)))))))

;; If (T1 |> T2) does a tick in T1, this is equivalent to a noop, provided nothing disappears.
(property tick-t1 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (~= ([+] ttbf) ([+] (list (tbf-tick (car ttbf)) (cadr ttbf))))
  :hints (("Goal" :in-theory (enable |MAP*-*(LAMBDA (D) (TDG-ID D))|
				     ~=-definition-rule
				     [+]-definition-rule
				     tbf-tick-definition-rule
				     tbf-age-definition-rule))))

(property data-helper-for-tick-2 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (== (tdgs->poss (tbf-data ([+] ttbf)))
      (tdgs->poss (tbf-data ([+] (list (car ttbf) (tbf-tick (cadr ttbf)))))))
  :hints (("Goal" :in-theory (enable [+]-definition-rule)
	   :use ((:instance tdgs->poss-app
			    (tdgs0 (incr-ttl (tbf-data (car (list (car ttbf)
								  (tbf-tick (cadr ttbf)))))
					     (tbf-del (cadr (list (car ttbf)
								  (tbf-tick (cadr ttbf)))))))
			    (tdgs1 (tbf-data (cadr (list (car ttbf)
							 (tbf-tick (cadr ttbf)))))))
		 (:instance all-nz->tbf-tick->dgs->poss=
			    (tbf (cadr ttbf)))))))

;; If (T1 |> T2) does a tick in T2, this is equivalent to a noop, provided nothing disappears.
(property tick-t2 (ttbf :two-tbf)
  :h (^ (all-nz (tbf-data (car ttbf)))
	(all-nz (tbf-data (cadr ttbf))))
  (~= ([+] ttbf) ([+] (list (car ttbf) (tbf-tick (cadr ttbf)))))
  :hints (("Goal" :in-theory (enable ~=-definition-rule
				     [+]-definition-rule
				     tbf-tick-definition-rule
				     tbf-age-definition-rule))))
