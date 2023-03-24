(in-package "ACL2S")

;; The first SRTT is the first sample.
;; Each subsequent srtt = (1-alpha)(prior srtt) + (alpha)(cur sample).
(definec paramaterized-new-srtt
  (alpha :pos-rational srtt :pos-rational s :pos-rational) :pos-rational
  :ic (and (< 0 alpha) (< alpha 1))
  (+ (* (- 1 alpha) srtt) (* alpha s)))

(defdata samples (listof pos-rational))

;; R(a,sr,[s0]) = P(a,sr,s0)
;; R(a,sr,[s0,s1,...,sN]) = R(a,P(a,sr,s0),[s1,...,sN])
(definec recurse-srtt (alpha :pos-rational srtt :pos-rational ss :samples) :pos-rational
  :ic (and (< 0 alpha) (< alpha 1) (< 0 (len ss)))
  (let ((srtt0 (paramaterized-new-srtt alpha srtt (car ss))))
    (if (equal (len ss) 1)
	srtt0
      (recurse-srtt alpha srtt0 (cdr ss)))))

;; Next, define the recursive srtt for the case with N consecutive samples.
(definec recurse-srtt-N-cons
  (alpha :pos-rational srtt :pos-rational s :pos-rational N :nat) :pos-rational
  :ic (and (< 0 alpha) (< alpha 1))
  (if (equal N 0) (paramaterized-new-srtt alpha srtt s)
    (recurse-srtt-N-cons
     alpha
     (paramaterized-new-srtt alpha srtt s)
     s
     (1- N))))

(definec all-eq (ss :samples) :bool
  (if (< (len ss) 2) t
    (and (equal (car ss) (cadr ss))
	 (all-eq (cdr ss)))))

(property all-eq-works (ss :samples x :pos-rational y :pos-rational)
  (implies (and (all-eq ss)
		(not (equal x y)))
	   (not (and (in x ss)
		     (in y ss)))))

;; Prove equivalence.
(property recurse-srtt-when-N-cons (alpha :pos-rational srtt :pos-rational ss :samples)
  :hyps (and (< 0 alpha) (< alpha 1) (< 0 (len ss)) (all-eq ss))
  (equal (recurse-srtt alpha srtt ss)
	 (recurse-srtt-N-cons alpha srtt (car ss) (1- (len ss)))))

;; Next we will prove that recurse-srtt-N-cons can be re-written as an alpha summation.
;; To do this we first need to define alpha summations.

;; Define the alpha summation we will use to rewrite the case where there are N
;; identical consecutive samples.
;;     alpha-summation(N, a) = sum_{i=0}^N (1-a)^i (a)
(definec alpha-summation (N :nat alpha :pos-rational) :pos-rational
  :ic (and (< 0 alpha) (< alpha 1))
  (if (equal N 0) alpha
    (+ (* (expt (- 1 alpha) N) alpha)
       (alpha-summation (1- N) alpha))))

;; Prove critical shifting property of the alpha summation:
;;     (1-a)alpha-summation(N, a) + (a) = alpha-summation(N+1, a)
(property shift-alpha-summation (N :nat alpha :pos-rational)
  :hyps (and (< 0 alpha) (< alpha 1))
  (equal (+ (* (- 1 alpha) (alpha-summation N alpha)) alpha)
	 (alpha-summation (1+ N) alpha)))

;; Observe: srttK+1 = (1-a)srtt + (a)s
;;          srttK+2 = (1-a)^2(srtt) + (1-a)(a)s + (a)s
;;          srttK+3 = (1-a)^3(srtt) + (1-a)^2(a)s + (1-a)(a)s + (a)s
;;          ...
;;          srttK+N = (1-a)^N(srtt) + ( sum_{i=0}^{N-1} (1-a)^i (a) ) s

;; Begin with the base case.
(property base-case-unfold-recurse-srtt
  (alpha :pos-rational srtt :pos-rational s :pos-rational)
  :hyps (and (< 0 alpha) (< alpha 1))
  (equal (recurse-srtt-N-cons alpha srtt s 0)
	 (+ (* (expt (- 1 alpha) 1) srtt) (* (alpha-summation 0 alpha) s))))

;; Now for the general case (N arbitrary).
(property unfold-recurse-srtt (alpha :pos-rational srtt :pos-rational s :pos-rational N :nat)
  :hyps (and (< 0 alpha) (< alpha 1))
  (equal (recurse-srtt-N-cons alpha srtt s N)
	 (+ (* (expt (- 1 alpha) (1+ N)) srtt) (* (alpha-summation N alpha) s))))

;; We can further simplify the alpha summation to a closed form (which I discovered
;; using Wolfram Alpha).
(property simplify-alpha-sum (N :nat alpha :pos-rational)
  :hyps (and (< 0 alpha) (< alpha 1))
  (equal (alpha-summation N alpha)
	 (+ (* alpha (expt (- 1 alpha) N))
	    (* -1 (expt (- 1 alpha) N))
	    1))
  :hints (("Goal" :use (:instance shift-alpha-summation (N (- N 1)) (alpha alpha)))))

;; Now we can use this closed form to rewrite the recurse srtt (when samples are identical).
;; This is the Observation we report in the paper.  From this Observation, the limit is
;; immediately obvious, although we do not prove it directly here because ACL2s does not have
;; rationals, which makes epsilon delta proofs exceedingly difficult.
(property further-unfold-recurse-srtt
  (alpha :pos-rational srtt :pos-rational s :pos-rational N :nat)
  :hyps (and (< 0 alpha) (< alpha 1))
  (equal (recurse-srtt-N-cons alpha srtt s N)
	 (+ (* (expt (- 1 alpha) (1+ N)) srtt)
	    (* (+ (* alpha (expt (- 1 alpha) N))
		  (* -1 (expt (- 1 alpha) N))
		  1)
	       s))))

;; Now that we proved something sufficient to get the limit for identical samples
;; [s0 = s1 = ... = sN], let's consider the more general case where all the si fall
;; in some range (a, b) = Br_e(c) = (e - c, e + c).  To handle this case we first
;; need to prove srtt is linear in the sense that increasing input increases output.
;; Once we've proven this, then we need to show it also holds for the recursive case.

;; Prove that s0 <= s1 and srtt0 <= srtt1 -> srtt(srtt0,s0) <= srtt(srtt1,s1)
(property srtt-is-linear
  (srtt0 :pos-rational
	 srtt1 :pos-rational
	 s0 :pos-rational
	 s1 :pos-rational
	 alpha :pos-rational)
  :hyps (and (< 0 alpha) (< alpha 1) (<= s0 s1) (<= srtt0 srtt1))
  (<= (paramaterized-new-srtt alpha srtt0 s0)
      (paramaterized-new-srtt alpha srtt1 s1)))

;; Need a way to show that every element of one list is <= each corresponding
;; element of the other (index-wise comparison ...)
(definec all-<= (ss0 :samples ss1 :samples) :bool
  :ic (equal (len ss0) (len ss1))
  (if (equal (len ss0) 0) t
    (and (<= (car ss0) (car ss1))
	 (all-<= (cdr ss0) (cdr ss1)))))

;; Prove a sanity thm about this.
(property all-<=-works (ss0 :samples ss1 :samples)
  :hyps (and (equal (len ss0) (len ss1))
	     (< 0 (len ss0))
	     (all-<= ss0 ss1))
  (<= (car ss0) (car ss1)))

;; Lemma that nth samples is rational.
(property nth-ss-is-s (ss :samples n :nat)
  :hyps (< n (len ss))
  (pos-rationalp (nth n ss)))

;; Prove another sanity thm about this.
(property all-<=-works-inside (ss0 :samples ss1 :samples n :nat)
  :hyps (and (equal (len ss0) (len ss1))
	     (all-<= ss0 ss1)
	     (< n (len ss0)))
  (<= (nth n ss0) (nth n ss1)))

;; Now we need to prove as much for the recursive case.
;; Let's begin by sketching out a proof.
;; Start with the base case.
(property srtt-rec-is-linear-bc
  (alpha :pos-rational srtt :pos-rational ss0 :samples ss1 :samples)
  :hyps (and (< 0 alpha)
	     (< alpha 1)
	     (equal 1 (len ss0))
	     (equal (len ss0) (len ss1))
	     (all-<= ss0 ss1))
  (<= (recurse-srtt alpha srtt ss0)
      (recurse-srtt alpha srtt ss1)))

;; Now let's think a bit about the inductive step.  Recall:
;; R(a,sr,[s0]) = P(a,sr,s0)
;; R(a,sr,[s0,s1,...,sN]) = R(a,P(a,sr,s0),[s1,...,sN])
;; 
;; Let ss0 = [s0,...,sN] and ss1 = [s0',...,sN'] s.t. for each 0 <= i <= N,
;; si <= si'.  And assume N >= 1.
;;
;; Then R(a,sr,[s0,...,sN]) <= R(a,sr,[s0',...,sN'])
;; <-> R(a,P(a,sr,s0),[s1,...,sN]) <= R(a,P(a,sr,s0'),[s1',...,sN']).
;; So we need an inductor for this.
(property srtt-rec-proof-inductor-contracts
  (alpha :pos-rational
	 srtt0 :pos-rational
	 srtt1 :pos-rational
	 ss0 :samples
	 ss1 :samples)
  :hyps (and (< 0 alpha)
	     (< alpha 1)
	     (< 0 (len ss0))
	     (equal (len ss0) (len ss1)))
  (if (equal (len ss0) 1) (natp 1)
	     (and (pos-rationalp alpha)
		  (pos-rationalp (paramaterized-new-srtt alpha srtt0 (car ss0)))
		  (pos-rationalp (paramaterized-new-srtt alpha srtt1 (car ss1)))
		  (samplesp (cdr ss0))
		  (samplesp (cdr ss1)))))

(definec srtt-rec-proof-inductor
  (alpha :pos-rational
	 srtt0 :pos-rational
	 srtt1 :pos-rational
	 ss0 :samples
	 ss1 :samples) :nat
	 :ic (and (< 0 alpha)
		  (< alpha 1)
		  (< 0 (len ss0))
		  (equal (len ss0) (len ss1)))
	 (if (equal (len ss0) 1) 1
	   (1+ (srtt-rec-proof-inductor
		alpha
		(paramaterized-new-srtt alpha srtt0 (car ss0))
		(paramaterized-new-srtt alpha srtt1 (car ss1))
		(cdr ss0)
		(cdr ss1)))))
    
(defthm
 srtt-rec-is-linear
 (implies (and (pos-rationalp alpha)
               (pos-rationalp srtt0)
               (pos-rationalp srtt1)
               (samplesp ss0)
               (samplesp ss1)
               (< 0 alpha)
               (< alpha 1)
               (< 0 (len ss0))
               (equal (len ss0) (len ss1))
               (all-<= ss0 ss1)
               (<= srtt0 srtt1))
          (<= (recurse-srtt alpha srtt0 ss0)
              (recurse-srtt alpha srtt1 ss1)))
 :instructions
 (:pro
  (:induct (srtt-rec-proof-inductor alpha srtt0 srtt1 ss0 ss1))
  :pro
  (:claim (<= (paramaterized-new-srtt alpha srtt0 (car ss0))
              (paramaterized-new-srtt alpha srtt1 (car ss1))))
  (:claim (<= (recurse-srtt alpha
                            (paramaterized-new-srtt alpha srtt0 (car ss0))
                            (cdr ss0))
              (recurse-srtt alpha
                            (paramaterized-new-srtt alpha srtt1 (car ss1))
                            (cdr ss1))))
  (:drop 3)
  (:use (:instance recurse-srtt-definition-rule
                   (alpha alpha)
                   (srtt srtt0)
                   (ss ss0)))
  :pro
  (:use (:instance recurse-srtt-definition-rule
                   (alpha alpha)
                   (srtt srtt1)
                   (ss ss1)))
  :pro
  (:claim (equal (recurse-srtt alpha srtt1 ss1)
                 (let ((srtt0 (paramaterized-new-srtt alpha srtt1 (car ss1)))
                       (ss ss1))
                      (if (equal (len ss) 1)
                          srtt0
                          (recurse-srtt alpha srtt0 (cdr ss))))))
  (:claim (equal (recurse-srtt alpha srtt0 ss0)
                 (let ((srtt0 (paramaterized-new-srtt alpha srtt0 (car ss0)))
                       (ss ss0))
                      (if (equal (len ss) 1)
                          srtt0
                          (recurse-srtt alpha srtt0 (cdr ss))))))
  (:drop 1 2)
  (:drop 16 17 18 19)
  (:drop 11 12 13 14 15)
  (:claim (equal (recurse-srtt alpha srtt1 ss1)
                 (recurse-srtt alpha
                               (paramaterized-new-srtt alpha srtt1 (car ss1))
                               (cdr ss1))))
  (:claim (equal (recurse-srtt alpha srtt0 ss0)
                 (recurse-srtt alpha
                               (paramaterized-new-srtt alpha srtt0 (car ss0))
                               (cdr ss0))))
  (:drop 15 16)
  :prove
  :pro :prove))

;; Next, I want to argue for a bounded closed form, which gives me the bounded
;; convergence result.

(defthm srtt-bounded-thm
        (implies (and (pos-rationalp alpha)
                      (pos-rationalp srtt)
                      (samplesp ss-bot)
                      (samplesp ss-top)
                      (samplesp ss)
                      (< 0 alpha)
                      (< alpha 1)
                      (equal (len ss-bot) (len ss))
                      (equal (len ss) (len ss-top))
                      (all-eq ss-bot)
                      (all-eq ss-top)
                      (all-<= ss-bot ss)
                      (all-<= ss ss-top)
                      (< 0 (len ss)))
                 (and (<= (recurse-srtt-n-cons alpha srtt (car ss-bot)
                                               (1- (len ss-bot)))
                          (recurse-srtt alpha srtt ss))
                      (<= (recurse-srtt alpha srtt ss)
                          (recurse-srtt-n-cons alpha srtt (car ss-top)
                                               (1- (len ss-top))))))
        :instructions
        (:pro (:claim (equal (recurse-srtt-n-cons alpha srtt (car ss-bot)
                                                  (+ -1 (len ss-bot)))
                             (recurse-srtt alpha srtt ss-bot)))
              (:claim (equal (recurse-srtt-n-cons alpha srtt (car ss-top)
                                                  (+ -1 (len ss-top)))
                             (recurse-srtt alpha srtt ss-top)))
              (:use (:instance srtt-rec-is-linear (alpha alpha)
                               (srtt0 srtt)
                               (srtt1 srtt)
                               (ss0 ss-bot)
                               (ss1 ss)))
              :pro
              (:claim (<= (recurse-srtt alpha srtt ss-bot)
                          (recurse-srtt alpha srtt ss)))
              (:drop 1)
              (:use (:instance srtt-rec-is-linear (alpha alpha)
                               (srtt0 srtt)
                               (srtt1 srtt)
                               (ss0 ss)
                               (ss1 ss-top)))
              :pro
              (:claim (<= (recurse-srtt alpha srtt ss)
                          (recurse-srtt alpha srtt ss-top)))
              (:drop 1)
              :prove))

;; Now, let's take a look at RTTVar.
(definec paramaterized-new-rttvar
  (beta :pos-rational srtt :pos-rational rttvar :pos-rational s :pos-rational) :pos-rational
  :ic (and (< 0 beta) (< beta 1))
  (+ (* (- 1 beta) rttvar)
     (* beta (abs (- srtt s)))))

;; NOTE: The rttvar IS NOT linear in srtt and/or s.

;; Step 1: Show how RTTVar collapses when d(SRTT, S) is upper-bounded.
(property rttvar-collapses-when-d-srtt-s-bounded
  (beta :pos-rational
	srtt :pos-rational
	rttvar :pos-rational
	s :pos-rational
	bnd :pos-rational)
  :hyps (and (< 0 beta)
	     (< beta 1)
	     (<= (abs (- srtt s)) bnd))
  (<= (paramaterized-new-rttvar beta srtt rttvar s)
      (+ (* (- 1 beta) rttvar)
	 (* beta bnd))))


#|
R(1) = (1-b)R(0) + (b)2r
R(2) = (1-b)^2 R(0) + (1-b)(b)2r + (b)2r
R(3) = (1-b)^3 R(0) + (1-b)^2(b)2r + (1-b)(b)2r + (b)2r
R(N) = (1-b)^N R(0) + sum_{i=0}^{N-1} (1-b)^i (b)2r = (1-b)^N R(0) + (1 - (1-b)^n)2r
Lim N->inf R(N) = 0 + 2r
|#
(definec rttvar-right-sum (r :pos-rational N :nat beta :pos-rational) :rational
  :ic (< 0 N)
  (let ((term (* (expt (- 1 beta) (- N 1)) beta 2 r)))
	(if (equal N 1) term
	  (+ term (rttvar-right-sum r (- N 1) beta)))))


(definec rttvar-right-sum-cf (r :pos-rational N :nat beta :pos-rational) :rational
  (* (- 1 (expt (- 1 beta) N)) 2 r))


;; This is basically the final observation.
(property rttvar-right-sum-to-cf (r :pos-rational N :nat beta :pos-rational)
  :hyps (< 0 N)
  (equal (rttvar-right-sum r N beta)
	 (rttvar-right-sum-cf r N beta)))


;; Refine recurse-rttvars to return a LIST of the consecutive RTTVars.
(definec recurse-rttvars
  (beta :pos-rational srtts :samples rttvar0 :pos-rational ss :samples) :samples
  :ic (and (< 0 beta)
		 (< beta 1)
		 (< 0 (len ss))
		 (equal (len ss) (len srtts)))
  (let ((rttvar1 (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))))
    (if (equal (len ss) 1) (list rttvar1)
      (cons rttvar1 (recurse-rttvars beta (cdr srtts) rttvar1 (cdr ss))))))

;; Just to test it.
(recurse-rttvars 1/8 '(12 33 8) 5 '(2 3 4))

(definec sum-square-dels (ss :samples mu :pos-rational) :rational
  :ic (< 0 (len ss))
  (let ((del (expt (- (car ss) mu) 2)))
    (if (equal (len ss) 1) del
      (+ del (sum-square-dels (cdr ss) mu)))))

(definec sum (ss :samples) :pos-rational
  :ic (< 0 (len ss))
  (if (equal (len ss) 1) (car ss)
    (+ (car ss) (sum (cdr ss)))))

(definec mean (ss :samples) :pos-rational
  :ic (< 0 (len ss))
  (/ (sum ss) (len ss)))

(definec sample-variance-squared (ss :samples) :rational
  :ic (< 1 (len ss))
  (/ (sum-square-dels ss (mean ss))
     (- (len ss) 1)))

;; Observation: RTTVar is NOT the statistical variance.
(let* ((ss '(1 44 13))
       (beta 1/4)
       (alpha 1/8)
       (srtt0 1)
       (srtt1 (paramaterized-new-srtt alpha srtt0 (cadr ss)))
       (srtt2 (paramaterized-new-srtt alpha srtt1 (caddr ss)))
       (srtts (list srtt0 srtt1 srtt2))
       (rttvar0 1/2))
  (list (expt (car (last (recurse-rttvars beta srtts rttvar0 ss))) 2)
	(sample-variance-squared ss)))
