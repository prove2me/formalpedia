-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_close_of_sqrt33
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:48.528417+00:00
-- url     : https://prove2.me/submissions/24f35eda-729e-4437-818a-3b34882cd53a

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03


/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
-/

namespace ProofsInTheBook.Chapter03

open Nat















theorem primeIntervalProduct_dvd_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ∣ M.choose a := by
  rw [primeIntervalProduct, ← Nat.add_sub_of_le haM]
  exact Finset.prod_primes_dvd _ (fun _ hp => (Finset.mem_filter.1 hp).2.prime) fun p hp => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact hp.2.dvd_choose_add hp.1.1 (hd.trans_lt hp.1.1) hp.1.2

theorem primeIntervalProduct_le_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ≤ M.choose a := by
  exact le_of_dvd (Nat.choose_pos haM) (primeIntervalProduct_dvd_choose haM hd)

theorem log_primeIntervalProduct_le_log_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    Real.log (primeIntervalProduct a M) ≤ Real.log (M.choose a) := by
  exact Real.log_le_log
    (by exact_mod_cast (Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos :
      0 < primeIntervalProduct a M))
    (by exact_mod_cast primeIntervalProduct_le_choose haM hd)

theorem sqrt_le_div_three_of_nine_le {n : ℕ} (hn : 9 ≤ n) : sqrt n ≤ n / 3 := by
  rw [← Nat.lt_succ_iff]
  rw [Nat.sqrt_lt]
  have hq : 3 ≤ n / 3 := by omega
  have hnle : n ≤ 3 * (n / 3) + 2 := by omega
  nlinarith [sq_nonneg ((n / 3 : ℕ) : ℤ)]

theorem sqrt_le_min_of_nine_le_and_lt_sq {n k : ℕ} (hn : 9 ≤ n) (hlt : n < k * k) :
    sqrt n ≤ min k (n / 3) := by
  refine le_min ?_ (sqrt_le_div_three_of_nine_le hn)
  exact (Nat.sqrt_lt.mpr hlt).le

theorem not_hasPrimeFactorAbove_iff_noLargePrimeFactor {k m : ℕ} :
    ¬ HasPrimeFactorAbove k m ↔ NoLargePrimeFactor k m := by
  constructor
  · intro h p hp hpdvd
    by_contra hkp
    exact h ⟨p, by omega, hp, hpdvd⟩
  · rintro h ⟨p, hkp, hp, hpdvd⟩
    exact (not_lt_of_ge (h p hp hpdvd)) hkp

theorem factorization_choose_eq_zero_of_noLargePrimeFactor
    {n k p : ℕ} (hno : NoLargePrimeFactor k (n.choose k)) (hkp : k < p) :
    (n.choose k).factorization p = 0 := by
  by_cases hp : p.Prime
  · by_contra hne
    have hpdvd : p ∣ n.choose k := Nat.dvd_of_factorization_pos hne
    exact (not_lt_of_ge (hno p hp hpdvd)) hkp
  · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hp





theorem choose_factorization_le_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k =
      ∏ p ∈ Finset.range (min k (n / 3) + 1),
        p ^ (n.choose k).factorization p := by
  refine (Eq.trans ?_ (Nat.prod_pow_factorization_choose n k hkn)).symm
  refine Finset.prod_subset ?hsub ?hzero
  · intro p hp
    rw [Finset.mem_range] at hp ⊢
    omega
  · intro p hp_range hp_not_small
    rw [Finset.mem_range] at hp_range hp_not_small
    have hMp : min k (n / 3) < p := by omega
    by_cases hpprime : p.Prime
    · by_cases hkp : k < p
      · rw [factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp, pow_zero]
      · have hpk : p ≤ k := le_of_not_gt hkp
        have hpnk : p ≤ n - k := by omega
        have hp2 : p ≠ 2 := by
          intro hp_eq
          have hnthird : 2 ≤ n / 3 := by omega
          omega
        have hdiv : n / 3 < p := by omega
        have hnlt : n < 3 * p := by
          have := (Nat.div_lt_iff_lt_mul three_pos).mp hdiv
          simpa [mul_comm] using this
        rw [Nat.factorization_choose_of_lt_three_mul hp2 hpk hpnk hnlt, pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]





theorem choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * primeIntervalProduct (sqrt n) (min k (n / 3)) := by
  let M := min k (n / 3)
  let S := {p ∈ Finset.range (M + 1) | Nat.Prime p}
  let f := fun p => p ^ (n.choose k).factorization p
  have hprime_filter : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ hpprime => ?_
    contrapose hpprime
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]
  rw [choose_factorization_le_min_third_of_noLargePrimeFactor hkn hn2k hn6 hno, ← hprime_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ n)).trans ?_
    · exact Nat.pow_factorization_choose_le hnpos
    rw [Finset.prod_const]
    refine pow_right_mono₀ (Nat.succ_le_iff.mpr hnpos) ?_
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card fun p hp => by
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.mpr ⟨hpsqrt, (Finset.mem_filter.1 hpS).2⟩
  · refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 hpS).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 hpsqrt)
    change (∏ p ∈ Finset.filter (fun p => ¬p ≤ sqrt n) S, p) ≤
      ∏ p ∈ Finset.Ioc (sqrt n) M with p.Prime, p
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.1 hpS
      rw [Finset.mem_range] at hpRange
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_not_ge hpsqrt, by omega⟩, hpPrime⟩
    · intro p hp _hnot
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact hp.2.one_lt.le









theorem log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
  let P := primeIntervalProduct (sqrt n) (min k (n / 3))
  have hnat :
      n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * P :=
    choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
      hnpos hkn hn2k hn6 hno
  have hpos_choose_nat : 0 < n.choose k := Nat.choose_pos hkn
  have hPpos : 0 < P := by
    dsimp [P, primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogle :
      Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := by
    exact Real.log_le_log (by exact_mod_cast hpos_choose_nat) (by exact_mod_cast hnat)
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := hlogle
    _ = Real.log ((n : ℝ) ^ Nat.primeCounting (sqrt n) * (P : ℝ)) := by
      norm_num [Nat.cast_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n + Real.log P := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0))
        (by exact_mod_cast hPpos.ne' : (P : ℝ) ≠ 0),
        Real.log_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
      simp [P]

theorem log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log ((min k (n / 3)).choose (sqrt n)) := by
  exact (log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    (n := n) (k := k) hnpos hkn hn2k hn6 hno).trans
      (add_le_add_right (log_primeIntervalProduct_le_log_choose hsqrtM hMsub)
        ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n))

theorem log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  let M := min k (n / 3)
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hchoose_pos : 0 < M.choose (sqrt n) := Nat.choose_pos hsqrtM
  have hchoose_le : M.choose (sqrt n) ≤ 2 ^ M := Nat.choose_le_two_pow M (sqrt n)
  have hlog_choose_le :
      Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := by
    exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hchoose_le)
  exact hupper.trans <| add_le_add_right
    (by
      calc
        Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := hlog_choose_le
        _ = Real.log ((2 : ℝ) ^ M) := by norm_num [Nat.cast_pow]
        _ = (M : ℝ) * Real.log 2 := by rw [Real.log_pow])
    ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n)



theorem log_factorial_le_stirling_upper {m : ℕ} (hm : m ≠ 0) :
    Real.log (m !) ≤ (m : ℝ) * Real.log m - (m : ℝ) + Real.log m / 2 + 1 := by
  have hlogseq : Real.log (Stirling.stirlingSeq m) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact Real.log_le_log (Stirling.stirlingSeq'_pos t)
      (Stirling.stirlingSeq'_antitone (Nat.zero_le t))
  have hformula := Stirling.log_stirlingSeq_formula m
  have hone : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div, Real.log_exp]
    · rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · positivity
    · positivity
  rw [hformula, hone] at hlogseq
  rw [Real.log_mul (x := (2 : ℝ)) (y := (m : ℝ)), Real.log_div, Real.log_exp] at hlogseq
  · nlinarith
  all_goals positivity

theorem entropy_lower_le_log_choose {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k
      + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
      + Real.log (2 * Real.pi) / 2 - 2
      ≤ Real.log (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hrpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hfac_nat := Nat.choose_mul_factorial_mul_factorial hkn
  have hfac : (n.choose k : ℝ) * (k ! : ℝ) * ((n - k)! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hfac_nat
  have hlogfac :
      Real.log (n !) = Real.log (n.choose k) + Real.log (k !) + Real.log ((n - k)!) := by
    rw [← hfac]
    rw [Real.log_mul
        (mul_ne_zero (by exact_mod_cast hchoose_pos.ne') (by exact_mod_cast (Nat.factorial_pos k).ne'))
        (by exact_mod_cast (Nat.factorial_pos (n - k)).ne'),
      Real.log_mul
        (by exact_mod_cast hchoose_pos.ne')
        (by exact_mod_cast (Nat.factorial_pos k).ne')]
  have hN := Stirling.le_log_factorial_stirling (show n ≠ 0 from hnpos.ne')
  have hK := log_factorial_le_stirling_upper (m := k) hkpos.ne'
  have hR := log_factorial_le_stirling_upper (m := n - k) hrpos.ne'
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  rw [hlogfac] at hN
  unfold entropyTerm
  rw [hcast_sub] at hR ⊢
  nlinarith

theorem entropyTerm_lower_basic {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
      + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) ≤ entropyTerm n k := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (hkpos.trans hklt)
  have hrpos_nat : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hrpos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast hrpos_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  have hlog_ratio :=
    Real.log_le_sub_one_of_pos
      (x := ((n - k : ℕ) : ℝ) / (n : ℝ)) (div_pos hrpos hnpos)
  have hdiff :
      (k : ℝ) / (n : ℝ) ≤ Real.log n - Real.log (n - k) := by
    rw [Real.log_div (ne_of_gt hrpos) (ne_of_gt hnpos)] at hlog_ratio
    rw [hcast_sub] at hlog_ratio
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp [hnne] at hlog_ratio ⊢
    nlinarith
  have hmul :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) / (n : ℝ)) ≤
        ((n - k : ℕ) : ℝ) * (Real.log n - Real.log (n - k)) :=
    mul_le_mul_of_nonneg_left hdiff hrpos.le
  unfold entropyTerm
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [hcast_sub] at hmul ⊢
  field_simp [hnne] at hmul ⊢
  nlinarith





























theorem three_mul_primeCounting_le_30_150_cert :
    ∀ k : Fin 150, 33 ≤ k.val → 3 * Nat.primeCounting k.val ≤ k.val := by
  intro k hk33
  rcases le_or_gt k.val 36 with hk36 | hk37
  · have hpi : Nat.primeCounting k.val ≤ 11 := by
      have hmono := Nat.monotone_primeCounting hk36
      have h36 : Nat.primeCounting 36 = 11 := by decide
      exact hmono.trans_eq h36
    omega
  rcases le_or_gt k.val 40 with hk40 | hk41
  · have hpi : Nat.primeCounting k.val ≤ 12 := by
      have hmono := Nat.monotone_primeCounting hk40
      have h40 : Nat.primeCounting 40 = 12 := by decide
      exact hmono.trans_eq h40
    omega
  rcases le_or_gt k.val 42 with hk42 | hk43
  · have hpi : Nat.primeCounting k.val ≤ 13 := by
      have hmono := Nat.monotone_primeCounting hk42
      have h42 : Nat.primeCounting 42 = 13 := by decide
      exact hmono.trans_eq h42
    omega
  rcases le_or_gt k.val 46 with hk46 | hk47
  · have hpi : Nat.primeCounting k.val ≤ 14 := by
      have hmono := Nat.monotone_primeCounting hk46
      have h46 : Nat.primeCounting 46 = 14 := by decide
      exact hmono.trans_eq h46
    omega
  rcases le_or_gt k.val 52 with hk52 | hk53
  · have hpi : Nat.primeCounting k.val ≤ 15 := by
      have hmono := Nat.monotone_primeCounting hk52
      have h52 : Nat.primeCounting 52 = 15 := by decide
      exact hmono.trans_eq h52
    omega
  rcases le_or_gt k.val 60 with hk60 | hk61
  · have hpi : Nat.primeCounting k.val ≤ 17 := by
      have hmono := Nat.monotone_primeCounting hk60
      have h60 : Nat.primeCounting 60 = 17 := by decide
      exact hmono.trans_eq h60
    omega
  rcases le_or_gt k.val 72 with hk72 | hk73
  · have hpi : Nat.primeCounting k.val ≤ 20 := by
      have hmono := Nat.monotone_primeCounting hk72
      have h72 : Nat.primeCounting 72 = 20 := by decide
      exact hmono.trans_eq h72
    omega
  rcases le_or_gt k.val 96 with hk96 | hk97
  · have hpi : Nat.primeCounting k.val ≤ 24 := by
      have hmono := Nat.monotone_primeCounting hk96
      have h96 : Nat.primeCounting 96 = 24 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h96
    omega
  rcases le_or_gt k.val 136 with hk136 | hk137
  · have hpi : Nat.primeCounting k.val ≤ 32 := by
      have hmono := Nat.monotone_primeCounting hk136
      have h136 : Nat.primeCounting 136 = 32 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h136
    omega
  · have hpi : Nat.primeCounting k.val ≤ 35 := by
      have hmono := Nat.monotone_primeCounting k.isLt.le
      have h149 : Nat.primeCounting 149 = 35 := by
        set_option maxRecDepth 10000 in
        decide
      set_option maxRecDepth 10000 in
      exact hmono.trans_eq h149
    omega

theorem three_mul_primeCounting_le_of_33_le {k : ℕ} (hk33 : 33 ≤ k) :
    3 * Nat.primeCounting k ≤ k := by
  by_cases hk150 : k < 150
  · exact three_mul_primeCounting_le_30_150_cert ⟨k, hk150⟩ hk33
  · let m := k - 30
    have hk_eq : k = 30 + m := by omega
    have hbound0 := Nat.primeCounting_add_le
      (a := 30) (k := 30) (n := m) (by norm_num) (by norm_num : 30 ≤ 30)
    have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (m / 30 + 1) := by
      simpa [hk_eq] using hbound0
    have hcalc : Nat.primeCounting 30 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (m / 30 + 1) := by
      simpa [hcalc, htot] using hbound
    have hm120 : 120 ≤ m := by omega
    have hq4 : 4 ≤ m / 30 := by
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).mpr hm120
    have hmul : 30 * (m / 30) ≤ m := Nat.mul_div_le m 30
    omega

theorem log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  exact hupper.trans <|
    add_le_add_left (mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le)
      (((min k (n / 3) : ℕ) : ℝ) * Real.log 2)





theorem min_eq_left_of_sqrt33_close
    {n k : ℕ} (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    min k (n / 3) = k := by
  by_cases hk : k ≤ n / 3
  · exact Nat.min_eq_left hk
  · have hM : min k (n / 3) = n / 3 := Nat.min_eq_right (le_of_not_ge hk)
    have hclose : n / 3 ≤ 2 * sqrt n := by
      omega
    have hnle : n ≤ 3 * (n / 3) + 2 := by omega
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith

theorem close_branch_coef_gap_aux {L N : ℝ} (h10 : 10 * L < N) (hL : L < 1) :
    (2 : ℝ) / 3 < N / 6 - 2 * L + 1 := by
  linarith

theorem close_branch_main_gap_aux {k N L : ℝ} (hk : 34 ≤ k) (hN : N / 2 ≤ k / 6)
    (hc : (2 : ℝ) / 3 < N / 6 - 2 * L + 1) :
    0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6 := by
  have hkpos : 0 < k := by linarith
  have hprod :
      k * ((2 : ℝ) / 3) < k * (N / 6 - 2 * L + 1) :=
    mul_lt_mul_of_pos_left hc hkpos
  nlinarith

theorem close_branch_simple_gap_aux {k N L : ℝ}
    (h : 0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6) :
    k / 3 * N + k * L <
      (k / 2 * N - k * L + k - 4) - N / 2 - 2 := by
  nlinarith

theorem close_branch_shift_aux {A B N : ℝ} (h : A ≤ B) :
    A - N / 2 - 2 ≤ B - N / 2 - 2 := by
  linarith

theorem close_branch_upper_simple_aux {a k M : ℕ} {N L : ℝ}
    (hM : M = k) (ha : a ≤ k) (hN : 0 ≤ N) :
    (a : ℝ) / 3 * N + (M : ℝ) * L ≤ (k : ℝ) / 3 * N + (k : ℝ) * L := by
  subst M
  have ha_real : (a : ℝ) / 3 ≤ (k : ℝ) / 3 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) (by norm_num)
  exact add_le_add_left (mul_le_mul_of_nonneg_right ha_real hN) ((k : ℝ) * L)




























































































































































































































































/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/



/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/











/-!
### Binomial coefficients are (almost) never powers

Erdős's theorem (1951): C(n,k) ≠ m^l for k ≥ 4, n ≥ 2k, l ≥ 2.
Reference: P. Erdős, On a diophantine equation,
J. London Math. Soc. 26 (1951), 176-178.

Below: Step 1 (concentration lemma + n > k²) is complete.
Steps 2–4 are pending (l-th-power-free decomposition, distinctness,
classification {aⱼ}={1,…,k}, and contradiction for l=2, l≥3).
-/

section Tier1

/-! ### Prime-divisibility helpers for Finset products -/





/-! ### Step 1: Concentration lemma → n > k² -/







/-! ### Step 2: l-th-power-free decomposition -/







/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/





























































































/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/



/-! ### Legendre / `padicValNat_factorial` helpers -/













/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open Nat
open ProofsInTheBook.Chapter03
set_option maxHeartbeats 800000

theorem solution
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := by omega
  have hkn : k ≤ n := by omega
  have hklt : k < n := by omega
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hn6 : 6 ≤ n := by
    have hsqrt_le_self : sqrt n ≤ n := Nat.sqrt_le_self n
    omega
  have hn9 : 9 ≤ n := by omega
  have hsqrtM : sqrt n ≤ min k (n / 3) :=
    sqrt_le_min_of_nine_le_and_lt_sq hn9 hnsq
  have hM_eq : min k (n / 3) = k :=
    min_eq_left_of_sqrt33_close hsqrt33 hMsub
  have hsqrt_lt_k : sqrt n < k := Nat.sqrt_lt.mpr hnsq
  have hk34 : 34 ≤ k := by omega
  have hk_le_2sqrt : k ≤ 2 * sqrt n := by
    rw [hM_eq] at hMsub
    omega
  have hksq4 : k * k ≤ 4 * n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hlogn_pos : 0 < Real.log n := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogk_le_logn : Real.log k ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hkn)
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hnkpos) (by exact_mod_cast (by omega : n - k ≤ n))
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) := by
    exact Real.log_nonneg (by nlinarith [Real.one_le_pi_div_two])
  have hcorr_ge :
      - Real.log n / 2 - 2 ≤
        Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2 := by
    nlinarith
  have hlog4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have htwologk_le : 2 * Real.log k ≤ Real.log n + 2 * Real.log 2 := by
    have hlog_sq_le : Real.log ((k : ℝ) ^ 2) ≤ Real.log ((4 : ℝ) * (n : ℝ)) := by
      have hcast : (k : ℝ) ^ 2 ≤ (4 : ℝ) * (n : ℝ) := by
        norm_num [pow_two]
        exact_mod_cast hksq4
      exact Real.log_le_log (sq_pos_of_pos (by exact_mod_cast hkpos)) hcast
    rw [Real.log_pow] at hlog_sq_le
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0), hlog4_eq] at hlog_sq_le
    norm_num at hlog_sq_le
    nlinarith
  have hlogk_le_half : Real.log k ≤ Real.log n / 2 + Real.log 2 := by
    linarith
  have hk_sq_div_le_four : (k : ℝ) ^ 2 / (n : ℝ) ≤ 4 := by
    have hcast : (k : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hksq4
    exact (div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)).mpr (by linarith)
  have hbasic_ge :
      (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4 ≤
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) := by
    have hmul : (k : ℝ) * Real.log k ≤ (k : ℝ) * (Real.log n / 2 + Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogk_le_half (by positivity)
    nlinarith
  have hbasic_ge_shift :
      ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - (2 : ℝ) ≤
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - (2 : ℝ) := by
    exact close_branch_shift_aux hbasic_ge
  have hlog16_lt_four : Real.log (16 : ℝ) < 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hlogk_le_six : Real.log k ≤ (k : ℝ) / 6 := by
    have hdivpos : 0 < (k : ℝ) / 16 := by positivity
    have hdiv :=
      Real.log_le_sub_one_of_pos (x := (k : ℝ) / 16) hdivpos
    rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
      (by norm_num : (16 : ℝ) ≠ 0)] at hdiv
    have haux : Real.log k ≤ (k : ℝ) / 16 + 3 := by
      nlinarith
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    nlinarith
  have hlogn_lt_twologk : Real.log n < 2 * Real.log k := by
    have hlog_lt : Real.log (n : ℝ) < Real.log ((k * k : ℕ) : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hnsq)
    rw [show ((k * k : ℕ) : ℝ) = (k : ℝ) ^ 2 by norm_num [pow_two],
      Real.log_pow] at hlog_lt
    exact hlog_lt
  have hlogn_le_kthird : Real.log n ≤ (k : ℝ) / 3 := by
    linarith only [hlogn_lt_twologk, hlogk_le_six]
  have hlogn_half_le_ksix : Real.log n / 2 ≤ (k : ℝ) / 6 := by
    linarith only [hlogn_le_kthird]
  have hn1024 : 1024 < n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    have h1024 : 1024 < sqrt n * sqrt n := by
      nlinarith only [hsqrt33]
    exact h1024.trans_le hsq
  have hten_log2_lt_logn : 10 * Real.log 2 < Real.log n := by
    have hlog_lt : Real.log (1024 : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log (by norm_num) (by exact_mod_cast hn1024)
    rwa [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hlog_lt
  have hcoef : (2 : ℝ) / 3 < Real.log n / 6 - 2 * Real.log 2 + 1 := by
    exact close_branch_coef_gap_aux hten_log2_lt_logn hlog2_lt_one
  have hmain :
      0 < (k : ℝ) * (Real.log n / 6 - 2 * Real.log 2 + 1)
          - Real.log n / 2 - 6 := by
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    exact close_branch_main_gap_aux hk34r hlogn_half_le_ksix hcoef
  have hsimple_gap :
      (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 <
        ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - 2 := by
    exact close_branch_simple_gap_aux hmain
  have hupper_simple :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 ≤
        (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := by
    exact close_branch_upper_simple_aux
      (a := sqrt n) (k := k) (M := min k (n / 3))
      (N := Real.log n) (L := Real.log 2) hM_eq hsqrt_lt_k.le hlogn_pos.le
  have hbasic := entropyTerm_lower_basic (n := n) (k := k) hkpos hklt
  have hlower_entropy := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  have hlower :
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
        ≤ Real.log (n.choose k) := by
    calc
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
          ≤ entropyTerm n k
            + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
            + Real.log (2 * Real.pi) / 2 - 2 := by
              linarith only [hbasic, hcorr_ge]
      _ ≤ Real.log (n.choose k) := hlower_entropy
  have hupper_lt_lower :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 <
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
    calc
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2
          ≤ (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := hupper_simple
      _ < (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4
            - Real.log n / 2 - 2 := hsimple_gap
      _ ≤ ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
            exact hbasic_ge_shift
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrt33 hsqrtM hMsub
  exact not_lt_of_ge (hlower.trans hupper) hupper_lt_lower
