-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:20.594149+00:00
-- url     : https://prove2.me/submissions/794633d7-287b-44bd-a097-3b0337b3cb37

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









theorem primorial_eq_mul_primeIntervalProduct {a M : ℕ} (haM : a ≤ M) :
    primorial M = primorial a * primeIntervalProduct a M := by
  rw [primorial, primeIntervalProduct]
  rw [show (Finset.range (M + 1)).filter Nat.Prime =
      (Finset.range (a + 1)).filter Nat.Prime ∪ (Finset.Ioc a M).filter Nat.Prime by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpM, hpprime⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨by omega, hpprime⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hpprime⟩
    · rintro (⟨hpa, hpprime⟩ | ⟨⟨hpa, hpM⟩, hpprime⟩) <;> exact ⟨by omega, hpprime⟩]
  rw [Finset.prod_union]
  · rfl
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
    omega

theorem log_primeIntervalProduct_eq_theta_sub {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) =
      Chebyshev.theta (M : ℝ) - Chebyshev.theta (a : ℝ) := by
  have hprod := primorial_eq_mul_primeIntervalProduct (a := a) (M := M) haM
  have hposA : 0 < (primorial a : ℕ) := primorial_pos a
  have hposP : 0 < primeIntervalProduct a M := by
    dsimp [primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogprod :
      Real.log (primorial M) =
        Real.log (primorial a) + Real.log (primeIntervalProduct a M) := by
    rw [hprod, Nat.cast_mul]
    exact Real.log_mul
      (by exact_mod_cast hposA.ne' : ((primorial a : ℕ) : ℝ) ≠ 0)
      (by exact_mod_cast hposP.ne' : ((primeIntervalProduct a M : ℕ) : ℝ) ≠ 0)
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial]
  norm_num at hlogprod ⊢
  linarith

theorem log_primeIntervalProduct_le_min_third_log4_sub_theta
    {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) ≤
      (M : ℝ) * Real.log 4 - Chebyshev.theta (a : ℝ) := by
  rw [log_primeIntervalProduct_eq_theta_sub haM]
  have hthetaM := Chebyshev.theta_le_log4_mul_x (x := (M : ℝ)) (by positivity)
  linarith













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

theorem solution
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  have hlogP :=
    log_primeIntervalProduct_le_min_third_log4_sub_theta
      (a := sqrt n) (M := min k (n / 3)) hsqrtM
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  have hpc :
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n ≤
        ((sqrt n : ℕ) : ℝ) / 3 * Real.log n :=
    mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le
  linarith
