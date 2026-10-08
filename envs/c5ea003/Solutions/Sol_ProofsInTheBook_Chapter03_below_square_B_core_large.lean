-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.below_square_B_core_large
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:22.057119+00:00
-- url     : https://prove2.me/submissions/413e0a79-6c95-47d4-a5d2-3be3b594ec21

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

















































































































theorem log2_lt_7_10 : Real.log 2 < (7 : ℝ) / 10 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_7_5 : Real.log 4 < (7 : ℝ) / 5 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]







theorem log16_gt_69_25 : (69 : ℝ) / 25 < Real.log 16 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]













theorem entropyRatio_lower_log_add
    {x : ℝ} (hx : 1 < x) :
    Real.log x + 1 - 1 / x ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hypos : 0 < x / (x - 1) := div_pos hxpos hxsubpos
  have hlog := Real.one_sub_inv_le_log_of_pos hypos
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  have hinv_eq : (x / (x - 1))⁻¹ = (x - 1) / x := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos]
  rw [hinv_eq] at hlog
  have hlog' : 1 / x ≤ Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos] at hlog ⊢
    linarith
  have hmul :
      (x - 1) * (1 / x) ≤ (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hlog' (by linarith)
  have hbasic :
      Real.log x + 1 - 1 / x ≤
        Real.log x + (x - 1) * Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos] at hmul ⊢
    nlinarith
  rwa [hrewrite] at hbasic









theorem sqrt_div_mul_log_mul_le_of_base_le
    {K0 K x : ℝ} (hK0pos : 0 < K0) (hK0K : K0 ≤ K) (hxpos : 0 < x)
    (hexp : Real.exp 2 ≤ K0 * x) :
    Real.sqrt (x / K) * Real.log (K * x) ≤
      Real.sqrt (x / K0) * Real.log (K0 * x) := by
  have hKpos : 0 < K := hK0pos.trans_le hK0K
  have hzK : Real.exp 2 ≤ K * x := by
    have hle : K0 * x ≤ K * x := mul_le_mul_of_nonneg_right hK0K hxpos.le
    exact hexp.trans hle
  have hKx : K0 * x ≤ K * x := mul_le_mul_of_nonneg_right hK0K hxpos.le
  have hanti := Real.log_div_sqrt_antitoneOn hexp hzK hKx
  have hscale :
      x * (Real.log (K * x) / Real.sqrt (K * x)) ≤
        x * (Real.log (K0 * x) / Real.sqrt (K0 * x)) :=
    mul_le_mul_of_nonneg_left hanti hxpos.le
  have hleft :
      Real.sqrt (x / K) * Real.log (K * x) =
        x * (Real.log (K * x) / Real.sqrt (K * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hKpos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hKpos)]
    rw [Real.sq_sqrt hxpos.le]
  have hright :
      Real.sqrt (x / K0) * Real.log (K0 * x) =
        x * (Real.log (K0 * x) / Real.sqrt (K0 * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hK0pos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hK0pos)]
    rw [Real.sq_sqrt hxpos.le]
  rw [hleft, hright]
  exact hscale
























































































































































































































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

theorem solution {K x : ℝ}
    (_hK120 : 120 ≤ K) (hx31 : 31 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  let K0 : ℝ := 4 * x - 4
  have hK0pos : 0 < K0 := by
    dsimp [K0]
    linarith
  have hK0K : K0 ≤ K := by
    dsimp [K0]
    linarith
  have hexp : Real.exp 2 ≤ K0 * x := by
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    dsimp [K0]
    nlinarith
  have hmono :=
    sqrt_div_mul_log_mul_le_of_base_le
      (K0 := K0) (K := K) (x := x) hK0pos hK0K hxpos hexp
  have hmono_div :
      Real.sqrt (x / K) / 3 * Real.log (K * x)
        ≤ Real.sqrt (x / K0) / 3 * Real.log (K0 * x) := by
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have h := div_le_div_of_nonneg_right hmono h3
    convert h using 1 <;> ring
  have hsqrt : Real.sqrt (x / K0) ≤ (13 : ℝ) / 25 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)]
    dsimp [K0]
    have hdenpos : 0 < (4 : ℝ) * x - 4 := by nlinarith
    rw [div_le_iff₀ hdenpos]
    nlinarith [hx31]
  have hlogbase :
      Real.log (K0 * x) ≤ Real.log 4 + 2 * Real.log x := by
    have hbasepos : 0 < K0 * x := mul_pos hK0pos hxpos
    have hlearg : K0 * x ≤ 4 * x ^ 2 := by
      dsimp [K0]
      nlinarith
    have hlogle := Real.log_le_log hbasepos hlearg
    have hrewrite : Real.log (4 * x ^ 2) = Real.log 4 + 2 * Real.log x := by
      have hx_ne : x ≠ 0 := ne_of_gt hxpos
      have hx2_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx_ne
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx2_ne, Real.log_pow]
      norm_num
    linarith
  have hlogbase_nonneg : 0 ≤ Real.log (K0 * x) := by
    have hbase_one : (1 : ℝ) ≤ K0 * x := by
      dsimp [K0]
      nlinarith
    exact Real.log_nonneg hbase_one
  have hterm_base :
      Real.sqrt (x / K0) / 3 * Real.log (K0 * x)
        ≤ ((13 : ℝ) / 25) / 3 * (Real.log 4 + 2 * Real.log x) := by
    have hmul := mul_le_mul hsqrt hlogbase hlogbase_nonneg (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)
    nlinarith
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ (7 : ℝ) / 5 := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ (7 : ℝ) / 5 := by nlinarith [log4_lt_7_5]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : (16 : ℝ) ≤ x)
    nlinarith [hlelog, log16_gt_69_25]
  have hinv : 1 / x ≤ (1 : ℝ) / 31 := by
    exact one_div_le_one_div_of_le (by norm_num) hx31
  have haux :
      ((13 : ℝ) / 25) / 3 * (Real.log 4 + 2 * Real.log x) + (7 : ℝ) / 5 + (1 : ℝ) / 32
        ≤ Real.log x + 1 - 1 / x := by
    nlinarith [log4_lt_7_5, hlogx, hinv]
  have hlower := entropyRatio_lower_log_add hx1
  linarith
