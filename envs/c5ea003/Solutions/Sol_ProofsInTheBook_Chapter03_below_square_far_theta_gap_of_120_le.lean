-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.below_square_far_theta_gap_of_120_le
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:23.660364+00:00
-- url     : https://prove2.me/submissions/40540c4f-a91e-46d1-a4d2-d9376bad34e4

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

theorem log2_lt_1733_2500 : Real.log 2 < (1733 : ℝ) / 2500 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_1733_1250 : Real.log 4 < (1733 : ℝ) / 1250 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_1733_2500]

theorem log4_gt_69_50 : (69 : ℝ) / 50 < Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]

theorem log16_gt_69_25 : (69 : ℝ) / 25 < Real.log 16 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]

theorem log64_lt_21_5 : Real.log 64 < (21 : ℝ) / 5 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]

theorem log_le_div64_add_16_5_of_120_le {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k ≤ (k : ℝ) / 64 + (16 : ℝ) / 5 := by
  have hkpos : 0 < k := by omega
  have hdivpos : 0 < (k : ℝ) / 64 := by positivity
  have hlogdiv := Real.log_le_sub_one_of_pos (x := (k : ℝ) / 64) hdivpos
  rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
    (by norm_num : (64 : ℝ) ≠ 0)] at hlogdiv
  nlinarith [log64_lt_21_5]

theorem large_k_stirling_tail_lt_div32 {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k / 2 + (6 : ℝ) / 5 < (k : ℝ) / 32 := by
  have hlog := log_le_div64_add_16_5_of_120_le hk120
  have hkreal : (120 : ℝ) ≤ k := by exact_mod_cast hk120
  nlinarith

theorem log6_gt_8_5 : (8 : ℝ) / 5 < Real.log 6 := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul]
    all_goals norm_num
  nlinarith

theorem stirling_correction_ge_neg_log_k_sub_six_fifths
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    - Real.log k / 2 - (6 : ℝ) / 5 ≤
      Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub (le_of_lt hklt)
  have hnkpos_real : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
    rw [← hcast_sub]
    exact_mod_cast hnkpos
  have hnk_le_n_real : (n : ℝ) - (k : ℝ) ≤ (n : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    linarith
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log hnkpos_real hnk_le_n_real
  have htwopi : (6 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlog6_le : Real.log 6 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) htwopi.le
  nlinarith [log6_gt_8_5, hlog6_le]

theorem entropyTerm_eq_mul_entropyRatio
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k =
      (k : ℝ) * (((n : ℝ) / (k : ℝ)) * Real.log ((n : ℝ) / (k : ℝ))
        - ((n : ℝ) / (k : ℝ) - 1) * Real.log ((n : ℝ) / (k : ℝ) - 1)) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnkpos_real_nat : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnkpos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos_real
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos_real
  have hnk_ne : ((n - k : ℕ) : ℝ) ≠ 0 := ne_of_gt hnkpos_real_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
  have hratio_sub :
      (n : ℝ) / (k : ℝ) - 1 = ((n - k : ℕ) : ℝ) / (k : ℝ) := by
    rw [hcast_sub]
    field_simp [hk_ne]
  unfold entropyTerm
  rw [Real.log_div hn_ne hk_ne, hratio_sub, Real.log_div hnk_ne hk_ne]
  rw [hcast_sub]
  field_simp [hk_ne]
  ring

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

theorem two_mul_sub_one_div_add_one_le_log {x : ℝ} (hx1 : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  by_cases hx : x = 1
  · subst x
    norm_num
  have hxgt : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hx)
  let u : ℝ := (x - 1) / (x + 1)
  have hdenpos : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := by
    exact div_nonneg (by linarith) hdenpos.le
  have hu1 : u < 1 := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    rw [div_lt_one hdenpos]
    linarith
  have hsum := Real.sum_range_le_log_div hu0 hu1 1
  norm_num at hsum
  have hratio : (1 + u) / (1 - u) = x := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    field_simp [hdenpos.ne']
    ring
  rw [hratio] at hsum
  have hleft : 2 * (x - 1) / (x + 1) = 2 * u := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    ring
  rw [hleft]
  nlinarith

theorem two_div_two_mul_sub_one_le_log_div_sub_one {x : ℝ} (hx : 1 < x) :
    2 / (2 * x - 1) ≤ Real.log (x / (x - 1)) := by
  have hy1 : 1 ≤ x / (x - 1) := by
    have hden : 0 < x - 1 := by linarith
    rw [one_le_div hden]
    linarith
  have h := two_mul_sub_one_div_add_one_le_log hy1
  have hden : 0 < x - 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  convert h using 1
  field_simp [hden.ne', hden2.ne']
  ring

theorem entropyRatio_lower_log_add_two_div
    {x : ℝ} (hx : 1 < x) :
    Real.log x + (x - 1) * (2 / (2 * x - 1)) ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hratio := two_div_two_mul_sub_one_le_log_div_sub_one hx
  have hmul :
      (x - 1) * (2 / (2 * x - 1)) ≤
        (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  linarith

theorem sqrt_div_mul_log_mul_le_of_120_le
    {K x : ℝ} (hK : 120 ≤ K) (hx : 2 ≤ x) :
    Real.sqrt (x / K) * Real.log (K * x) ≤
      Real.sqrt (x / 120) * Real.log (120 * x) := by
  have hxpos : 0 < x := by linarith
  have hKpos : 0 < K := by linarith
  have h120pos : (0 : ℝ) < 120 := by norm_num
  have hz0 : Real.exp 2 ≤ 120 * x := by
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    nlinarith
  have hzK : Real.exp 2 ≤ K * x := by
    have hle : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
    exact hz0.trans hle
  have hKx : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
  have hanti := Real.log_div_sqrt_antitoneOn hz0 hzK hKx
  have hscale :
      x * (Real.log (K * x) / Real.sqrt (K * x)) ≤
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) :=
    mul_le_mul_of_nonneg_left hanti hxpos.le
  have hleft :
      Real.sqrt (x / K) * Real.log (K * x) =
        x * (Real.log (K * x) / Real.sqrt (K * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hKpos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hKpos)]
    rw [Real.sq_sqrt hxpos.le]
  have hright :
      Real.sqrt (x / 120) * Real.log (120 * x) =
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul h120pos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos h120pos)]
    rw [Real.sq_sqrt hxpos.le]
  rw [hleft, hright]
  exact hscale

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

theorem nat_sqrt_div_le_sqrt_ratio {n k : ℕ} (hkpos : 0 < k) :
    ((sqrt n : ℕ) : ℝ) / (k : ℝ) ≤
      Real.sqrt (((n : ℝ) / (k : ℝ)) / (k : ℝ)) := by
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnonneg : 0 ≤ ((sqrt n : ℕ) : ℝ) / (k : ℝ) := by positivity
  have harg_nonneg : 0 ≤ ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by positivity
  have hsqrt_sq_nat : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
  have hsqrt_sq_real : (((sqrt n : ℕ) : ℝ) / (k : ℝ)) ^ 2 ≤
      ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by
    have hcast : (((sqrt n : ℕ) : ℝ) ^ 2) ≤ (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hsqrt_sq_nat
    field_simp [ne_of_gt hkpos_real]
    nlinarith
  exact (Real.le_sqrt hnonneg harg_nonneg).mpr hsqrt_sq_real

theorem log360_lt_6 : Real.log 360 < (6 : ℝ) := by
  have hfracpos : (0 : ℝ) < 360 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (360 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (360 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log420_lt_31_5 : Real.log 420 < (31 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 420 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (420 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (420 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log480_lt_13_2 : Real.log 480 < (13 : ℝ) / 2 := by
  have hfracpos : (0 : ℝ) < 480 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (480 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (480 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log720_lt_20_3 : Real.log 720 < (20 : ℝ) / 3 := by
  have hfracpos : (0 : ℝ) < 720 / 512 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (720 : ℝ) / 512) hfracpos
  rw [Real.log_div (by norm_num : (720 : ℝ) ≠ 0) (by norm_num : (512 : ℝ) ≠ 0)] at hfrac
  have h512 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
  rw [h512] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log1200_lt_15_2 : Real.log 1200 < (15 : ℝ) / 2 := by
  have hfracpos : (0 : ℝ) < 1200 / 1024 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (1200 : ℝ) / 1024) hfracpos
  rw [Real.log_div (by norm_num : (1200 : ℝ) ≠ 0) (by norm_num : (1024 : ℝ) ≠ 0)] at hfrac
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [h1024] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log1920_lt_8 : Real.log 1920 < (8 : ℝ) := by
  have hfracpos : (0 : ℝ) < 1920 / 1024 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (1920 : ℝ) / 1024) hfracpos
  rw [Real.log_div (by norm_num : (1920 : ℝ) ≠ 0) (by norm_num : (1024 : ℝ) ≠ 0)] at hfrac
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [h1024] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log2880_lt_41_5 : Real.log 2880 < (41 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 2880 / 2048 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (2880 : ℝ) / 2048) hfracpos
  rw [Real.log_div (by norm_num : (2880 : ℝ) ≠ 0) (by norm_num : (2048 : ℝ) ≠ 0)] at hfrac
  have h2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  rw [h2048] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log3720_lt_43_5 : Real.log 3720 < (43 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 3720 / 2048 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (3720 : ℝ) / 2048) hfracpos
  rw [Real.log_div (by norm_num : (3720 : ℝ) ≠ 0) (by norm_num : (2048 : ℝ) ≠ 0)] at hfrac
  have h2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  rw [h2048] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem sqrt_log120_mul_le_1_3_of_2_le_of_le_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) / 3 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (1 : ℝ) / 6 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (6 : ℝ) := by
    have hle : 120 * x ≤ (360 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log360_lt_6.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_8_of_3_le_of_le_7_2 {x : ℝ}
    (hx3 : 3 ≤ x) (hx7 : x ≤ (7 : ℝ) / 2) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 8 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (7 : ℝ) / 40 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 7 / 40)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (31 : ℝ) / 5 := by
    have hle : 120 * x ≤ (420 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log420_lt_31_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_2_5_of_7_2_le_of_le_4 {x : ℝ}
    (hx7 : (7 : ℝ) / 2 ≤ x) (hx4 : x ≤ 4) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (2 : ℝ) / 5 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (11 : ℝ) / 60 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (11 : ℝ) / 60)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (13 : ℝ) / 2 := by
    have hle : 120 * x ≤ (480 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log480_lt_13_2.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_1_2_of_4_le_of_le_6 {x : ℝ} (hx4 : 4 ≤ x) (hx6 : x ≤ 6) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (9 : ℝ) / 40 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 40)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (20 : ℝ) / 3 := by
    have hle : 120 * x ≤ (720 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log720_lt_20_3.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_4_of_6_le_of_le_10 {x : ℝ} (hx6 : 6 ≤ x) (hx10 : x ≤ 10) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 4 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (3 : ℝ) / 10 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 10)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (15 : ℝ) / 2 := by
    have hle : 120 * x ≤ (1200 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log1200_lt_15_2.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_1_of_10_le_of_le_16 {x : ℝ} (hx10 : 10 ≤ x) (hx16 : x ≤ 16) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (3 : ℝ) / 8 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 8)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (8 : ℝ) := by
    have hle : 120 * x ≤ (1920 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log1920_lt_8.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_5_4_of_16_le_of_le_24 {x : ℝ} (hx16 : 16 ≤ x) (hx24 : x ≤ 24) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (5 : ℝ) / 4 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (9 : ℝ) / 20 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 20)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (41 : ℝ) / 5 := by
    have hle : 120 * x ≤ (2880 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log2880_lt_41_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_2_of_24_le_of_le_31 {x : ℝ} (hx24 : 24 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (13 : ℝ) / 25 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (43 : ℝ) / 5 := by
    have hle : 120 * x ≤ (3720 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log3720_lt_43_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem far_core_aux_2_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    (1 : ℝ) / 32 + x / 3 * ((1733 : ℝ) / 1250) + (1 : ℝ) / 3 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht0 : 0 ≤ x - 2 := by linarith
  have ht1 : 0 ≤ 3 - x := by linarith
  have hp :
      0 ≤ -55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ) := by
    have h0 : 0 ≤ (24021 : ℝ) * (3 - x) ^ 3 := by positivity
    have h1 : 0 ≤ (3 : ℝ) * 68844 * (x - 2) * (3 - x) ^ 2 := by positivity
    have h2 : 0 ≤ (3 : ℝ) * 98929 * (x - 2) ^ 2 * (3 - x) := by positivity
    have h3 : 0 ≤ (58820 : ℝ) * (x - 2) ^ 3 := by positivity
    have hid :
        -55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ) =
          24021 * (3 - x) ^ 3 + 3 * 68844 * (x - 2) * (3 - x) ^ 2
            + 3 * 98929 * (x - 2) ^ 2 * (3 - x) + 58820 * (x - 2) ^ 3 := by
      ring
    rw [hid]
    positivity
  have hdenpos : 0 < (60000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ (-55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ)) /
        ((60000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg hp hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + x / 3 * ((1733 : ℝ) / 1250) + (1 : ℝ) / 3)
      =
      (-55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ)) /
        ((60000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem far_core_aux_3_7_2 {x : ℝ} (hx3 : 3 ≤ x) (_hx7 : x ≤ (7 : ℝ) / 2) :
    (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 8 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht : 0 ≤ x - 3 := by linarith
  have hp : 0 ≤ (16098 : ℝ) * x ^ 2 - 51951 * x + 11951 := by
    have hid : (16098 : ℝ) * x ^ 2 - 51951 * x + 11951 =
        16098 * (x - 3) ^ 2 + 44637 * (x - 3) + 980 := by ring
    rw [hid]
    positivity
  have hdenpos : 0 < (20000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ (3 * ((16098 : ℝ) * x ^ 2 - 51951 * x + 11951)) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg (by positivity) hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 8)
      =
      (3 * ((16098 : ℝ) * x ^ 2 - 51951 * x + 11951)) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem far_core_aux_7_2_4 {x : ℝ} (hx7 : (7 : ℝ) / 2 ≤ x) (_hx4 : x ≤ 4) :
    (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (2 : ℝ) / 5 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht : 0 ≤ x - (7 : ℝ) / 2 := by linarith
  have hp : 0 ≤ (47294 : ℝ) * x ^ 2 - 156353 * x + 36353 := by
    have hid : (47294 : ℝ) * x ^ 2 - 156353 * x + 36353 =
        47294 * (x - (7 : ℝ) / 2) ^ 2 + 174705 * (x - (7 : ℝ) / 2) + 68469 := by
      ring
    rw [hid]
    positivity
  have hdenpos : 0 < (20000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ ((47294 : ℝ) * x ^ 2 - 156353 * x + 36353) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg hp hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (2 : ℝ) / 5)
      =
      ((47294 : ℝ) * x ^ 2 - 156353 * x + 36353) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem below_square_B_core_2_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_3_of_2_le_of_le_3 hx2 hx3
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ x / 3 * ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ (x / 3) * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_right 1 (x / 3)) hlog4_nonneg
      _ ≤ (x / 3) * ((1733 : ℝ) / 1250) := by
        exact mul_le_mul_of_nonneg_left log4_lt_1733_1250.le (by nlinarith)
  have haux := far_core_aux_2_3 hx2 hx3
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_3_7_2 {x : ℝ} (hx3 : 3 ≤ x) (hx7 : x ≤ (7 : ℝ) / 2) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_8_of_3_le_of_le_7_2 hx3 hx7
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by
        nlinarith [log4_lt_1733_1250]
  have haux := far_core_aux_3_7_2 hx3 hx7
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_7_2_4 {x : ℝ} (hx7 : (7 : ℝ) / 2 ≤ x) (hx4 : x ≤ 4) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_2_5_of_7_2_le_of_le_4 hx7 hx4
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by
        nlinarith [log4_lt_1733_1250]
  have haux := far_core_aux_7_2_4 hx7 hx4
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_4_6 {x : ℝ} (hx4 : 4 ≤ x) (hx6 : x ≤ 6) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_2_of_4_le_of_le_6 hx4 hx6
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 50 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx4
    nlinarith [hlelog, log4_gt_69_50]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (1 : ℝ) / 2
      ≤ (69 : ℝ) / 50 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 4 := by
      exact one_div_le_one_div_of_le (by norm_num) hx4
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_6_10 {x : ℝ} (hx6 : 6 ≤ x) (hx10 : x ≤ 10) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_4_of_6_le_of_le_10 hx6 hx10
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (8 : ℝ) / 5 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hx6
    nlinarith [hlelog, log6_gt_8_5]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 4
      ≤ (8 : ℝ) / 5 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 6 := by
      exact one_div_le_one_div_of_le (by norm_num) hx6
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_10_16 {x : ℝ} (hx10 : 10 ≤ x) (hx16 : x ≤ 16) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_of_10_le_of_le_16 hx10 hx16
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (8 : ℝ) / 5 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by linarith : (6 : ℝ) ≤ x)
    nlinarith [hlelog, log6_gt_8_5]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (1 : ℝ)
      ≤ (8 : ℝ) / 5 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 10 := by
      exact one_div_le_one_div_of_le (by norm_num) hx10
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_16_24 {x : ℝ} (hx16 : 16 ≤ x) (hx24 : x ≤ 24) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_5_4_of_16_le_of_le_24 hx16 hx24
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hx16
    nlinarith [hlelog, log16_gt_69_25]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (5 : ℝ) / 4
      ≤ (69 : ℝ) / 25 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 16 := by
      exact one_div_le_one_div_of_le (by norm_num) hx16
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_24_31 {x : ℝ} (hx24 : 24 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_2_of_24_le_of_le_31 hx24 hx31
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : (16 : ℝ) ≤ x)
    nlinarith [hlelog, log16_gt_69_25]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 2
      ≤ (69 : ℝ) / 25 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 24 := by
      exact one_div_le_one_div_of_le (by norm_num) hx24
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_compact {x : ℝ} (hx2 : 2 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  by_cases hx3 : x ≤ 3
  · exact below_square_B_core_2_3 hx2 hx3
  · have hx3' : 3 ≤ x := by linarith
    by_cases hx7 : x ≤ (7 : ℝ) / 2
    · exact below_square_B_core_3_7_2 hx3' hx7
    · have hx7' : (7 : ℝ) / 2 ≤ x := by linarith
      by_cases hx4 : x ≤ 4
      · exact below_square_B_core_7_2_4 hx7' hx4
      · have hx4' : 4 ≤ x := by linarith
        by_cases hx6 : x ≤ 6
        · exact below_square_B_core_4_6 hx4' hx6
        · have hx6' : 6 ≤ x := by linarith
          by_cases hx10 : x ≤ 10
          · exact below_square_B_core_6_10 hx6' hx10
          · have hx10' : 10 ≤ x := by linarith
            by_cases hx16 : x ≤ 16
            · exact below_square_B_core_10_16 hx10' hx16
            · have hx16' : 16 ≤ x := by linarith
              by_cases hx24 : x ≤ 24
              · exact below_square_B_core_16_24 hx16' hx24
              · have hx24' : 24 ≤ x := by linarith
                exact below_square_B_core_24_31 hx24' hx31

theorem below_square_B_core_large {K x : ℝ}
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

theorem below_square_B_core {K x : ℝ}
    (hK120 : 120 ≤ K) (hx2 : 2 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  by_cases hx31 : x ≤ 31
  · have hmono :=
      sqrt_div_mul_log_mul_le_of_120_le (K := K) (x := x) hK120 hx2
    have hmono_div :
        Real.sqrt (x / K) / 3 * Real.log (K * x)
          ≤ Real.sqrt (x / 120) / 3 * Real.log (120 * x) := by
      have h3 : (0 : ℝ) ≤ 3 := by norm_num
      have h := div_le_div_of_nonneg_right hmono h3
      convert h using 1 <;> ring
    have hcompact := below_square_B_core_compact hx2 hx31
    linarith
  · have hx31' : 31 ≤ x := by linarith
    exact below_square_B_core_large hK120 hx31' hxhi


























































































































































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
    {n k : ℕ} (hk120 : 120 ≤ k) (hn2k : 2 * k ≤ n)
    (_hnsq : n < k * k) (hfar : 2 * sqrt n < min k (n / 3)) :
    ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) <
      entropyTerm n k
        + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by
  let x : ℝ := (n : ℝ) / (k : ℝ)
  let M : ℕ := min k (n / 3)
  have hkpos : 0 < k := by omega
  have hklt : k < n := by omega
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hkneR : (k : ℝ) ≠ 0 := ne_of_gt hkposR
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx2 : 2 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hkposR]
    exact_mod_cast hn2k
  have hfar_k : 2 * sqrt n < k :=
    lt_of_lt_of_le hfar (min_le_left k (n / 3))
  have hxhi : x ≤ (k : ℝ) / 4 + 1 := by
    have hroot : (n : ℝ) < ((sqrt n : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt' n
      exact_mod_cast h
    have h2root : 2 * ((sqrt n : ℝ) + 1) ≤ (k : ℝ) + 1 := by
      exact_mod_cast (by omega : 2 * (sqrt n + 1) ≤ k + 1)
    have hsquare :
        ((sqrt n : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((k : ℝ) + 1 - 2 * ((sqrt n : ℝ) + 1))]
    have hn_bound : (n : ℝ) ≤ ((k : ℝ) / 4 + 1) * (k : ℝ) := by
      have hn_bound0 : (n : ℝ) ≤ ((k : ℝ) + 1) ^ 2 / 4 :=
        le_trans hroot.le hsquare
      nlinarith [hkposR]
    dsimp [x]
    exact (div_le_iff₀ hkposR).mpr hn_bound
  have hlogkx_eq : Real.log ((k : ℝ) * x) = Real.log n := by
    congr 1
    dsimp [x]
    field_simp [hkneR]
  have hlogkx_nonneg : 0 ≤ Real.log ((k : ℝ) * x) := by
    rw [hlogkx_eq]
    exact Real.log_nonneg hn_ge_one
  have hsqrt_ratio := nat_sqrt_div_le_sqrt_ratio (n := n) (k := k) hkpos
  have hsqrt_term :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        ≤ (k : ℝ) * (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)) := by
    have hcoeff_nonneg : 0 ≤ (k : ℝ) * Real.log ((k : ℝ) * x) / 3 := by
      have hmul : 0 ≤ (k : ℝ) * Real.log ((k : ℝ) * x) :=
        mul_nonneg hkposR.le hlogkx_nonneg
      nlinarith
    calc
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          = (((sqrt n : ℕ) : ℝ) / (k : ℝ))
              * ((k : ℝ) * Real.log ((k : ℝ) * x) / 3) := by
              rw [hlogkx_eq]
              field_simp [hkneR]
      _ ≤ Real.sqrt (x / (k : ℝ)) * ((k : ℝ) * Real.log ((k : ℝ) * x) / 3) := by
              exact mul_le_mul_of_nonneg_right hsqrt_ratio hcoeff_nonneg
      _ = (k : ℝ) * (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)) := by
              ring
  have hM_le_k : M ≤ k := min_le_left k (n / 3)
  have hM_le_n_div3 : M * 3 ≤ n := by
    have hM : M ≤ n / 3 := min_le_right k (n / 3)
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hM
  have hMratio_left : ((M : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hkposR]
    have hMk : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hM_le_k
    nlinarith
  have hMratio_right : ((M : ℕ) : ℝ) / (k : ℝ) ≤ x / 3 := by
    rw [div_le_iff₀ hkposR]
    have hMreal : (M : ℝ) ≤ (n : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      exact_mod_cast hM_le_n_div3
    have hxmul : x / 3 * (k : ℝ) = (n : ℝ) / 3 := by
      dsimp [x]
      field_simp [hkneR]
    nlinarith
  have hMratio : ((M : ℕ) : ℝ) / (k : ℝ) ≤ min 1 (x / 3) :=
    le_min hMratio_left hMratio_right
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hM_term :
      ((M : ℕ) : ℝ) * Real.log 4
        ≤ (k : ℝ) * (min 1 (x / 3) * Real.log 4) := by
    calc
      ((M : ℕ) : ℝ) * Real.log 4
          = (((M : ℕ) : ℝ) / (k : ℝ)) * ((k : ℝ) * Real.log 4) := by
              field_simp [hkneR]
      _ ≤ min 1 (x / 3) * ((k : ℝ) * Real.log 4) := by
              exact mul_le_mul_of_nonneg_right hMratio (mul_nonneg hkposR.le hlog4_nonneg)
      _ = (k : ℝ) * (min 1 (x / 3) * Real.log 4) := by
              ring
  have hcore := below_square_B_core (K := (k : ℝ)) (x := x)
    (by exact_mod_cast hk120) hx2 hxhi
  have hentropy_core :
      (k : ℝ) *
        (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)
          + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32)
        ≤ entropyTerm n k := by
    have hmul := mul_le_mul_of_nonneg_left hcore hkposR.le
    rw [entropyTerm_eq_mul_entropyRatio (n := n) (k := k) hkpos hklt]
    exact hmul
  have hupper_plus :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((M : ℕ) : ℝ) * Real.log 4 + (k : ℝ) / 32
        ≤ entropyTerm n k := by
    have hsum :
        ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
            + ((M : ℕ) : ℝ) * Real.log 4 + (k : ℝ) / 32
          ≤ (k : ℝ) *
            (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)
              + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32) := by
      nlinarith [hsqrt_term, hM_term]
    exact hsum.trans hentropy_core
  have htail := large_k_stirling_tail_lt_div32 hk120
  have hcorr := stirling_correction_ge_neg_log_k_sub_six_fifths (n := n) (k := k) hkpos hklt
  have htheta_nonneg : 0 ≤ Chebyshev.theta ((sqrt n : ℕ) : ℝ) :=
    Chebyshev.theta_nonneg _
  dsimp [M] at hupper_plus
  nlinarith
