-- Prove2me | solution 1 for mme_log_interval_of_exact_rational_series_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:15:18.450603+00:00
-- url     : https://prove2.me/submissions/f2b3175d-390e-454f-b4ed-51f5b48b4377

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

private theorem log_two_interval :
    (69314718055 / 100000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718057 / 100000000000 : ℝ) := by
  have hL := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  have hU := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  rw [show (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = 2 by norm_num] at hL hU
  have hlo : (69314718055 / 100000000000 : ℝ) ≤
      2 * ∑ i ∈ range 12, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [sum_range_succ]
  have hhi : 2 * ((∑ i ∈ range 12, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) +
      (1 / 3 : ℝ) ^ (2 * 12 + 1) / (1 - (1 / 3 : ℝ) ^ 2)) ≤
        69314718057 / 100000000000 := by
    norm_num [sum_range_succ]
  constructor <;> nlinarith

/-- All certificate hypotheses are exact rational inequalities or equalities. -/
theorem solution
    (q t lo hi : ℚ) (k n : ℕ)
    (hq : 0 < q) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hscale : q * 2 ^ k = (1 + t) / (1 - t))
    (hlo : lo + k * (69314718057 / 100000000000 : ℚ) ≤
      2 * ∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1))
    (hhi : 2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
      t ^ (2 * n + 1) / (1 - t ^ 2)) -
      k * (69314718055 / 100000000000 : ℚ) ≤ hi) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have ht1R : (t : ℝ) < 1 := by exact_mod_cast ht1
  have hscaleR : (q : ℝ) * 2 ^ k = (1 + (t : ℝ)) / (1 - (t : ℝ)) := by
    exact_mod_cast hscale
  have hsumCast :
      ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1) : ℚ) : ℝ) =
        ∑ i ∈ range n, (t : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    push_cast
    rfl
  have hloR : (lo : ℝ) + (k : ℝ) * (69314718057 / 100000000000 : ℝ) ≤
      2 * ∑ i ∈ range n, (t : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hlo
    push_cast only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] at h
    rw [hsumCast] at h
    norm_num at h ⊢
    exact h
  have hhiR : 2 * ((∑ i ∈ range n, (t : ℝ) ^ (2 * i + 1) / (2 * i + 1)) +
      (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) -
      (k : ℝ) * (69314718055 / 100000000000 : ℝ) ≤ (hi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhi
    push_cast only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_natCast] at h
    rw [hsumCast] at h
    norm_num at h ⊢
    exact h
  have hL := Real.sum_range_le_log_div ht0R ht1R n
  have hU := Real.log_div_le_sum_range_add ht0R ht1R n
  rw [← hscaleR, Real.log_mul hqR.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne',
    Real.log_pow] at hL hU
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htwoL := mul_le_mul_of_nonneg_left log_two_interval.1 hk
  have htwoU := mul_le_mul_of_nonneg_left log_two_interval.2 hk
  constructor <;> linarith
