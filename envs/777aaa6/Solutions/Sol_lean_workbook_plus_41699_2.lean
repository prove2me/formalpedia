-- Prove2me | solution 2 for lean_workbook_plus_41699
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:32:50.272015+00:00
-- url     : https://prove2.me/submissions/c74bf80e-7621-45d0-bbd9-89c84b2bdb3d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h₁ : a ≥ 1) (h₂ : b + c ≤ -1) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3 := by
  have ha : a ^ 3 ≤ a ^ 4 := by
    have h0 : 0 ≤ a ^ 3 * (a - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith [h0]
  -- global lower bound x^4 - x^3 ≥ -27/256
  have key : ∀ x : ℝ, x ^ 3 ≤ x ^ 4 + 27 / 256 := by
    intro x
    nlinarith [mul_nonneg (sq_nonneg (4 * x - 3)) (add_nonneg (sq_nonneg (4 * x + 1)) (by norm_num : (0:ℝ) ≤ 2))]
  -- for x ≤ 0, x^4 ≥ x^3
  have neg : ∀ x : ℝ, x ≤ 0 → x ^ 3 ≤ x ^ 4 := by
    intro x hx
    have h3 : x ^ 3 ≤ 0 := by
      have : x ^ 3 = x * x ^ 2 := by ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg hx (sq_nonneg x)
    have h0 : 0 ≤ x ^ 3 * (x - 1) := mul_nonneg_of_nonpos_of_nonpos h3 (by linarith)
    nlinarith [h0]
  -- for x ≤ -1, x^4 ≥ x^3 + 2
  have negbig : ∀ x : ℝ, x ≤ -1 → x ^ 3 + 2 ≤ x ^ 4 := by
    intro x hx
    have h3 : x ^ 3 ≤ -1 := by
      have hf : x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by ring
      have hq : 0 ≤ x ^ 2 - x + 1 := by nlinarith [sq_nonneg (x - 1/2)]
      have : (x + 1) * (x ^ 2 - x + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
      linarith
    have h0 : 0 ≤ (-1 - x ^ 3) * (1 - x) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h0]
  rcases le_or_gt b 0 with hb | hb
  · rcases le_or_gt c 0 with hc | hc
    · linarith [neg b hb, neg c hc]
    · linarith [negbig b (by linarith), key c]
  · linarith [negbig c (by linarith), key b]
