-- Prove2me | solution 1 for lean_workbook_plus_59352
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:21.194651+00:00
-- url     : https://prove2.me/submissions/b60f9eb7-81a7-4a27-89a3-8bb0441d7a50

import Mathlib.Analysis.Complex.Basic

theorem solution (ε : ℝ) : ∃ δ : ℝ, ∀ x : ℝ, |x - 2| < δ → |x ^ 2 - 4| < ε := by
  refine ⟨min 1 (ε / 5), fun x hx => ?_⟩
  have h1 : |x - 2| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - 2| < ε / 5 := lt_of_lt_of_le hx (min_le_right _ _)
  have h3 : |x + 2| ≤ 5 := by
    have : x + 2 = (x - 2) + 4 := by ring
    rw [this]
    calc |(x - 2) + 4| ≤ |x - 2| + |(4:ℝ)| := abs_add_le _ _
      _ ≤ 1 + 4 := by
        have : |(4:ℝ)| = 4 := abs_of_pos (by norm_num)
        rw [this]; linarith
      _ = 5 := by norm_num
  have h4 : x ^ 2 - 4 = (x - 2) * (x + 2) := by ring
  rw [h4, abs_mul]
  calc |x - 2| * |x + 2| ≤ |x - 2| * 5 := by
        apply mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ < ε / 5 * 5 := by
        apply mul_lt_mul_of_pos_right h2 (by norm_num)
    _ = ε := by ring
