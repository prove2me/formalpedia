-- Prove2me | solution 1 for lean_workbook_plus_38702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:55.095705+00:00
-- url     : https://prove2.me/submissions/77fe279a-1c66-4761-9add-bc90c123b394

import Mathlib.Analysis.Complex.Basic

theorem solution (α : ℝ) (x y : ℝ) (hα : 0 < α ∧ α < 1) :
  α * |x| + (1 - α) * |y| ≥ |α * x + (1 - α) * y| := by
  obtain ⟨h0, h1⟩ := hα
  have h1' : (0:ℝ) < 1 - α := by linarith
  rw [ge_iff_le]
  calc |α * x + (1 - α) * y| ≤ |α * x| + |(1 - α) * y| := abs_add_le _ _
    _ = α * |x| + (1 - α) * |y| := by
        rw [abs_mul, abs_mul, abs_of_pos h0, abs_of_pos h1']
