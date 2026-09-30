-- Prove2me | solution 1 for lean_workbook_plus_14517
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:57.576763+00:00
-- url     : https://prove2.me/submissions/0c0caf99-a486-4d67-a617-f721f7cff66a

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x a : ℝ, (x = x * a ∧ a < 1) → x = 0 := by
  intro x a ⟨h, ha⟩
  have h1 : x * (1 - a) = 0 := by
    rw [mul_sub, mul_one]
    linarith
  rcases mul_eq_zero.mp h1 with hx | h2
  · exact hx
  · exfalso
    linarith
