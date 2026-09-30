-- Prove2me | solution 1 for lean_workbook_plus_54147
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:39.773103+00:00
-- url     : https://prove2.me/submissions/0676b896-ecce-440d-a1ab-e1232755ba74

import Mathlib.Analysis.Complex.Basic

theorem solution (M x: ℝ) (g : ℝ → ℝ) (h₁ : |g x - M| < |M| / 2) : |g x| > |M| / 2 := by
  have h2 : |M| - |g x| ≤ |g x - M| := by
    have := abs_sub_abs_le_abs_sub M (g x)
    rw [abs_sub_comm] at this
    exact this
  linarith
