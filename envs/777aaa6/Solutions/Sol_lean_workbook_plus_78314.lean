-- Prove2me | solution 1 for lean_workbook_plus_78314
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:33.524333+00:00
-- url     : https://prove2.me/submissions/3125bc7c-6844-454e-9939-01727704e9b1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b : ℝ) (hab : b ≠ 0)
    (h : (a / b - 1 / 2) * (a / b - 2) ≤ 0) :
    a^2 / b^2 + 1 ≤ 5 * a / (2 * b) := by
  have hr : 5*a/(2*b) = (5/2)*(a/b) := by field_simp <;> ring
  rw [← div_pow, hr]
  nlinarith only [h]
