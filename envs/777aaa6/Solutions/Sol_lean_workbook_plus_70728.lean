-- Prove2me | solution 1 for lean_workbook_plus_70728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:46.928564+00:00
-- url     : https://prove2.me/submissions/87001f2d-08b0-48ee-9eb5-a5f8adf93160

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (h₁ : a < b ∧ b < c ∧ c < d) :
    (a + b + c + d) ^ 2 - 8 * (a * c + b * d) > 0 := by
  have hda : a < d := h₁.1.trans (h₁.2.1.trans h₁.2.2)
  have hprod := mul_pos (sub_pos.mpr h₁.2.1) (sub_pos.mpr hda)
  nlinarith [sq_nonneg (b + c - a - d)]

#print axioms solution
