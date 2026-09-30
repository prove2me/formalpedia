-- Prove2me | solution 1 for lean_workbook_plus_78228
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:02.878694+00:00
-- url     : https://prove2.me/submissions/b44c70b8-f65e-46da-ac95-a29323e1b3e0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a ^ 2 + 1)⁻¹ + (b ^ 2 + 1)⁻¹ ≥ 2 / (1 + a * b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 1 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have ha2 : 0 < a ^ 2 + 1 := by positivity
  have hb2 : 0 < b ^ 2 + 1 := by positivity
  have hd : 0 < 1 + a * b := by positivity
  have hid : (a ^ 2 + 1)⁻¹ + (b ^ 2 + 1)⁻¹ - 2 / (1 + a * b) =
      (a * b - 1) * (a - b) ^ 2 / ((a ^ 2 + 1) * (b ^ 2 + 1) * (1 + a * b)) := by
    field_simp [ne_of_gt ha2, ne_of_gt hb2, ne_of_gt hd] <;> ring
  have hn : 0 ≤ (a * b - 1) * (a - b) ^ 2 /
      ((a ^ 2 + 1) * (b ^ 2 + 1) * (1 + a * b)) :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
  linarith

#print axioms solution
