-- Prove2me | solution 1 for lean_workbook_plus_40306
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:31:57.989002+00:00
-- url     : https://prove2.me/submissions/6afe8e71-05f6-454f-93b0-ae4f8feca0b3

import Theorems.Thm_lean_workbook_plus_40306
import Mathlib.Tactic.Linarith

theorem solution (a : ℝ) (ha : a > 0) (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hxy : x < y) :
    (x^4 + x^2 + a * x - 2) < (y^4 + y^2 + a * y - 2) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have h2 : x^2 < y^2 := by nlinarith
  have h4 : x^4 < y^4 := by nlinarith [h2, mul_pos hx1 hx1, mul_pos hy1 hy1, sq_nonneg (x*y)]
  have ha' : a * x < a * y := by nlinarith
  linarith
