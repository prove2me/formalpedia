-- Prove2me | solution 1 for lean_workbook_plus_487
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:38.27405+00:00
-- url     : https://prove2.me/submissions/385ddcf3-f0f6-455e-893c-f1394ec8060a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^9 + b^9 = 2) : a^2 / b + b^2 / a ≥ 2 := by
  have h1 : a^2 / b = a^3 := by
    field_simp
    nlinarith [hab]
  have h2 : b^2 / a = b^3 := by
    field_simp
    nlinarith [hab]
  rw [h1, h2]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), mul_pos ha hb, hab, sq_nonneg (a - 1), sq_nonneg (b - 1)]
