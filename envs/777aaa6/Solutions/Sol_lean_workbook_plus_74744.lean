-- Prove2me | solution 1 for lean_workbook_plus_74744
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:51.922525+00:00
-- url     : https://prove2.me/submissions/1cbc431e-650e-45a9-b93d-eb37617eeed0

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a + b + c = 0) : (a^3 + b^3 + c^3 + a^2 - b^2 - c^2) / (b * c) = 3 * a + 2 := by
  have hc' : c = -a - b := by linarith
  subst hc'
  rw [div_eq_iff (mul_ne_zero hb hc)]
  ring
