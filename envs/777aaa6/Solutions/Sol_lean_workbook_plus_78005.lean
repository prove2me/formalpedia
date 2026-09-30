-- Prove2me | solution 1 for lean_workbook_plus_78005
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:16:10.450256+00:00
-- url     : https://prove2.me/submissions/b1e19d15-f66b-461d-abde-5d47dc9bbb47

import Mathlib

theorem correct_strict_bound (x y : ℝ) (hxy : x > y) (hy : y > 0) :
    (x^4 - y^4) / (4 * x^3) < x - y := by
  have hx : 0 < x := lt_trans hy hxy
  have hden : 0 < 4 * x^3 := by positivity
  apply (div_lt_iff₀ hden).2
  have hrem : 0 < (x - y)^2 * (3*x^2 + 2*x*y + y^2) :=
    mul_pos (sq_pos_of_pos (sub_pos.mpr hxy)) (by positivity)
  nlinarith only [hrem]

theorem solution : ¬ (∀ (x y : ℝ), x > y → y > 0 →
    (x^4 - y^4) / (4 * x^3) > x - y) := by
  intro h
  have hbad := h 2 1 (by norm_num) (by norm_num)
  exact lt_asymm hbad (correct_strict_bound 2 1 (by norm_num) (by norm_num))
