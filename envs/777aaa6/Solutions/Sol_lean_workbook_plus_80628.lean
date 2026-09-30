-- Prove2me | solution 1 for lean_workbook_plus_80628
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:54.568286+00:00
-- url     : https://prove2.me/submissions/a9f5f853-0a12-4465-a9ef-a67c570f7b83

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b x y : ℝ) (hab : a > b ∧ b > 0) (hxy : x > y ∧ y > 0) :
    (a + y) / (b + y) > (a + x) / (b + x) := by
  change (a+x) / (b+x) < (a+y) / (b+y)
  have hx : 0 < x := lt_trans hxy.2 hxy.1
  apply (div_lt_div_iff₀ (add_pos hab.2 hx) (add_pos hab.2 hxy.2)).mpr
  nlinarith [mul_pos (sub_pos.mpr hab.1) (sub_pos.mpr hxy.1)]
