-- Prove2me | solution 1 for lean_workbook_plus_35589
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:42.452956+00:00
-- url     : https://prove2.me/submissions/f33acb00-3186-4552-8ab5-4b62fba8a503

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, x < y → x^3 < y^3 := by
  intro x y h
  have hp : 0<y^2+x*y+x^2 := by
    have hd := sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt h))
    nlinarith [sq_nonneg (x+y)]
  have hm := mul_pos (sub_pos.mpr h) hp
  nlinarith only [hm]
