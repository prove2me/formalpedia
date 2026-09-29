-- Prove2me | solution 1 for lean_workbook_plus_3255
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:12.052605+00:00
-- url     : https://prove2.me/submissions/3d33d67f-c2b7-4542-9fe9-546514b1cebf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
  (1 + x^30) / (1 + x^60) < 1 + x^30 := by
  have hp : 0<1+x^30 := by positivity
  have hd : 1<1+x^60 := by nlinarith [pow_pos hx.1 60]
  exact div_lt_self hp hd
