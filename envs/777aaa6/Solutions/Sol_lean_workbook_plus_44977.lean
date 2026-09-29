-- Prove2me | solution 1 for lean_workbook_plus_44977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:41.250707+00:00
-- url     : https://prove2.me/submissions/c40f5d46-f294-489f-bb7b-7535973f19e4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (t : ℝ) (ht : 0 < t ∧ t < 1) :
  (27 * t ^ 4 + 1) / (t ^ 2 - 2 * t + 1) ≥ 18 * t - 3 := by
  have hd : 0 < t^2-2*t+1 := by
    nlinarith [sq_pos_of_ne_zero (by linarith [ht.2] : t-1 ≠ 0)]
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (sq_nonneg (3*t-1)) (by positivity : 0 ≤ 3*t^2+4)]
