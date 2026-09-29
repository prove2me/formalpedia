-- Prove2me | solution 1 for lean_workbook_plus_23252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:49.815103+00:00
-- url     : https://prove2.me/submissions/7b854c8e-7ba2-494d-8bb5-c6fe9f7a05d0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : 1 / (1 + x) ^ 2 < 1 / (1 + x) ∧ 1 / (1 + x) < 1 := by
  have hd : 0<1+x := by linarith
  constructor
  · apply one_div_lt_one_div_of_lt hd
    nlinarith
  · apply (div_lt_iff₀ hd).2
    linarith
