-- Prove2me | solution 1 for lean_workbook_plus_26505
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:39.151446+00:00
-- url     : https://prove2.me/submissions/710ce8a7-2c7e-47de-b94e-8adc95f9fcf3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) (hx : x = (2^31 + 3^31) / (2^29 + 3^29)) : ⌊x⌋ = 8 := by
  rw [hx, Int.floor_eq_iff]
  norm_num
