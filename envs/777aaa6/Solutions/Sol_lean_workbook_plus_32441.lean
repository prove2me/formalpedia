-- Prove2me | solution 1 for lean_workbook_plus_32441
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:55.544164+00:00
-- url     : https://prove2.me/submissions/e453050f-010b-4340-b297-a997ef3e8734

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (i : ℕ) (hx : x > -1) (hi : 1 ≤ i) :
  (1 + x) ^ i ≥ 1 + i * x := by
  exact one_add_mul_le_pow (by linarith : (-2:ℝ)≤x) i
