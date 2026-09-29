-- Prove2me | solution 1 for lean_workbook_plus_58025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:25:51.673563+00:00
-- url     : https://prove2.me/submissions/b1f43311-84be-4520-bb4d-622558ba9901

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 1 / 2 * x ^ 6 + 1 / 2 * x ^ 4 * y ^ 4 ≥ x ^ 5 * y ^ 2 := by
  nlinarith [sq_nonneg (x ^ 3 - x ^ 2 * y ^ 2)]
