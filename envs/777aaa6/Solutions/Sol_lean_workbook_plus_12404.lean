-- Prove2me | solution 1 for lean_workbook_plus_12404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:08.317455+00:00
-- url     : https://prove2.me/submissions/7d646006-0c0f-47c4-aaf4-23db78f43f4d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (h0 : 0 < x ∧ 0 < y ∧ 0 < z) (h1 : x < y) (h2 : y < z) : |x * z - y ^ 2| < y * (z - x) := by
  apply abs_lt.mpr
  constructor
  · have hp := mul_pos (show 0 < x+y by linarith [h0.1, h0.2.1]) (show 0 < z-y by linarith)
    nlinarith
  · have hp := mul_pos (show 0 < y-x by linarith) (show 0 < z+y by linarith [h0.2.1, h0.2.2])
    nlinarith
