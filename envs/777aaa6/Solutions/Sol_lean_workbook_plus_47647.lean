-- Prove2me | solution 1 for lean_workbook_plus_47647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:03:04.506701+00:00
-- url     : https://prove2.me/submissions/5db526df-d417-47d3-9170-1ade9a6ddba0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z u v w : ℝ) :
  (x - u) ^ 2 + (y - v) ^ 2 + (z - w) ^ 2 ≥
    1 / 2 * ((x - z) * (x - u - v + z) + (y - x) * (y - v - w + x) + (z - y) * (z - w - u + y)) := by
  nlinarith only [sq_nonneg (4*(x-u)-(x-y)), sq_nonneg (4*(y-v)-(y-z)), sq_nonneg (4*(z-w)-(z-x)), sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
