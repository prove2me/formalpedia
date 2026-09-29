-- Prove2me | solution 1 for lean_workbook_plus_27581
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:48.580293+00:00
-- url     : https://prove2.me/submissions/d1d67832-6348-45a4-81e0-0f015eacbf6b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x ≥ 0) : x + 1 ≥ 2 * Real.sqrt x := by
  nlinarith only [Real.sq_sqrt hx,sq_nonneg (Real.sqrt x-1)]
