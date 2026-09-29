-- Prove2me | solution 1 for lean_workbook_plus_46768
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:10.583421+00:00
-- url     : https://prove2.me/submissions/2abefeb8-e739-4980-8156-3689cd8a5d83

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := by
  exact (Real.sqrt_mul hx.le y).symm
