-- Prove2me | solution 1 for lean_workbook_plus_44958
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:07:14.355061+00:00
-- url     : https://prove2.me/submissions/cc64e95a-8ab2-41e1-8fa5-8f929a521d3f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (ha : a ≥ 0) : 2 * (a^2 + 1)^3 ≥ (a^3 + 1) * (a + 1)^3 := by
  have hfactor : 0 ≤ a ^ 2 + a + 1 := by positivity
  have h := mul_nonneg (sq_nonneg ((a - 1) ^ 2)) hfactor
  nlinarith [h]
