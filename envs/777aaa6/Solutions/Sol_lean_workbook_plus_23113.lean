-- Prove2me | solution 1 for lean_workbook_plus_23113
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:46:26.719851+00:00
-- url     : https://prove2.me/submissions/25a8d04b-11ea-4dd6-8981-5ed543267947

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b * (a + 2 * b - 10) + 8 * (a + b) ≥ 9 := by
  have hau : 0 ≤ a-1 := sub_nonneg.mpr ha
  have hbv : 0 ≤ b-1 := sub_nonneg.mpr hb
  have hs : 0 ≤ (b-1)*(a-2)^2 + 2*(a-1)*(b-2)^2 + (a+b-2)^2 + (b-1)^2 + 2*(b-1) := by positivity
  nlinarith only [hs]
