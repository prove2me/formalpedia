-- Prove2me | solution 1 for lean_workbook_plus_35102
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:30.747135+00:00
-- url     : https://prove2.me/submissions/2accc0c4-81bb-4690-aa28-238f5b896eea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : 0 ≤ x) : √x ≤ (1 / 2) * (x - 1) + 1 := by
  have hs := Real.sq_sqrt hx
  nlinarith only [hs,sq_nonneg (Real.sqrt x-1)]
