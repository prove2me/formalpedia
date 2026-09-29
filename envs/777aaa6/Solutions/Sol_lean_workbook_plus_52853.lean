-- Prove2me | solution 1 for lean_workbook_plus_52853
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:38.962798+00:00
-- url     : https://prove2.me/submissions/add1830f-1905-4169-9a3b-250c278ea035

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (t : ℝ) :
  2 * t ≤ 1 + t^2 := by
  intros
  have h : (0 : ℝ) ≤ (1 + t^2) - (2 * t) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * t)))^2 := by positivity
      _ = (1 + t^2) - (2 * t) := by ring
  exact sub_nonneg.mp h
