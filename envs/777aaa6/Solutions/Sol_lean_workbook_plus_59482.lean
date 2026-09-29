-- Prove2me | solution 1 for lean_workbook_plus_59482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:19.885784+00:00
-- url     : https://prove2.me/submissions/12646efb-2861-4de1-8e19-1ccb7404dbcc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y : ℝ} : 25 * x ^ 2 + 25 * y ^ 2 ≥ 50 * x * y := by
  intros
  have h : (0 : ℝ) ≤ (25 * x ^ 2 + 25 * y ^ 2) - (50 * x * y) := by
    calc
      0 ≤ (25 : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (25 * x ^ 2 + 25 * y ^ 2) - (50 * x * y) := by ring
  exact sub_nonneg.mp h
