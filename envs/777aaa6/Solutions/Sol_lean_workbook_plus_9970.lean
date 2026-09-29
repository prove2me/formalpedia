-- Prove2me | solution 1 for lean_workbook_plus_9970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:29.014149+00:00
-- url     : https://prove2.me/submissions/38a4202e-931d-42aa-85f9-bb1a020e1271

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : 5 * x ^ 2 + y ^ 2 + 4 ≥ 4 * x + 4 * x * y := by
  intros
  have h : (0 : ℝ) ≤ (5 * x ^ 2 + y ^ 2 + 4) - (4 * x + 4 * x * y) := by
    calc
      0 ≤ (4 : ℝ) * ((1 + ((-1 / 2) * x)))^2 + (1 : ℝ) * ((y + ((-2) * x)))^2 := by positivity
      _ = (5 * x ^ 2 + y ^ 2 + 4) - (4 * x + 4 * x * y) := by ring
  exact sub_nonneg.mp h
