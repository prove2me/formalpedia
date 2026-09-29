-- Prove2me | solution 1 for lean_workbook_plus_38308
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:58.889163+00:00
-- url     : https://prove2.me/submissions/e845fe62-6d34-400c-82e4-747bfce40b22

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z) ≥ y * z * (2 * x * y + 2 * x * z - y * z) := by
  intros
  have h : (0 : ℝ) ≤ (x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z)) - (y * z * (2 * x * y + 2 * x * z - y * z)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((y * z) + ((-2) * x * z)))^2 + ((1 / 2) : ℝ) * (((y * z) + ((-2) * x * y)))^2 + (1 : ℝ) * (((x * z) + ((-1) * x * y)))^2 := by positivity
      _ = (x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z)) - (y * z * (2 * x * y + 2 * x * z - y * z)) := by ring
  exact sub_nonneg.mp h
