-- Prove2me | solution 1 for lean_workbook_plus_40868
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:12.032839+00:00
-- url     : https://prove2.me/submissions/609be895-33e6-44a4-bb6e-21704d160cd6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : 5.3 + y^2 * x^2 + y^2 * z^2 + z^2 * x^2 ≥ 2 * (x * y + z * x + y * z) := by
  intros
  have h : (0 : ℝ) ≤ (5.3 + y^2 * x^2 + y^2 * z^2 + z^2 * x^2) - (2 * (x * y + z * x + y * z)) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * y * z)))^2 + ((7 / 150) : ℝ) * ((1 + ((-2) * x * z)))^2 + ((18 / 25) : ℝ) * ((1 + ((1 / 2) * x * z)))^2 + ((38 / 15) : ℝ) * ((1 + ((-1 / 2) * x * z)))^2 + (1 : ℝ) * ((1 + ((-1) * x * y)))^2 := by positivity
      _ = (5.3 + y^2 * x^2 + y^2 * z^2 + z^2 * x^2) - (2 * (x * y + z * x + y * z)) := by ring
  exact sub_nonneg.mp h
