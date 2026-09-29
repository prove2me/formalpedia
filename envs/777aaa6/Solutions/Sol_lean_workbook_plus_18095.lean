-- Prove2me | solution 1 for lean_workbook_plus_18095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:45.539553+00:00
-- url     : https://prove2.me/submissions/ede464da-962f-4f31-87b9-29ef74b24f9c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} : (x^2 * z^2 + x^2 * y^2 + y^2 * z^2)^2 ≥ 3 * (x^2 + y^2 + z^2) * x^2 * y^2 * z^2 := by
  intros
  have h : (0 : ℝ) ≤ ((x^2 * z^2 + x^2 * y^2 + y^2 * z^2)^2) - (3 * (x^2 + y^2 + z^2) * x^2 * y^2 * z^2) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((((y ^ 2) * (z ^ 2)) + ((-1) * (x ^ 2) * (z ^ 2))))^2 + ((1 / 2) : ℝ) * ((((y ^ 2) * (z ^ 2)) + ((-1) * (x ^ 2) * (y ^ 2))))^2 + ((1 / 2) : ℝ) * ((((x ^ 2) * (z ^ 2)) + ((-1) * (x ^ 2) * (y ^ 2))))^2 := by positivity
      _ = ((x^2 * z^2 + x^2 * y^2 + y^2 * z^2)^2) - (3 * (x^2 + y^2 + z^2) * x^2 * y^2 * z^2) := by ring
  exact sub_nonneg.mp h
