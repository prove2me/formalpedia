-- Prove2me | solution 1 for lean_workbook_plus_19017
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:43.644439+00:00
-- url     : https://prove2.me/submissions/df5de37f-4a99-441d-9ea7-26c335f95ec7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 3/2 * x^2 + 3/2 * y^2 + 2 * x * y - x - y + 1 ≥ (x + y)^2 := by
  intros
  have h : (0 : ℝ) ≤ (3/2 * x^2 + 3/2 * y^2 + 2 * x * y - x - y + 1) - ((x + y)^2) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * x)))^2 := by positivity
      _ = (3/2 * x^2 + 3/2 * y^2 + 2 * x * y - x - y + 1) - ((x + y)^2) := by ring
  exact sub_nonneg.mp h
