-- Prove2me | solution 1 for lean_workbook_plus_39051
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:31.654134+00:00
-- url     : https://prove2.me/submissions/9b603f0a-9a5d-4da5-9e56-2927c322954b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : (x^4 + y^4) * (x^2 + y^2) ≥ 4 * x^3 * y^3 := by
  intros
  have h : (0 : ℝ) ≤ ((x^4 + y^4) * (x^2 + y^2)) - (4 * x^3 * y^3) := by
    calc
      0 ≤ (1 : ℝ) * (((y ^ 3) + ((-1) * (x ^ 3))))^2 + (1 : ℝ) * (((x * (y ^ 2)) + ((-1) * y * (x ^ 2))))^2 := by positivity
      _ = ((x^4 + y^4) * (x^2 + y^2)) - (4 * x^3 * y^3) := by ring
  exact sub_nonneg.mp h
