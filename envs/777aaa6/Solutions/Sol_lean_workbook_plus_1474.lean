-- Prove2me | solution 1 for lean_workbook_plus_1474
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:21.98071+00:00
-- url     : https://prove2.me/submissions/9ab7d1d5-5b2f-412a-b9c5-a5d61c1cf6a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 4 * x * y) : x⁻¹ + y⁻¹ = 4 := by
  intros
  grind
