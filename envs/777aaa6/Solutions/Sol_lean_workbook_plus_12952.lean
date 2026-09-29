-- Prove2me | solution 1 for lean_workbook_plus_12952
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:48.407165+00:00
-- url     : https://prove2.me/submissions/de6d7189-9062-457f-b140-7bcbb5b762d3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : a > 1) : (a - 1)⁻¹ + a⁻¹ + (a + 1)⁻¹ > 3 * a⁻¹ := by
  have ha0 : 0 < a := by linarith
  have ham : 0 < a-1 := by linarith
  have hap : 0 < a+1 := by linarith
  have hi : (a-1)⁻¹+a⁻¹+(a+1)⁻¹-3*a⁻¹ = 2/(a*(a-1)*(a+1)) := by field_simp; ring
  have hp : 0 < 2/(a*(a-1)*(a+1)) := by positivity
  linarith
