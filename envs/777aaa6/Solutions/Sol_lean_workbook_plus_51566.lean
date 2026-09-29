-- Prove2me | solution 1 for lean_workbook_plus_51566
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:03.193043+00:00
-- url     : https://prove2.me/submissions/e3527fa2-95a5-42ad-b114-b03548bc9e65

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (t : ℝ)
  (h₀ : -4.9 * t^2 + 20 * t = 0) :
  t = 0 ∨ t = 200 / 49 := by
  have hf : t*(t-200/49)=0 := by nlinarith [h₀]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)
