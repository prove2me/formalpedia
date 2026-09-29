-- Prove2me | solution 1 for lean_workbook_plus_68921
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:26.362163+00:00
-- url     : https://prove2.me/submissions/102f8769-6929-4b94-bbfe-1208eb87c8ef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ≠ 2)
  (h₂ : x ≠ -3)
  (h₃ : x^2 + x - 6 ≠ 0)
  (h₄ : x^2 - 4 * x + 3 ≥ 0) :
  Real.sqrt ((x^2 - 4 * x + 3) / (x^2 + x - 6)) = Real.sqrt ((x - 1) * (x - 3) / ((x - 2) * (x + 3))) := by
  clear h₀ h₁ h₂ h₃ h₄
  grind
