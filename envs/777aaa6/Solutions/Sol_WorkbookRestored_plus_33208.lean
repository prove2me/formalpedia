-- Prove2me | solution 1 for WorkbookRestored.plus_33208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:42.715207+00:00
-- url     : https://prove2.me/submissions/ab43470f-469a-48f0-9616-5604f0829678

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33208.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ)
  (y z : ℝ)
  (h₀ : sin x = y)
  (h₁ : cos x = z)
  (h₂ : y^2 + z^2 = 1)
  (h₃ : y^2 + 3 * y * z - 15 * z^2 = 0) :
  9 * y^2 * (1 - y^2) = (16 * y^2 - 15)^2   := by
  nlinarith [h₀, h₁, h₂, h₃]
#print axioms solution
