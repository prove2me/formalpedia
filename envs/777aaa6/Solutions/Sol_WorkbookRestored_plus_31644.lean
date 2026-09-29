-- Prove2me | solution 1 for WorkbookRestored.plus_31644
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:36.148435+00:00
-- url     : https://prove2.me/submissions/bdd25d74-d407-4c87-b209-f37eb327f739

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_31644.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) :
  Real.cos θ + Real.sqrt 3 * Real.sin θ =
    2 * (Real.cos θ * Real.cos (Real.pi / 3) + Real.sin θ * Real.sin (Real.pi / 3))   := by
  simp [cos_add, sin_add, cos_pi_div_three, sin_pi_div_three]
  ring
#print axioms solution
