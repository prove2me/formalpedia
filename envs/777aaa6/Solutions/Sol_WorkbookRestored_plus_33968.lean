-- Prove2me | solution 1 for WorkbookRestored.plus_33968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:46.081912+00:00
-- url     : https://prove2.me/submissions/8bd46f9a-d57e-43ed-8c0e-331f648ba745

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33968.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |sin x - sin a| < ε   := by
  intro ε εpos
  have : ContinuousAt (fun x ↦ sin x) a := continuous_sin.continuousAt
  exact Metric.continuousAt_iff.mp this ε εpos
#print axioms solution
