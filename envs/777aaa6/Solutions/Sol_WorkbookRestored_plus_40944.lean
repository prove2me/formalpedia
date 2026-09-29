-- Prove2me | solution 1 for WorkbookRestored.plus_40944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:00.833316+00:00
-- url     : https://prove2.me/submissions/89352db0-284e-4a55-8cae-fcababbc54d9

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_40944.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : Continuous (fun p : ℝ × ℝ => sin (p.1^2 + p.2^2))   := by
  exact continuous_sin.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2))
#print axioms solution
