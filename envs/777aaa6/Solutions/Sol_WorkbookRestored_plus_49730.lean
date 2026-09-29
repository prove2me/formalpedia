-- Prove2me | solution 1 for WorkbookRestored.plus_49730
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:44.207247+00:00
-- url     : https://prove2.me/submissions/800bae8e-ecf3-4041-ab76-c904643c33c6

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_49730.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y z : ℝ) : Real.sin (x - y) * Real.sin (z - x) = 1/2 * (Real.cos (2 * x - y - z) - Real.cos (z - y))   := by
  rw [show 2*x-y-z = (x-y)-(z-x) by ring,show z-y=(x-y)+(z-x) by ring,cos_sub,cos_add]
  ring
#print axioms solution
