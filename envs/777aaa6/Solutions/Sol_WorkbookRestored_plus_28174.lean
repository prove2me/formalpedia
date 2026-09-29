-- Prove2me | solution 1 for WorkbookRestored.plus_28174
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:02:01.391851+00:00
-- url     : https://prove2.me/submissions/13cbed9a-f4bc-4ea8-8d20-c01752b5558f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_28174.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β γ : ℝ) : α = π - (β + γ) → cos α = -cos (γ + β)   := by
  exact fun h ↦ by rw [h, cos_pi_sub, add_comm, cos_add]
#print axioms solution
