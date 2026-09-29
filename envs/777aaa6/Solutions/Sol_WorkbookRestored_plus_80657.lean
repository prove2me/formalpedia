-- Prove2me | solution 1 for WorkbookRestored.plus_80657
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:36.83336+00:00
-- url     : https://prove2.me/submissions/5a9711fa-926d-4fd2-8907-e6202d17d80d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80657.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α θ : ℝ) (h₁ : cos (2 * α) = 7 / 25) (h₂ : sin (2 * α) = 24 / 25) : cos (2 * α + 2 * θ) = (7 * cos (2 * θ) - 24 * sin (2 * θ)) / 25   := by
  rw [cos_add, h₁, h₂] <;> ring_nf
#print axioms solution
