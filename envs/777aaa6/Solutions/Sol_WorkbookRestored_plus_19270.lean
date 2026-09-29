-- Prove2me | solution 1 for WorkbookRestored.plus_19270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:32.645437+00:00
-- url     : https://prove2.me/submissions/0afdd696-a116-4dc6-89db-6e19443d4edb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19270.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : sin x ≠ 0 ∧ cos x ≠ 0) : tan x + 1 / tan x = 1 / (sin x * cos x)   := by
  rw [tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2]
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
