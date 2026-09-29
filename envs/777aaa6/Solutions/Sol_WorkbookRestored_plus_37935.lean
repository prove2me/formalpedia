-- Prove2me | solution 1 for WorkbookRestored.plus_37935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:11.487156+00:00
-- url     : https://prove2.me/submissions/0a1f2a03-f5c8-41db-b656-d17eeeba1b18

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_37935.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (ha : 1 ≤ a) : ∀ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ≤ y → x^a + a^x ≤ y^a + a^y   := by
  rintro x y ⟨hx, hy, hxy⟩
  gcongr <;> linarith
#print axioms solution
