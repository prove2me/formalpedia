-- Prove2me | solution 1 for WorkbookRestored.plus_18068
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:52.714198+00:00
-- url     : https://prove2.me/submissions/3e1ad0e1-6f73-42a8-b3ac-ba6517714dce

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_18068. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a * a⁻¹ = 1   := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact mul_inv_cancel₀ ha
#print axioms solution
