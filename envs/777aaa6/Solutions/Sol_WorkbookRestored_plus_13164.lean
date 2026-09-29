-- Prove2me | solution 1 for WorkbookRestored.plus_13164
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:47.170697+00:00
-- url     : https://prove2.me/submissions/f08810c2-6ecf-4f92-b0e5-6bace02264ca

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_13164. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (ha : a ≠ 1) (ha' : a > 0) : ∀ f : ℝ → ℝ, (∀ x y : ℝ, f (x + y) = f y * a ^ x) ↔ ∃ k :ℝ, ∀ x : ℝ, f x = k * a ^ x   := by
  refine' fun f => ⟨_, _⟩
  exact fun h => ⟨f 0, fun x ↦ by simpa using h x 0⟩
  rintro ⟨k, hk⟩ x y
  rw [hk, hk y, mul_assoc]
  simp [Real.rpow_add ha', mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
