-- Prove2me | solution 1 for WorkbookRestored.plus_42229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:42.777993+00:00
-- url     : https://prove2.me/submissions/89b8ded7-b581-4b84-9040-1b3d67b51645

/- InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_42229. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
theorem solution (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a = a⁻¹ ↔ a = 1 ∨ a = p-1   := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    have hsq : a ^ 2 = 1 := by
      calc
        a ^ 2 = a * a := pow_two a
        _ = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha
    have hc : a = 1 ∨ a = -1 := eq_or_eq_neg_of_sq_eq_sq a 1 (by simpa using hsq)
    simpa using hc
  · rintro (rfl | h)
    · simp
    · have hneg : a = -1 := by simpa using h
      rw [hneg]
      simp
#print axioms solution
