-- Prove2me | solution 1 for lean_workbook_plus_46905
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:54:41.912283+00:00
-- url     : https://prove2.me/submissions/4a1bd36b-ae34-49b3-9a2f-067ac54ab705

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x0 : Fin m → ℝ) (h : A.mulVec x0 = b) :
    ∀ x, A.mulVec x = b ↔ ∃ h : Fin m → ℝ, x = x0 + h ∧ A.mulVec h = 0 := by
  intro x
  constructor
  · intro hx
    refine ⟨x - x0, ?_, ?_⟩
    · simp only [← add_sub_assoc, add_sub_cancel_left]
    · rw [Matrix.mulVec_sub, hx, h, sub_self]
  · rintro ⟨v, rfl, hv⟩
    rw [Matrix.mulVec_add, h, hv, add_zero]
