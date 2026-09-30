-- Prove2me | solution 1 for lean_workbook_plus_28710
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:15.366282+00:00
-- url     : https://prove2.me/submissions/d53c8899-284a-4475-9283-721507f383b0

import Mathlib
set_option autoImplicit false

theorem solution (P Q : Type) (f : P → Q) (h : ∀ B : Set Q, f '' (f ⁻¹' B) = B) : ∀ y : Q, ∃ x : P, f x = y   := by
  intro y
  have h1 : y ∈ f '' (f ⁻¹' {y}) := by rw [h]; simp
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, hx.2⟩

#print axioms solution
