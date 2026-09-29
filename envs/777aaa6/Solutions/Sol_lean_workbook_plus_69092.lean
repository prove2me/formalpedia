-- Prove2me | solution 1 for lean_workbook_plus_69092
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:03.045574+00:00
-- url     : https://prove2.me/submissions/55df6fff-e04c-4d5a-9c4d-c9cd0dd1fa14

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ x^2 - 2 * x = 0) :
  S = {0, 2} := by
  ext x
  rw [h₀]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hp : x * (x - 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl h
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
