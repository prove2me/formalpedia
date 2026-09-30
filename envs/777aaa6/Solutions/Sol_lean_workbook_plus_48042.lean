-- Prove2me | solution 1 for lean_workbook_plus_48042
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:47:04.391477+00:00
-- url     : https://prove2.me/submissions/24da9e48-94ea-4925-9aeb-623efd2fdb50

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℕ)
    (h₀ : 0 ≤ x ∧ x ≤ 9) (h₁ : 0 ≤ y ∧ y ≤ 9)
    (h₂ : 3 ∣ (10 * x + y)) (h₃ : 3 ∣ (10 * y + (9 - x))) :
    x ∈ ({0, 3, 6, 9} : Finset ℕ) ∧ y ∈ ({0, 3, 6, 9} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

#print axioms solution
