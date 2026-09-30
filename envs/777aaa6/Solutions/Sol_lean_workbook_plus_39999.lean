-- Prove2me | solution 1 for lean_workbook_plus_39999
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:25:04.016214+00:00
-- url     : https://prove2.me/submissions/c12f2e34-5600-49c0-8c91-025d5a598573

import Mathlib.Analysis.Complex.Basic

theorem solution  (p q : ℕ)
  (h₀ : 0 < p ∧ 0 < q)
  (h₁ : p ≠ q)
  (h₂ : 5 ∣ (p^2 + q^2) * (p^2 - q^2)) :
  5 ∣ p^4 - q^4 := by
  have e : p^4 - q^4 = (p^2 + q^2) * (p^2 - q^2) := by
    rw [show p^4 = (p^2)^2 by ring, show q^4 = (q^2)^2 by ring, Nat.sq_sub_sq]
  rw [e]
  exact h₂
