-- Prove2me | solution 1 for lean_workbook_plus_27916
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:11:12.910794+00:00
-- url     : https://prove2.me/submissions/25d1bb4b-7619-468e-9cd5-deeb7643b3ec

import Mathlib.Analysis.Complex.Basic

theorem solution  (f g : ℝ → ℝ)
  (h₁ : Continuous g)
  (h₂ : 0 ≤ g ∧ g ≤ 1)
  (h₃ : ∀ x y, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 → x ≤ y → f x ≤ f y)
  (h₄ : ∀ x y, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 → x < y → f x < f y)
  (h₅ : g 0 = 0 ∨ g 1 = 1)
  (h₆ : f 0 = 0 ∧ f 1 = 1) :
  ∃ x, g x = x := by
  rcases h₅ with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
