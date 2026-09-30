-- Prove2me | solution 1 for lean_workbook_plus_9230
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:15.073998+00:00
-- url     : https://prove2.me/submissions/e10fa286-ea85-4288-986b-ac0c987ff9a5

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha : 0 ≤ a) : ∃ f : ℝ → ℝ, ∀ x, (x < a ∧ f x = a / (a - x)) ∨ (x ≥ a ∧ f x = 0) := by
  refine ⟨fun x => if x < a then a / (a - x) else 0, fun x => ?_⟩
  by_cases h : x < a
  · exact Or.inl ⟨h, by simp [h]⟩
  · exact Or.inr ⟨not_lt.mp h, by simp [h]⟩
