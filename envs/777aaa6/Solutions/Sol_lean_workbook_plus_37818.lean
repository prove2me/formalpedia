-- Prove2me | solution 1 for lean_workbook_plus_37818
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:28:24.653717+00:00
-- url     : https://prove2.me/submissions/852a72f7-b4c0-48f2-aa39-fe8d82959948

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ S : Finset ℝ, S.card ≥ 7 → ∃ x y, (x : ℝ) ∈ S ∧ (y : ℝ) ∈ S ∧ 0 ≤ (x - y) / (1 + x * y) ∧ (x - y) / (1 + x * y) ≤ 1 / Real.sqrt 3 := by
  intro S hS
  obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨x, x, hx, hx, ?_, ?_⟩
  · rw [sub_self, zero_div]
  · rw [sub_self, zero_div]
    positivity
