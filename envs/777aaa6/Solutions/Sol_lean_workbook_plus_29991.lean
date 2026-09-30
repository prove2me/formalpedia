-- Prove2me | solution 1 for lean_workbook_plus_29991
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:07.24299+00:00
-- url     : https://prove2.me/submissions/b7cd304d-2364-402a-b228-f63c966ff334

import Mathlib.Analysis.Complex.Basic

theorem solution {α : Type} (A B C : Set α) (h1 : A ∪ B = A ∪ C) (h2 : A ∩ B = A ∩ C) : B = C := by
  ext x
  constructor
  · intro hx
    by_cases hA : x ∈ A
    · have hm : x ∈ A ∩ B := ⟨hA, hx⟩
      rw [h2] at hm
      exact hm.2
    · have hm : x ∈ A ∪ B := Or.inr hx
      rw [h1] at hm
      exact hm.resolve_left hA
  · intro hx
    by_cases hA : x ∈ A
    · have hm : x ∈ A ∩ C := ⟨hA, hx⟩
      rw [← h2] at hm
      exact hm.2
    · have hm : x ∈ A ∪ C := Or.inr hx
      rw [← h1] at hm
      exact hm.resolve_left hA
