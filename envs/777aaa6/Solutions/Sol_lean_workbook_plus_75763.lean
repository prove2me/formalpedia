-- Prove2me | solution 1 for lean_workbook_plus_75763
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:04.764325+00:00
-- url     : https://prove2.me/submissions/9a59e450-9783-47d7-bacf-aaa07beadb94

import Mathlib

theorem solution (a b c m n : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) :
    a ∣ (m * b - n * c) := by
  rcases h₁ with ⟨u, rfl⟩
  rcases h₂ with ⟨v, rfl⟩
  exact ⟨m * u - n * v, by ring⟩
