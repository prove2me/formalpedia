-- Prove2me | solution 1 for lean_workbook_plus_76386
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:03.986261+00:00
-- url     : https://prove2.me/submissions/605ba178-8c3a-45b0-a8f9-cbb6f2ab95aa

import Mathlib

theorem solution (a b c : ℤ) (h : Even a ∧ Even b ∧ Even c) :
    4 ∣ a ^ 2 + b ^ 2 + c ^ 2 := by
  rcases h with ⟨⟨u, rfl⟩, ⟨v, rfl⟩, ⟨w, rfl⟩⟩
  exact ⟨u ^ 2 + v ^ 2 + w ^ 2, by ring⟩
