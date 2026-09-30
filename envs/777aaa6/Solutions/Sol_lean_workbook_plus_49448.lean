-- Prove2me | solution 1 for lean_workbook_plus_49448
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:44.340347+00:00
-- url     : https://prove2.me/submissions/3b1239c6-a712-487e-83b9-526992d18172

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ {a b c : ℕ},
    a ∣ b ∧ b ∣ c ∧ c ∣ a → a = b ∧ b = c ∧ c = a := by
  intro a b c h
  exact ⟨Nat.dvd_antisymm h.1 (dvd_trans h.2.1 h.2.2),
    Nat.dvd_antisymm h.2.1 (dvd_trans h.2.2 h.1),
    Nat.dvd_antisymm h.2.2 (dvd_trans h.1 h.2.1)⟩
