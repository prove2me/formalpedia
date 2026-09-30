-- Prove2me | solution 1 for lean_workbook_plus_75653
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:38:02.948991+00:00
-- url     : https://prove2.me/submissions/7b7fd69c-ef18-4320-9685-c53a873ce1de

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ p : ℕ, p.Prime ∧ p % 8 = 1 ∨ p.Prime ∧ p % 8 = 3 ↔ p.Prime ∧ ∃ x y : ℕ, x^2 + 2*y^2 = p) := by
  intro h
  have h2 := (h 2).2 ⟨Nat.prime_two, 0, 1, by norm_num⟩
  rcases h2 with ⟨_, h8⟩ | ⟨_, h8⟩ <;> norm_num at h8
