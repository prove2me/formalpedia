-- Prove2me | solution 1 for lean_workbook_plus_60827
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:16.969706+00:00
-- url     : https://prove2.me/submissions/bc582635-f4ea-494a-9003-ac05c869b183

import Mathlib.Analysis.Complex.Basic

theorem solution (b : ℕ) (h1 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 4) (h2 : b % 7 = 0 ∨ b % 7 = 3 ∨ b % 7 = 4) : ∃ k : ℕ, b = 0 + k*5 ∨ b = 4 + k*5 ∨ b = 10 + k*5 ∨ b = 11 + k*5 ∨ b = 14 + k*5 ∨ b = 21 + k*5 ∨ b = 24 + k*5 ∨ b = 25 + k*5 := by
  rcases h1 with h | h | h
  · exact ⟨b / 5, Or.inl (by omega)⟩
  · exact ⟨(b - 11) / 5, by omega⟩
  · exact ⟨b / 5, Or.inr (Or.inl (by omega))⟩
