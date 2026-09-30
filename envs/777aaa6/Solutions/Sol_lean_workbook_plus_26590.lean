-- Prove2me | solution 1 for lean_workbook_plus_26590
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:15:05.595525+00:00
-- url     : https://prove2.me/submissions/b5957152-b0a6-4e83-b717-f7ef81deb4a7

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℕ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h₂ : a * d < b * c) : (a * d < b * c ∧ b * c < (a + c) * (b + d)) := by
  obtain ⟨ha, hb, hc, hd⟩ := h₁
  refine ⟨h₂, ?_⟩
  nlinarith [Nat.mul_pos ha hb, Nat.mul_pos hc hd]
