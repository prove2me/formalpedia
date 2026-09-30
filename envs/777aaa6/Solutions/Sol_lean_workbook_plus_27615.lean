-- Prove2me | solution 1 for lean_workbook_plus_27615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:53.062711+00:00
-- url     : https://prove2.me/submissions/df5e4337-7513-412e-a094-e83d0185e839

import Mathlib.Analysis.Complex.Basic

theorem solution :
  ∀ a b : ℤ, a ≠ 0 ∧ b ≠ 0 → (a - b) ^ 2 + (a + b) ^ 2 > a ^ 2 + b ^ 2 := by
  intro a b ⟨ha, hb⟩
  have h1 : 0 < a ^ 2 := by positivity
  have h2 : 0 < b ^ 2 := by positivity
  nlinarith [h1, h2]
