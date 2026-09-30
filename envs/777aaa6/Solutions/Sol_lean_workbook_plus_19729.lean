-- Prove2me | solution 1 for lean_workbook_plus_19729
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:32:49.825712+00:00
-- url     : https://prove2.me/submissions/0f81f2da-92ba-4099-89d5-d17644e384c9

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (u v : ℝ) : (u * v = 12 ∧ x = (v - u - 4) / 8 ∧ (2 * y + 1) ^ 2 = (u + v - 6) / 2) ↔ (u * v = 12 ∧ (u + v - 6) / 2 = (2 * y + 1) ^ 2 ∧ x = (v - u - 4) / 8) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3.symm, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2.symm⟩
