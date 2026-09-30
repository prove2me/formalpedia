-- Prove2me | solution 1 for lean_workbook_plus_12389
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:03:51.092988+00:00
-- url     : https://prove2.me/submissions/3ec0458d-de9b-4674-9f56-4cdbe3f2afaf

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a : ℝ, a ≠ -1 ∧ a ≠ 1 → a^2 * (a^3 - 1) / (a^3 + 1) ≥ 3 * (a - 1) / 2 ↔ 2 * a^2 * (a - 1) * (a^2 + a + 1) / (a^3 + 1) ≥ 3 * (a - 1) := by
  intro a
  have key : 2 * a^2 * (a - 1) * (a^2 + a + 1) / (a^3 + 1) = 2 * (a^2 * (a^3 - 1) / (a^3 + 1)) := by
    ring
  rw [key]
  constructor
  · intro h
    by_cases h1 : a = -1
    · subst h1
      norm_num
    · by_cases h2 : a = 1
      · subst h2
        norm_num
      · have := h ⟨h1, h2⟩
        linarith
  · intro h _
    linarith
