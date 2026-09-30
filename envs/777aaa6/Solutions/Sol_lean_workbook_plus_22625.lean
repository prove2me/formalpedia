-- Prove2me | solution 1 for lean_workbook_plus_22625
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:24.636281+00:00
-- url     : https://prove2.me/submissions/25e6b623-d5b9-4321-abb3-e7247408ab19

import Mathlib.Analysis.Complex.Basic

theorem solution (a b x z : ℝ) : a * x = z + b ∧ b * z = x + a → (a - 1) * x + (b - 1) * z = a + b := by
  rintro ⟨h1, h2⟩
  linarith
