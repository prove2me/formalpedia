-- Prove2me | solution 1 for lean_workbook_plus_16454
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:02.881466+00:00
-- url     : https://prove2.me/submissions/3879abeb-41a6-4a13-bf4e-ba605213aa7a

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ)
  (h₀ : 0 < (x - 1)^2)
  (h₁ : (x - 2) / (x - 3) < 0) :
  2 < x ∧ x < 3 := by
  rcases div_neg_iff.mp h₁ with ⟨h, h'⟩ | ⟨h, h'⟩
  · constructor <;> linarith
  · exfalso; linarith
