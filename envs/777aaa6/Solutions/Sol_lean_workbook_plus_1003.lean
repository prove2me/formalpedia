-- Prove2me | solution 1 for lean_workbook_plus_1003
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:12:46.543162+00:00
-- url     : https://prove2.me/submissions/708f33a4-3401-4b24-a5e5-a0f5744fba67

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d e f : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f)
  (h₁ : a * b * c - d * e * f = 1) :
  (a * b * c - d * e * f : ℚ) ≥ 1 / 288 := by
  have h2 : a * b * c = d * e * f + 1 := by
    generalize a * b * c = x at h₁ ⊢
    generalize d * e * f = y at h₁ ⊢
    omega
  have h3 : ((a * b * c : ℕ) : ℚ) = ((d * e * f + 1 : ℕ) : ℚ) := by rw [h2]
  push_cast at h3
  linarith
