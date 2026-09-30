-- Prove2me | solution 1 for lean_workbook_plus_44767
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:26:16.380435+00:00
-- url     : https://prove2.me/submissions/f4a7287f-ae9c-4f8b-903b-8a9b318076e5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

theorem solution (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a * b = 4) (h₂ : a + b = 4) :
    a = 2 ∧ b = 2 := by
  have hb : b = 4 - a := by linarith
  subst hb
  have h3 : (a - 2) ^ 2 = 0 := by nlinarith
  have h4 : a ≤ 2 := by nlinarith
  have h5 : a ≥ 2 := by nlinarith
  constructor <;> linarith
