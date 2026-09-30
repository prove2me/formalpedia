-- Prove2me | solution 1 for lean_workbook_plus_24455
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:39:29.464116+00:00
-- url     : https://prove2.me/submissions/5f391e42-2850-4dd3-9c3b-eddbf5ecdcec

import Mathlib.Analysis.Complex.Basic

theorem solution {a b : ℝ} (h₁ : a + b = 2) (h₂ : a ^ 4 + b ^ 4 = 16) : a * b = 0 := by
  have hb : b = 2 - a := by linarith
  subst hb
  have h3 : (a * (2 - a)) * (a * (2 - a) - 8) = 0 := by nlinarith
  have h4 : a * (2 - a) ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · linarith
