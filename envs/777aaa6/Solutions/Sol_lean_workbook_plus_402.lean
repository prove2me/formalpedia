-- Prove2me | solution 1 for lean_workbook_plus_402
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:27.015283+00:00
-- url     : https://prove2.me/submissions/41b1dc93-3fc4-43e9-980c-c3addc079541

import Mathlib.Analysis.Complex.Basic

theorem solution (p q r a b : ℝ)
  (h₀ : p + q + r = 1 / a)
  (h₁ : p * q + q * r + r * p = b / a) :
  a * b = (p * q + q * r + r * p) / (p + q + r)^2 := by
  rw [h₀, h₁]
  by_cases ha : a = 0
  · subst ha
    simp
  · field_simp
