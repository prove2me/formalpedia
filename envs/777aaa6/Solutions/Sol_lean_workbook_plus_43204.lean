-- Prove2me | solution 1 for lean_workbook_plus_43204
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:39.809367+00:00
-- url     : https://prove2.me/submissions/2fce6b09-32c6-49db-82c9-3efc5347c7e7

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ)
  (h₀ : (2 * x - 1) * (x - 2) = 0) :
  x = 1 / 2 ∨ x = 2 := by
  rcases mul_eq_zero.mp h₀ with h | h
  · left; linarith
  · right; linarith
