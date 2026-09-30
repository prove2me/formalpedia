-- Prove2me | solution 1 for lean_workbook_plus_18747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:36.203437+00:00
-- url     : https://prove2.me/submissions/393b81bb-b7d2-4653-940b-3cc0e05a5b1c

import Mathlib.Analysis.Complex.Basic

theorem solution (n a b : ℕ) (t x : Fin n → ℝ) :
  (∑ i, t i * x i + a * b * ∑ i, t i / x i) ^ 2 ≥
  4 * a * b * (∑ i, t i * x i) * (∑ i, t i / x i) := by
  nlinarith [sq_nonneg (∑ i, t i * x i - a * b * ∑ i, t i / x i)]
