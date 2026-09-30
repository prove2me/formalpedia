-- Prove2me | solution 1 for lean_workbook_plus_20076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:03.876828+00:00
-- url     : https://prove2.me/submissions/beccd505-8bcd-4f12-b14d-5085515d3101

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c d x y : ℝ} (hab : a = b + x) (hcd : d = c + y) :
  6 * (x ^ 2 + y ^ 2) + (x + y) ^ 2 + 4 * (x + y) * (b + c) + 4 * (b + c) ^ 2 - 12 * b * c ≥ 0 ∧
  3 * (x - y) ^ 2 + 3 * (b - c) ^ 2 + (2 * x + 2 * y + b + c) ^ 2 ≥ 0 := by
  constructor
  · nlinarith [sq_nonneg (x - y), sq_nonneg (b - c), sq_nonneg (2 * x + 2 * y + b + c)]
  · positivity
