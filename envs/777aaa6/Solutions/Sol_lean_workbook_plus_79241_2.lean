-- Prove2me | solution 2 for lean_workbook_plus_79241
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:49.990961+00:00
-- url     : https://prove2.me/submissions/a501b122-de7c-4f81-86d8-5b06060459ff

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^3+y^3 ≥ x*y*(x+y) := by
  have h : 0 ≤ (x+y)*(x-y)^2 := mul_nonneg (by linarith) (sq_nonneg (x-y))
  nlinarith
