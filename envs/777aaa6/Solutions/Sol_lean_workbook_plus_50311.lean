-- Prove2me | solution 1 for lean_workbook_plus_50311
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:11.450982+00:00
-- url     : https://prove2.me/submissions/00b1868d-2f33-459e-bbfb-09e2fda92eff

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : x^2 + y^2 + 1 ≥ x*y + x + y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
