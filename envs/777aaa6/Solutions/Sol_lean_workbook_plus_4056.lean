-- Prove2me | solution 1 for lean_workbook_plus_4056
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:53.364309+00:00
-- url     : https://prove2.me/submissions/37acd9ca-5796-4592-af27-192b327fbc18

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
