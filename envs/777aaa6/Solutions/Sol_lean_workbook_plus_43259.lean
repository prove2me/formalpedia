-- Prove2me | solution 1 for lean_workbook_plus_43259
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:04.839915+00:00
-- url     : https://prove2.me/submissions/db2854b1-f5f1-4627-b363-a2e9ce958366

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : x*y*z = 1) : x^2 + y^2 + z^2 ≥ x*y + y*z + x*z := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (x-z)]
