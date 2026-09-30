-- Prove2me | solution 1 for lean_workbook_plus_10050
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:57.94763+00:00
-- url     : https://prove2.me/submissions/a66d6e97-47b6-42f0-b759-8eb1e046ea08

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) : (a^2+b^2+c^2)*(x^2+y^2+z^2) ≥ (a*x+b*y+c*z)^2 := by
  nlinarith [sq_nonneg (a*y - b*x), sq_nonneg (a*z - c*x), sq_nonneg (b*z - c*y)]
