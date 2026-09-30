-- Prove2me | solution 1 for lean_workbook_plus_75775
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:01.598527+00:00
-- url     : https://prove2.me/submissions/dcef2035-b35a-4392-927d-e6cc9d3eb819

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ x y z : ℝ,
    x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 + z ^ 4 * x ^ 2 ≥
      1 / 4 * (y * z * (x ^ 2 + y * z) * (y ^ 2 + x * z) +
        z * x * (y ^ 2 + x * z) * (z ^ 2 + x * y) +
        x * y * (z ^ 2 + x * y) * (x ^ 2 + y * z)) := by
  intro x y z
  nlinarith only [sq_nonneg (x^2*y-y^2*z), sq_nonneg (y^2*z-z^2*x),
    sq_nonneg (z^2*x-x^2*y)]

#print axioms solution
