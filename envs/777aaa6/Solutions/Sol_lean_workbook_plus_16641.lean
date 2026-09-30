-- Prove2me | solution 1 for lean_workbook_plus_16641
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:00:41.420252+00:00
-- url     : https://prove2.me/submissions/4c161e2b-3125-4460-8dcc-d9cfeb433b58

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem degree_eight_variance_identity (x y z : ℝ) :
    6 * (x ^ 6 * z ^ 2 + y ^ 6 * x ^ 2 + z ^ 6 * y ^ 2) -
      6 * (x ^ 4 * y ^ 3 * z + y ^ 4 * z ^ 3 * x + z ^ 4 * x ^ 3 * y) =
    3 * ((x ^ 3 * z - y ^ 3 * x) ^ 2 + (y ^ 3 * x - z ^ 3 * y) ^ 2 +
      (z ^ 3 * y - x ^ 3 * z) ^ 2) := by
  ring

theorem solution (x y z : ℝ) :
    6 * (x ^ 6 * z ^ 2 + y ^ 6 * x ^ 2 + z ^ 6 * y ^ 2) ≥
      6 * (x ^ 4 * y ^ 3 * z + y ^ 4 * z ^ 3 * x + z ^ 4 * x ^ 3 * y) := by
  linarith [degree_eight_variance_identity x y z,
    sq_nonneg (x ^ 3 * z - y ^ 3 * x), sq_nonneg (y ^ 3 * x - z ^ 3 * y),
    sq_nonneg (z ^ 3 * y - x ^ 3 * z)]

#print axioms solution
