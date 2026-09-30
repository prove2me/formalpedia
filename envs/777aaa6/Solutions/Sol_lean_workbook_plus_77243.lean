-- Prove2me | solution 1 for lean_workbook_plus_77243
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:34.883265+00:00
-- url     : https://prove2.me/submissions/598fc5ba-e3c1-4832-b4cf-fccaa1085c45

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * (4 + a * b) ≥ 8 * a * b := by
  nlinarith only [mul_nonneg ha (sq_nonneg (b - 2)),
    mul_nonneg hb (sq_nonneg (a - 2))]
