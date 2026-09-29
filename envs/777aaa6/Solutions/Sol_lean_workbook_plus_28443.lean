-- Prove2me | solution 1 for lean_workbook_plus_28443
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T19:38:18.619532+00:00
-- url     : https://prove2.me/submissions/a9079865-ae1f-428b-81f9-1a1e319fc970

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x r : ℝ) (h : x^5 - x^3 + x = r) : x^6 ≥ 2 * r - 1   := by
  have hq : 0 ≤ x ^ 4 - x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
  have hp := mul_nonneg (sq_nonneg (x - 1)) hq
  nlinarith only [h, hp]
