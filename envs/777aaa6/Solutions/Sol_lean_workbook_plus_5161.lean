-- Prove2me | solution 1 for lean_workbook_plus_5161
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:28.999516+00:00
-- url     : https://prove2.me/submissions/1471b298-dacf-4cc3-8bdc-152bc94c877a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / 2 ≥ Real.sqrt (a * b) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a * b by positivity), Real.sqrt_nonneg (a * b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
