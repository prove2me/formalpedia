-- Prove2me | solution 1 for lean_workbook_plus_18577
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:05.58736+00:00
-- url     : https://prove2.me/submissions/63cc2455-182d-41a2-beb6-3127069a14e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b ≥ 2 * Real.sqrt (a * b) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a * b by positivity), Real.sqrt_nonneg (a * b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
