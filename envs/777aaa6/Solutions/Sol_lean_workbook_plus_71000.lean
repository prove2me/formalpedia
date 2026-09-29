-- Prove2me | solution 1 for lean_workbook_plus_71000
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:27.570516+00:00
-- url     : https://prove2.me/submissions/d3382bba-5dc9-4fdf-8c6b-711cd9105541

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b ≥ 2 * Real.sqrt (a * b) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a * b by positivity), Real.sqrt_nonneg (a * b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
