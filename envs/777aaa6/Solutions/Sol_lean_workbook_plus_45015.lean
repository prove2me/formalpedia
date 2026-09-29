-- Prove2me | solution 1 for lean_workbook_plus_45015
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:47.607966+00:00
-- url     : https://prove2.me/submissions/d511effb-fed3-48f0-8ea7-df3be05587c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 + 2 ≥ 2 * Real.sqrt (x^2 + 1) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x^2 + 1 by positivity), Real.sqrt_nonneg (x^2 + 1), sq_nonneg (x)])
