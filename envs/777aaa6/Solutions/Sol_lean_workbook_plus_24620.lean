-- Prove2me | solution 1 for lean_workbook_plus_24620
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:34:59.276761+00:00
-- url     : https://prove2.me/submissions/78e08eb1-0e45-4503-acda-931a53884b36

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 3 * u ^ 4 + 2 * u ^ 3 * v - 3 * u ^ 2 * v ^ 2 - 2 * u * v ^ 3 + 3 * v ^ 4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (u - v), sq_nonneg (u + v), mul_nonneg hu hv])
