-- Prove2me | solution 1 for lean_workbook_plus_33893
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:45.821141+00:00
-- url     : https://prove2.me/submissions/c5cae387-d7f4-4341-9a73-a28ddb7072de

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) : 2 * u ^ 3 + 2 * v ^ 3 + 2 * w ^ 3 - u ^ 2 * v - u ^ 2 * w - v ^ 2 * w - w ^ 2 * u ≥ 0 := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (w), sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w), sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (v + w), mul_nonneg hu hv, mul_nonneg hu hw, mul_nonneg hv hw])
