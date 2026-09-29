-- Prove2me | solution 1 for lean_workbook_plus_31243
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:57.347297+00:00
-- url     : https://prove2.me/submissions/c0beebd5-67bd-490d-8c38-6ee5f7915196

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (X Y Z : ℝ) (hX : X ≥ 0) (hY : Y ≥ 0) (hZ : Z ≥ 0) : X ^ 3 + Y ^ 3 + Z ^ 3 + X ^ 2 * Y + Y ^ 2 * Z + Z ^ 2 * X ≥ 2 * (X * Y ^ 2 + Y * Z ^ 2 + Z * X ^ 2) := by
  (intros; nlinarith [sq_nonneg (X), sq_nonneg (Y), sq_nonneg (Z), sq_nonneg (X - Y), sq_nonneg (X - Z), sq_nonneg (Y - Z), sq_nonneg (X + Y), sq_nonneg (X + Z), sq_nonneg (Y + Z)])
