-- Prove2me | solution 1 for lean_workbook_plus_8442
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:32.531667+00:00
-- url     : https://prove2.me/submissions/ecc2a174-9c77-4cc0-ade4-3550c72482e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 3 * (x ^ 2 + y ^ 2 + 1 ^ 2 + y * x + x + y) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
