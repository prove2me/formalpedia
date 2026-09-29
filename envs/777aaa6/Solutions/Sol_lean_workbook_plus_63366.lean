-- Prove2me | solution 1 for lean_workbook_plus_63366
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:36.255618+00:00
-- url     : https://prove2.me/submissions/770a6e12-2e7b-46fe-b4b2-29202f268d3b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w : ℝ) : (u + v + w) ^ 2 ≥ 3 * (u * v + v * w + w * u) := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (w), sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w), sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (v + w)])
