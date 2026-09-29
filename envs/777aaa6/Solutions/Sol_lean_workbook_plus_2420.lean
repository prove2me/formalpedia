-- Prove2me | solution 1 for lean_workbook_plus_2420
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:45.483719+00:00
-- url     : https://prove2.me/submissions/900461b3-0164-4403-bf1d-7e9bae8bff40

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hxy : 0 < x ∧ 0 < y) (h : x + y + x * y = 3) : x + y ≥ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
