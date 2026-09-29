-- Prove2me | solution 1 for lean_workbook_plus_68445
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:29:59.502545+00:00
-- url     : https://prove2.me/submissions/84808cef-93e4-4e64-8d99-051f0175bba0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 4 / (x + y) ≤ 1 / x + 1 / y := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
