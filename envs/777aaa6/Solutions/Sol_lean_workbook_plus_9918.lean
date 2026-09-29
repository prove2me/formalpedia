-- Prove2me | solution 1 for lean_workbook_plus_9918
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:33.129498+00:00
-- url     : https://prove2.me/submissions/397a6993-b6a7-4434-8117-65ac3467ea88

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y a : ℝ) (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) (hxy : x < y) : x / y < (x + a) / (y + a) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (a), sq_nonneg (x - y), sq_nonneg (x - a), sq_nonneg (y - a), sq_nonneg (x + y), sq_nonneg (x + a), sq_nonneg (y + a), mul_pos ha hx, mul_pos ha hy, mul_pos hx hy])
