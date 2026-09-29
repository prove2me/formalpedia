-- Prove2me | solution 1 for lean_workbook_plus_4427
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:03.429826+00:00
-- url     : https://prove2.me/submissions/173c9356-7bec-43d5-9b32-4b8349b64715

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a + d = b + c) :
  (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
