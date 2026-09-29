-- Prove2me | solution 1 for lean_workbook_plus_35511
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:41.321306+00:00
-- url     : https://prove2.me/submissions/7c73576b-7968-46ef-819c-eccc33229577

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a + b = a * b + 1) : a ^ 2 + b ^ 2 ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
