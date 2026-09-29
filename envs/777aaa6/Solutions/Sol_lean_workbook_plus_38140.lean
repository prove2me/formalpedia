-- Prove2me | solution 1 for lean_workbook_plus_38140
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:37.236167+00:00
-- url     : https://prove2.me/submissions/d27b55a7-4769-4263-8a1f-10d06e2fd989

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : 2 * (b + c) ^ 2 ≤ 4 * (b ^ 2 + c ^ 2) := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
