-- Prove2me | solution 1 for lean_workbook_plus_9397
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:58.233378+00:00
-- url     : https://prove2.me/submissions/bd4686c2-07f9-4562-b343-7173c0a63af2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) ≥ (a * b + b * c + a * c) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
