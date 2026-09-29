-- Prove2me | solution 1 for lean_workbook_plus_23867
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:22.996849+00:00
-- url     : https://prove2.me/submissions/1fcb0875-8f2d-4632-ad7b-addca1d8fbd0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : 6 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 12 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2) ≥ 8 * (a ^ 3 * b + b ^ 3 * a + a ^ 3 * c + c ^ 3 * a + a ^ 3 * d + d ^ 3 * a + b ^ 3 * c + c ^ 3 * b + b ^ 3 * d + d ^ 3 * b + c ^ 3 * d + d ^ 3 * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
