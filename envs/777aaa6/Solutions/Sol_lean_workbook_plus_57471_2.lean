-- Prove2me | solution 2 for lean_workbook_plus_57471
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:14.377099+00:00
-- url     : https://prove2.me/submissions/bf46a723-0586-42d7-89ee-272b43ef5be1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ≥ a * b * c + b * c * d + c * d * a + d * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
