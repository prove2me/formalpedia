-- Prove2me | solution 1 for lean_workbook_plus_66494
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:23.839453+00:00
-- url     : https://prove2.me/submissions/2cd50b4a-2620-446c-9c5d-df43c58c8ff8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s t : ℝ) : (r * s) ^ 2 + (s * t) ^ 2 + (r * t) ^ 2 ≥ (r + s + t) * (r * s * t) := by
  (intros; nlinarith [sq_nonneg (r), sq_nonneg (s), sq_nonneg (t), sq_nonneg (r - s), sq_nonneg (r - t), sq_nonneg (s - t), sq_nonneg (r + s), sq_nonneg (r + t), sq_nonneg (s + t)])
