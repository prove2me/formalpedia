-- Prove2me | solution 1 for lean_workbook_plus_21103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:30.838996+00:00
-- url     : https://prove2.me/submissions/98e9b5a5-395e-4e5c-9ce8-b4da3041689f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : 4 * s * t ≤ (s + t) ^ 2 := by
  (intros; nlinarith [sq_nonneg (s), sq_nonneg (t), sq_nonneg (s - t), sq_nonneg (s + t), mul_pos hs ht])
