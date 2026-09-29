-- Prove2me | solution 1 for lean_workbook_plus_32535
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:46.381019+00:00
-- url     : https://prove2.me/submissions/13b4fa78-de4b-41ff-9b3b-7aea095fb17d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) : (u + v) * (v + w) * (w + u) ≥ 8 * u * v * w := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (w), sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w), sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (v + w)])
