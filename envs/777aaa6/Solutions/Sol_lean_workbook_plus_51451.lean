-- Prove2me | solution 1 for lean_workbook_plus_51451
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:40.813965+00:00
-- url     : https://prove2.me/submissions/cee65611-2124-4505-8880-7fabf7bca0c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s t u v : ℝ) (hr : r ≥ s) (hs : s ≥ t) (ht : t ≥ u) (hu : u ≥ v) : r^2 - s^2 + t^2 - u^2 + v^2 ≥ (r - s + t - u + v)^2 := by
  (intros; nlinarith [sq_nonneg (r), sq_nonneg (s), sq_nonneg (t), sq_nonneg (u), sq_nonneg (r - s), sq_nonneg (r - t), sq_nonneg (r - u), sq_nonneg (s - t), sq_nonneg (s - u), sq_nonneg (t - u), sq_nonneg (r + s), sq_nonneg (r + t), sq_nonneg (r + u), sq_nonneg (s + t), sq_nonneg (s + u), sq_nonneg (t + u)])
