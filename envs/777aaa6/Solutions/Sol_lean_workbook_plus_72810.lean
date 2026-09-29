-- Prove2me | solution 1 for lean_workbook_plus_72810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:16.70881+00:00
-- url     : https://prove2.me/submissions/6be751f0-c7b2-45ec-8eda-9a40aaeb9f74

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w : ℝ)
  (h₀ : u + v + w = 1) :
  u * v + v * w + w * u ≤ 1 / 3 := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (w), sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w), sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (v + w)])
