-- Prove2me | solution 1 for lean_workbook_plus_50236
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:56.088301+00:00
-- url     : https://prove2.me/submissions/211c5059-ffc0-4365-bcb5-755c9adf6dc5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s t u v : ℝ)
  (h₀ : 0 ≤ s ∧ 0 ≤ t)
  (h₁ : 0 < u ∧ 0 < v)
  (h₂ : s ≥ t)
  (h₃ : u ≥ v) :
  s * u - t * v ≥ 0 := by
  (intros; nlinarith [sq_nonneg (s), sq_nonneg (t), sq_nonneg (u), sq_nonneg (v), sq_nonneg (s - t), sq_nonneg (s - u), sq_nonneg (s - v), sq_nonneg (t - u), sq_nonneg (t - v), sq_nonneg (u - v), sq_nonneg (s + t), sq_nonneg (s + u), sq_nonneg (s + v), sq_nonneg (t + u), sq_nonneg (t + v), sq_nonneg (u + v)])
