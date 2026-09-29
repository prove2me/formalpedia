-- Prove2me | solution 1 for lean_workbook_plus_31314
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:27.585015+00:00
-- url     : https://prove2.me/submissions/fa484cce-0c76-48da-a0f3-1ccb438bb12c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b r t : ℝ)
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : a + (k + 1) * r = b)
  (h₂ : 0 ≤ t)
  (h₃ : t ≤ k + 1) :
  a + t * r = a * (k + 1 - t) / (k + 1) + b * t / (k + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (r), sq_nonneg (t), sq_nonneg (a - b), sq_nonneg (a - r), sq_nonneg (a - t), sq_nonneg (b - r), sq_nonneg (b - t), sq_nonneg (r - t), sq_nonneg (a + b), sq_nonneg (a + r), sq_nonneg (a + t), sq_nonneg (b + r), sq_nonneg (b + t), sq_nonneg (r + t)])
