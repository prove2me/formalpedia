-- Prove2me | solution 1 for lean_workbook_plus_38963
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:23.718794+00:00
-- url     : https://prove2.me/submissions/f170cb58-7d15-42e4-82d7-a102fbbfbe83

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a : ℝ)
  (u v : ℝ)
  (h₀ : u = Real.sqrt (x + a))
  (h₁ : v = Real.sqrt (x - a))
  (h₂ : 0 ≤ x + a)
  (h₃ : 0 ≤ x - a) :
  u^2 - v^2 = 2 * a := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x + a by positivity), Real.sq_sqrt (show (0:ℝ) ≤ x - a by positivity), Real.sqrt_nonneg (x + a), Real.sqrt_nonneg (x - a), sq_nonneg (x), sq_nonneg (a), sq_nonneg (u), sq_nonneg (v), sq_nonneg (x - a), sq_nonneg (x - u), sq_nonneg (x - v), sq_nonneg (a - u), sq_nonneg (a - v), sq_nonneg (u - v), sq_nonneg (x + a), sq_nonneg (x + u), sq_nonneg (x + v), sq_nonneg (a + u), sq_nonneg (a + v), sq_nonneg (u + v)])
