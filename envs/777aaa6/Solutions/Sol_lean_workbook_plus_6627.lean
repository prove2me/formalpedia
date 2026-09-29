-- Prove2me | solution 1 for lean_workbook_plus_6627
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:21.74103+00:00
-- url     : https://prove2.me/submissions/ad29c765-78e2-48ec-8f08-aa761eaab21d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : 3 * x + 3 * y = 120)
  (h₂ : x + y = 40) :
  x * y ≤ 400 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
