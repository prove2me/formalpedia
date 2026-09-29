-- Prove2me | solution 1 for lean_workbook_plus_24592
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:02.008656+00:00
-- url     : https://prove2.me/submissions/38a57859-0dec-40ab-b59d-a9e03c7a88f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x * y = 6) (h₂ : 2 < x) (h₃ : 2 < y) : x + y < 5 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
