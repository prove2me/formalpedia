-- Prove2me | solution 1 for lean_workbook_plus_38958
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:17.851884+00:00
-- url     : https://prove2.me/submissions/be9b334e-c16a-440b-b8d6-ad72e41dcbc8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h1 : a + b = 1) (h2 : a >= 0 ∧ b >= 0) : a * b <= 1 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
