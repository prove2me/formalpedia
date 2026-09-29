-- Prove2me | solution 1 for lean_workbook_plus_27393
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:03:53.715084+00:00
-- url     : https://prove2.me/submissions/dae731b5-4874-4d2a-894a-2bbb48dc7b9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₀ : x ≠ 0) (h₁ : x * y = 1) : y = 1 / x := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
