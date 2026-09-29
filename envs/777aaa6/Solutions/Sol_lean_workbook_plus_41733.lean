-- Prove2me | solution 1 for lean_workbook_plus_41733
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:30:04.591758+00:00
-- url     : https://prove2.me/submissions/1bae5f12-663e-46a5-b018-2fd1669fd08e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ≤ 1) :
  1 / x ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
