-- Prove2me | solution 1 for lean_workbook_plus_64101
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:12.31917+00:00
-- url     : https://prove2.me/submissions/c8d5d469-c62d-426b-840a-a1f1c505b41e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x = 150000) :
  3/4 * x = 150000 * 3/4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
