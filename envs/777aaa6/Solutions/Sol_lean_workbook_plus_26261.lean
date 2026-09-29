-- Prove2me | solution 1 for lean_workbook_plus_26261
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:54.089426+00:00
-- url     : https://prove2.me/submissions/fb55d4ca-90d3-40ae-9f21-0e34e5340e2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (α β : ℂ) (h : α * β = 0) : α = 0 ∨ β = 0 := by
  (intros; simp_all)
