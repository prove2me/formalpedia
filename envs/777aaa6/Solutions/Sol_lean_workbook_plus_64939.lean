-- Prove2me | solution 1 for lean_workbook_plus_64939
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:53.247446+00:00
-- url     : https://prove2.me/submissions/b6915ed2-82e5-466d-a7c8-a07c02e44339

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : y = 60 * x - (2 * x + 24 / 60 * x))
  (h₂ : y = 600) :
  x = 125 / 12 := by
  (intros; linarith)
