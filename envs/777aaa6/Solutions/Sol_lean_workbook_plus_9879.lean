-- Prove2me | solution 1 for lean_workbook_plus_9879
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:30.493499+00:00
-- url     : https://prove2.me/submissions/f051578e-5ecd-42ba-892d-bb9eb778684c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (u : ℝ)
  (h₀ : 0 ≤ 2 * x + 19)
  (h₁ : u = Real.sqrt (2 * x + 19))
  (h₂ : 2 * u^2 - 14 * u + 21 = 0) :
  u^2 - 7 * u + 21 / 2 = 0 := by
  (intros; linarith)
