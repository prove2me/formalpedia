-- Prove2me | solution 1 for lean_workbook_plus_27186
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:56.098492+00:00
-- url     : https://prove2.me/submissions/45dbf9b5-a49e-4ed7-8178-66dd0dd4fbd8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x = 1 / 42 + 1 / 48 + 1 / 40) :
  4 / 50 - x = 29 / 2800 := by
  (intros; linarith)
