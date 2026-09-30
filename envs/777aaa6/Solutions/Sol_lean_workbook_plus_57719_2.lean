-- Prove2me | solution 2 for lean_workbook_plus_57719
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:52.485324+00:00
-- url     : https://prove2.me/submissions/b03cf951-fe4e-4dbf-bd8d-d6af27d6de2c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ)
  (h₀ : a = 1)
  (h₁ : b = 25)
  (h₂ : c = 17)
  (h₃ : d = 81) :
  (a + b + c + d) / 4 = 31 := by
  (intros; linarith)
