-- Prove2me | solution 1 for lean_workbook_plus_51037
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:27.419379+00:00
-- url     : https://prove2.me/submissions/dd9488e0-de5e-4491-b85e-dbc627a01d15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w x y z : ℝ) (h₁ : w + 4*x + 9*y + 16*z = 6) (h₂ : 4*w + 9*x + 16*y + 25*z = 7) (h₃ : 9*w + 16*x + 25*y + 36*z = 12) : w + x + y + z = 2 := by
  (intros; linarith)
