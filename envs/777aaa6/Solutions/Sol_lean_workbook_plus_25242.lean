-- Prove2me | solution 1 for lean_workbook_plus_25242
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:54.338552+00:00
-- url     : https://prove2.me/submissions/3a08f447-fb06-4a1a-a672-15db4e76a4da

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 5 / 8 * x + 2 / 5 = 3 / 8 * x + 3 / 5) :
  x = 4 / 5 := by
  (intros; linarith)
