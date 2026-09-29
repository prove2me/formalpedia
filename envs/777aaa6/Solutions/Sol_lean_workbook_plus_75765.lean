-- Prove2me | solution 1 for lean_workbook_plus_75765
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:31.120792+00:00
-- url     : https://prove2.me/submissions/f6b6c6ed-aceb-4d39-89de-731c24bde0f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 17 / 20 * x - 90 = 3 / 4 * x - 15) :
  x = 750 := by
  (intros; linarith)
