-- Prove2me | solution 1 for lean_workbook_plus_67561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:45.273722+00:00
-- url     : https://prove2.me/submissions/5e572734-8399-403b-82ab-923ff3e1bb6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : (x - 9) / 3 = 43)
  (h₁ : (x - 3) / 9 = 15) :
  x = 138 := by
  (intros; linarith)
