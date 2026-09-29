-- Prove2me | solution 1 for lean_workbook_plus_22006
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:21.345735+00:00
-- url     : https://prove2.me/submissions/b62c41bf-acd1-4e05-8586-995e90cdc72c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (d : ℝ)
  (h₀ : d^2 + 4 * d - 140 = 0) :
  (d + 14) * (d - 10) = 0 := by
  (intros; linarith)
