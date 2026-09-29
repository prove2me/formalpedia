-- Prove2me | solution 1 for lean_workbook_plus_22977
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:59.398098+00:00
-- url     : https://prove2.me/submissions/492f3271-f036-4a04-801d-74891465f2e4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n k : ℤ)
  (h₀ : n^2 - 19 * n + 99 = k^2) :
  (2 * k)^2 - (2 * n - 19)^2 = 35 := by
  (intros; linarith)
