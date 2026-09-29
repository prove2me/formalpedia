-- Prove2me | solution 1 for lean_workbook_plus_13584
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:44.828212+00:00
-- url     : https://prove2.me/submissions/293c163d-cc15-4c0f-a619-fbd6a0e6e491

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℤ) : q^2 * (q^2 - 3 * p^2)^2 + p^2 * (3 * q^2 - p^2)^2 = (p^2 + q^2)^3 := by
  (intros; linarith)
