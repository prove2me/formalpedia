-- Prove2me | solution 1 for lean_workbook_plus_17003
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:22.478707+00:00
-- url     : https://prove2.me/submissions/16c2317c-da66-4425-86a9-82cf440f01bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d: ℤ) (h : (a+b)^2 - (a^2 + b^2) = (c+d)^2 - (c^2 + d^2)) : a * b = c * d := by
  (intros; linarith)
