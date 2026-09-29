-- Prove2me | solution 1 for lean_workbook_plus_4804
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:38.002471+00:00
-- url     : https://prove2.me/submissions/1fdf03aa-3bcd-4363-898d-4952c1f855ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (a + b) * (b + c) * (c + a) = (a + b + c) * (a * b + b * c + c * a) - a * b * c := by
  (intros; linarith)
