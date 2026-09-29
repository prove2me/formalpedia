-- Prove2me | solution 1 for lean_workbook_plus_37482
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:37:34.69678+00:00
-- url     : https://prove2.me/submissions/192b5e6e-f7de-4f05-878d-0f645d1117b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (2 * a) ^ 2 + (b ^ 2 + 1) ^ 2 + (2 * c) ^ 2 - 1 = 4 * a ^ 2 + b ^ 4 + 2 * b ^ 2 + 4 * c ^ 2 := by
  (intros; linarith)
