-- Prove2me | solution 1 for lean_workbook_plus_37086
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:21.77226+00:00
-- url     : https://prove2.me/submissions/389ab42b-7710-489f-bf5c-cbd74e902520

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + 6 * a * b * c + 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) := by
  (intros; linarith)
