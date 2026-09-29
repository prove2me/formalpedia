-- Prove2me | solution 1 for lean_workbook_plus_27810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:26.890649+00:00
-- url     : https://prove2.me/submissions/544e6fbd-f7cc-4771-8c45-25eba517efb6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ a b c d : ℝ,
    4 * (a - c)^2 * (c + a)^2 + 4 * (b - d)^2 * (b + d)^2 =
    (b^2 - d^2 - a^2 + c^2)^2 + (c^2 - a^2 - b^2 + d^2)^2 +
    (a^2 - b^2 - c^2 + d^2)^2 + (a^2 - c^2 - d^2 + b^2)^2 := by
  (intros; linarith)
