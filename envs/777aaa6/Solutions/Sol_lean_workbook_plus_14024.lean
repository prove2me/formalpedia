-- Prove2me | solution 1 for lean_workbook_plus_14024
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:55.053304+00:00
-- url     : https://prove2.me/submissions/21173ca0-bc6e-4f04-a5b0-259e221b7437

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) (h : 3 ∣ x) : ∃ a : ℤ, x = 3 * a := by
  (intros; omega)
