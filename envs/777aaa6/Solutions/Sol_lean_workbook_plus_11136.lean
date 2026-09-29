-- Prove2me | solution 1 for lean_workbook_plus_11136
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:33.410326+00:00
-- url     : https://prove2.me/submissions/90b47da7-a5b7-47af-9fca-a37006cddfb4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 + 2 * a * b) * (a^2 + 2 * b^2 - 2 * a * b) := by
  (intros; linarith)
