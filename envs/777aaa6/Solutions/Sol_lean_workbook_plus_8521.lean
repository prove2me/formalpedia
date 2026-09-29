-- Prove2me | solution 1 for lean_workbook_plus_8521
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:15.079641+00:00
-- url     : https://prove2.me/submissions/ed7b1399-566d-43bc-83dc-7aff4d3a5d46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4) → (a + b + c) * (a + b - c) * (a + c - b) * (b + c - a) > 0 := by
  (intros; linarith)
