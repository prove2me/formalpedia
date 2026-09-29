-- Prove2me | solution 1 for lean_workbook_plus_5559
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:42.197994+00:00
-- url     : https://prove2.me/submissions/346f5bec-69df-4b7b-bfe5-b091d27fdc37

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  10 * (a^3 + b^3 + c^3) * (a + b + c)^2 - 9 * (a^5 + b^5 + c^5) =
    (a + b + c)^5 + (15 / 2) * (a + b) * (a + c) * (b + c) * ((a - b)^2 + (a - c)^2 + (b - c)^2) := by
  (intros; linarith)
