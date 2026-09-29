-- Prove2me | solution 1 for lean_workbook_plus_17585
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:15.178175+00:00
-- url     : https://prove2.me/submissions/f437dfec-6c0c-4314-b68b-8465f3039978

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - a * c) = a^3 + b^3 + c^3 - 3 * a * b * c := by
  (intros; linarith)
