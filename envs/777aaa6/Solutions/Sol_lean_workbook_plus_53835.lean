-- Prove2me | solution 1 for lean_workbook_plus_53835
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:50.770685+00:00
-- url     : https://prove2.me/submissions/5c3be452-b5d0-44d6-9684-9dee4522950e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) : a^2 + b^2 + c^2 + d^2 + e^2 - a * (b + c + d + e) = (a / 2 - b) ^ 2 + (a / 2 - c) ^ 2 + (a / 2 - d) ^ 2 + (a / 2 - e) ^ 2 := by
  (intros; linarith)
