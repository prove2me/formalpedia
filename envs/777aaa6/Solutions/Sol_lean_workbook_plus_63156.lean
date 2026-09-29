-- Prove2me | solution 1 for lean_workbook_plus_63156
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:41.75928+00:00
-- url     : https://prove2.me/submissions/b0bd08a4-1304-4f5a-b513-3ce4af0aed02

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a / (a + b) + b / (a + b) + c / (a + b) = (a + b + c) / (a + b) := by
  (intros; ring)
