-- Prove2me | solution 1 for lean_workbook_plus_30398
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:07.989298+00:00
-- url     : https://prove2.me/submissions/018a5f79-c790-4480-8aef-7448de10347d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y : ℝ) (ha : a ≠ 0) : y = -(x^2 + 2*b*x + c)/(2*a) ↔ y = -(1/(2*a)) * ((x + b)^2 + (c - b^2)) := by
  (intros; ring)
