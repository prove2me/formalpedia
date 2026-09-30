-- Prove2me | solution 1 for lean_workbook_plus_79750
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:06.108202+00:00
-- url     : https://prove2.me/submissions/a9e2fa6e-ed76-49eb-9172-f5124542fe79

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (a * b - a * c),
    sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c)]
