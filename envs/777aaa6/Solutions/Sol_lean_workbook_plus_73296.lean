-- Prove2me | solution 1 for lean_workbook_plus_73296
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:57.410732+00:00
-- url     : https://prove2.me/submissions/02510762-219a-4dd6-9204-923960ba76b4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) :
    7 * (a ^ 6 + b ^ 6 + c ^ 6) + 21 * a ^ 2 * b ^ 2 * c ^ 2 ≥
      14 * (a ^ 4 * b * c + b ^ 4 * c * a + c ^ 4 * a * b) := by
  nlinarith [sq_nonneg (a ^ 3 - a * b * c), sq_nonneg (b ^ 3 - a * b * c),
    sq_nonneg (c ^ 3 - a * b * c)]
