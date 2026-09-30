-- Prove2me | solution 1 for lean_workbook_plus_68452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:56.882851+00:00
-- url     : https://prove2.me/submissions/42ea7f19-5b55-4130-be44-791747d62808

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) :
    (b ^ 2 + c ^ 2 - a ^ 2) * (b - c) ^ 2 +
      (-b ^ 2 + a ^ 2 + c ^ 2) * (c - a) ^ 2 +
      (b ^ 2 + a ^ 2 - c ^ 2) * (a - b) ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg ((a - b) * (a + b - c)),
    sq_nonneg ((b - c) * (b + c - a)), sq_nonneg ((c - a) * (c + a - b))]
