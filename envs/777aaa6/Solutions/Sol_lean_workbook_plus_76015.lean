-- Prove2me | solution 1 for lean_workbook_plus_76015
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:44.729191+00:00
-- url     : https://prove2.me/submissions/1d7be888-62a2-4182-9f6b-b85d8a7823ad

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
    2 * a ^ 2 * d ^ 2 + 2 * b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 ≥
      a ^ 2 * c * d + a * b * d ^ 2 + a * b * c ^ 2 + b ^ 2 * c * d +
        2 * a * b * c * d := by
  nlinarith [sq_nonneg ((a - b) * (c - d)), sq_nonneg (a * c - b * d),
    sq_nonneg (a * d - b * c)]
