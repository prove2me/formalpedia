-- Prove2me | solution 1 for lean_workbook_plus_26332
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:16.805634+00:00
-- url     : https://prove2.me/submissions/3171dd03-f40b-42a4-b4c5-a97b2e0f9e6a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c d : ℝ) :
    (7 / 16) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥
    d ^ 2 * a ^ 2 + c ^ 2 * a ^ 2 + a ^ 2 * b ^ 2 +
      b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + b ^ 2 * d ^ 2 + a * b * c * d := by
  nlinarith only [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2),
    sq_nonneg (a ^ 2 - d ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
    sq_nonneg (a * b - c * d)]
