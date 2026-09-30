-- Prove2me | solution 1 for lean_workbook_plus_25993
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:08:34.883648+00:00
-- url     : https://prove2.me/submissions/dcf247f8-175b-4e24-9c6c-cf6cbda07f84

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c d : ℝ) :
    (b + d) * (c + a) * (a * c * d + a * b * d + b * c * a + b * d * c) -
      4 * (a + b + c + d) * (a * b * c * d) =
    (b - d) ^ 2 * a ^ 2 * c + (a - c) ^ 2 * b * d ^ 2 +
      (d - b) ^ 2 * c ^ 2 * a + (c - a) ^ 2 * b ^ 2 * d := by
  calc
    (b + d) * (c + a) * (a * c * d + a * b * d + b * c * a + b * d * c) -
        4 * (a + b + c + d) * (a * b * c * d) =
      (b - d) ^ 2 * a * c * (a + c) + (a - c) ^ 2 * b * d * (b + d) := by ring
    _ = (b - d) ^ 2 * a ^ 2 * c + (a - c) ^ 2 * b * d ^ 2 +
      (d - b) ^ 2 * c ^ 2 * a + (c - a) ^ 2 * b ^ 2 * d := by ring
