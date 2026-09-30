-- Prove2me | solution 1 for lean_workbook_plus_26681
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:01:54.082595+00:00
-- url     : https://prove2.me/submissions/7c6a36e6-cc22-456a-929b-9f3751ab55c5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) :
    4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 =
    (a - b + c) * (a + b - c) * (b + c - a) * (b + c + a) := by
  calc
    4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 =
        ((b + c) ^ 2 - a ^ 2) * (a ^ 2 - (b - c) ^ 2) := by ring
    _ = (a - b + c) * (a + b - c) * (b + c - a) * (b + c + a) := by ring
