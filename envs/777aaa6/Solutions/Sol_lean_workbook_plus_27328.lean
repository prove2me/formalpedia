-- Prove2me | solution 1 for lean_workbook_plus_27328
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:58:45.738159+00:00
-- url     : https://prove2.me/submissions/f73cdc87-601a-49c5-8de8-a6082e7faeea

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c d : ℝ) (ha : a ^ 2 ≤ 1)
    (hb : a ^ 2 + b ^ 2 ≤ 5) (hc : a ^ 2 + b ^ 2 + c ^ 2 ≤ 14)
    (hd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 30) :
    a + b + c + d ≤ 10 := by
  have hw : 12 * a ^ 2 + 6 * b ^ 2 + 4 * c ^ 2 + 3 * d ^ 2 ≤ 120 := by
    linarith
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2),
    sq_nonneg (c - 3), sq_nonneg (d - 4)]
