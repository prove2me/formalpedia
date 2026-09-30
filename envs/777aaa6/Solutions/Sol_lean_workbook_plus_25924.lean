-- Prove2me | solution 1 for lean_workbook_plus_25924
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:08:18.447633+00:00
-- url     : https://prove2.me/submissions/bef58857-de9a-4b9c-bec0-22bfc19cf58c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

lemma source_symmetric (a b c : ℝ) :
    2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) -
      3 * (a ^ 3 * b + b ^ 3 * a + b ^ 3 * c + c ^ 3 * b + c ^ 3 * a + a ^ 3 * c) ≥ 0 := by
  nlinarith only [sq_nonneg ((a - b) * (2 * a + 2 * b - 3 * c)),
    sq_nonneg ((b - c) * (2 * b + 2 * c - 3 * a)),
    sq_nonneg ((c - a) * (2 * c + 2 * a - 3 * b)),
    sq_nonneg (c * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (b * (c - a))]

theorem solution {a b c : ℝ} :
    2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) -
      3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) ≥ 0 := by
  nlinarith only [sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c),
    sq_nonneg (c ^ 2 - c * a), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
    sq_nonneg (c ^ 2), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
