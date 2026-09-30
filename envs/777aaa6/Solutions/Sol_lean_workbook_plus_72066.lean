-- Prove2me | solution 1 for lean_workbook_plus_72066
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:41.535457+00:00
-- url     : https://prove2.me/submissions/ee253bd2-98c6-44c1-b3a9-291041285b16

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution {a b c : ℝ} :
    (1 / 2) * ((a - b) ^ 6 + (b - c) ^ 6 + (c - a) ^ 6) +
      2 * (a * b * (a - b) ^ 4 + b * c * (b - c) ^ 4 + c * a * (c - a) ^ 4) +
      (1 / 2) * (a ^ 4 * (b - c) ^ 2 + b ^ 4 * (c - a) ^ 2 + c ^ 4 * (a - b) ^ 2) ≥ 0 := by
  nlinarith only [sq_nonneg ((a - b) ^ 2 * (a + b)),
    sq_nonneg ((b - c) ^ 2 * (b + c)), sq_nonneg ((c - a) ^ 2 * (c + a)),
    sq_nonneg (a ^ 2 * (b - c)), sq_nonneg (b ^ 2 * (c - a)),
    sq_nonneg (c ^ 2 * (a - b))]

#print axioms solution
