-- Prove2me | solution 1 for lean_workbook_plus_73424
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:22.356329+00:00
-- url     : https://prove2.me/submissions/80520ec5-003d-46da-bee3-bda0e00a7f61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥
      3 * a * b * c * (a + b + c) := by
  nlinarith only [sq_nonneg (a ^ 2 - b * c), sq_nonneg (b ^ 2 - c * a),
    sq_nonneg (c ^ 2 - a * b), sq_nonneg (a * b - b * c),
    sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
