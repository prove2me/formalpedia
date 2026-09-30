-- Prove2me | solution 1 for lean_workbook_plus_78959
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:24.916439+00:00
-- url     : https://prove2.me/submissions/ac05989d-8bd5-41fd-8b53-29b3fecce45f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (k : ℝ) (h₀ : k = a + b + c) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a + a + b + c) ≥ -3 := by
  nlinarith only [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
