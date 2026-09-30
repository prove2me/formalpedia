-- Prove2me | solution 1 for lean_workbook_plus_37353
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:31.618974+00:00
-- url     : https://prove2.me/submissions/336ec72c-c4ef-480a-aee3-c380a918eaca

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

theorem solution (a : ℕ → ℝ) (ha : ∀ i, a i > 0) (h : Summable a) :
    Summable (λ i => a i / (a i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h
  · exact div_nonneg (ha i).le (add_pos (ha i) zero_lt_one).le
  · exact div_le_self (ha i).le (le_add_of_nonneg_left (ha i).le)

#print axioms solution
