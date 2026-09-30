-- Prove2me | solution 1 for lean_workbook_plus_34471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:39.896543+00:00
-- url     : https://prove2.me/submissions/a92545f3-97a0-43e3-b234-86b7fff28cda

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

theorem solution (a : ℕ → NNReal) (h : Summable a) :
    Summable (fun k ↦ a k / (1 + k * a k)) := by
  refine NNReal.summable_of_le (fun k => ?_) h
  exact div_le_self (zero_le _) (le_add_of_nonneg_right (zero_le _))

#print axioms solution
