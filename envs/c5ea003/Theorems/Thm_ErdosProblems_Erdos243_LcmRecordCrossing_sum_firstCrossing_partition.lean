-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_sum_firstCrossing_partition
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.sum_firstCrossing_partition
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T23:01:00.043154+00:00
-- url     : https://prove2.me/theorems/793049d1-7ef5-4b72-adbc-ce5fd518e45d
-- title:
--   Finite weights partition by first-crossing time
-- statement:
--   For a finite set of target heights t_k all above U_0 and reached by time N, and arbitrary real weights w_k, the sum Σ_k w_k equals the sum over n<N and k of w_k when n is the first crossing of t_k and zero otherwise.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L134-L164
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

namespace LcmRecordExcess
end LcmRecordExcess

/-!
# Counting the CRT heights crossed by one arithmetic step

The heights are the actual arithmetic progression `x + k * P`, not an
assumed cardinality bound. This supplies the finite local charging step in
the weighted-record argument of `LcmRecordExcess.md`. First-crossing existence,
uniqueness, and the finite partition across time require no monotonicity of
the numerator sequence. The existing CRT construction supplies the covering
from any finite family of sufficiently large pairwise-coprime old divisors.
Producing that family from an infinite canonical orbit and the analytic
divergence argument are not asserted by this module.
-/


open LcmRecordExcess

open ErdosProblems.Erdos243.LcmRecordCrossing

open ErdosProblems.Erdos243.LcmRecordExcess

theorem ErdosProblems.Erdos243.LcmRecordCrossing.sum_firstCrossing_partition (s : Finset ℕ) (U t : ℕ → ℕ)
    (N : ℕ) (w : ℕ → ℝ)
    (hzero : ∀ k ∈ s, U 0 < t k)
    (hN : ∀ k ∈ s, ∃ j ≤ N, t k ≤ U j) :
    ∑ k ∈ s, w k =
      ∑ n ∈ Finset.range N, ∑ k ∈ s,
        if FirstCrossing U (t k) n then w k else 0 := by sorry
