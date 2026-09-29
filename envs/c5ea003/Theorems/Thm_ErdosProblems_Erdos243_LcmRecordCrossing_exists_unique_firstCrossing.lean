-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_exists_unique_firstCrossing
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.exists_unique_firstCrossing
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:53:43.857453+00:00
-- url     : https://prove2.me/theorems/1cb9dc38-6dbb-46ee-bb53-7cb9d6cc2cd0
-- title:
--   A reached height has one first crossing
-- statement:
--   If U_0<t and some U_j reaches t by time N, then exactly one n<N is a first crossing: U_(n+1)≥t and every U_i for i≤n is below t. U may fall at other times.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L95-L125
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

theorem ErdosProblems.Erdos243.LcmRecordCrossing.exists_unique_firstCrossing (U : ℕ → ℕ) (t N : ℕ)
    (hzero : U 0 < t) (hN : ∃ j ≤ N, t ≤ U j) :
    ∃! n, n < N ∧ FirstCrossing U t n := by sorry
