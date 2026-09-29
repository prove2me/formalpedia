-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_crossed_progression_spacing
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_spacing
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:51:40.125705+00:00
-- url     : https://prove2.me/theorems/22cff5d2-1e4d-464c-afcd-7c6e9f491d94
-- title:
--   Progression wall count controls a jump's width
-- statement:
--   For a nonempty finite set s, suppose U<x+kP≤U+d for every k in s. Then (|s|−1)P<d, even if s omits intermediate progression indices.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L166-L186
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

theorem ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_spacing (s : Finset ℕ) (hs : s.Nonempty)
    (x P U d : ℕ)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d) :
    (s.card - 1) * P < d := by sorry
