-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_WeightAnalysis_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR8_WeightAnalysis_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:30:00.211896+00:00
-- url     : https://prove2.me/theorems/ec391da8-5fdb-4eda-b6ac-0e8322a3d235
-- title:
--   Integer height weights and divergent integral
-- statement:
--   For f:R→R, defines the sampled weight w_n=f(max(1,n)). Defines divergent improper integral to mean that integral_1^x f(t) dt tends to +infinity as x tends to +infinity. The transfer from integral divergence to nonsummability requires the nonnegative nonincreasing hypotheses stated in the separate lemmas.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR8/WeightAnalysis.lean#L1-L177
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR8_WeightAnalysis_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR8.WeightAnalysis.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The analytic part of the weighted-record assembly

Compiled round-8 candidates. No assumed divergence of sampled weights is
left in the paper-facing theorem. Its source is the displayed improper
integral and antitonicity on `[1, infinity)`.

Pinned source checks:
* Analysis/SumIntegralComparisons.lean: AntitoneOn.integral_le_sum.
* Topology/Algebra/InfiniteSum/Real.lean: summable_of_sum_range_le.
* Topology/Algebra/InfiniteSum/NatInt.lean: summable_nat_add_iff.
* Algebra/BigOperators/Group/Finset/Basic.lean: sum_range_add, sum_range_succ.
* Topology/Algebra/InfiniteSum/Order.lean: Summable.sum_le_tsum.
* Algebra/Order/BigOperators/Group/Finset.lean: sum_le_sum,
  sum_le_sum_of_subset_of_nonneg.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter MeasureTheory
open scoped BigOperators

/-- Restriction to natural heights, with a harmless constant value at zero. -/
noncomputable def heightWeight (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  f (max 1 (n : ℝ))

/-- Improper integral divergence, without assigning `tsum` or a Bochner
integral its default value on a nonintegrable function. -/
def DivergentIntegral (f : ℝ → ℝ) : Prop :=
  Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop

















end ErdosProblems.Erdos243.PaperCompleteR8


