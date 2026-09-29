-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_paper_pinning_and_eight_scale_rigidity
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:16:30.554745+00:00
-- url     : https://prove2.me/theorems/1a029ca6-8d42-4b41-a009-e4c176de9ab0
-- title:
--   Paper pinning and eight scale rigidity
-- statement:
--   The true 2·3·5 normalized state satisfies its digit recurrence and is positive; integrality at one index propagates to all later indices. Fix a natural starting index A. Suppose a second real orbit satisfies the same recurrence from A, and both orbits lie in the interval (digit(n)/base(n), digit(n)/base(n)+width(n)] for every n≥A, where width(n)>0 and width(A+k)/8^k tends to zero. Then the two states agree at A. The widths themselves need not tend to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/EightScaleRigidity.lean#L76-L98
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

namespace PaperR7
end PaperR7

/-!
# Uniqueness for the full printed eight-scale width

The actual radix product grows as `8^k`, uniformly in the starting scale.
Keep that product in the homogeneous recurrence instead of replacing each
radix by two. This admits exactly the paper's `o(8^k)` width condition.
-/


open scoped BigOperators
open PaperR7

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A) := by sorry
