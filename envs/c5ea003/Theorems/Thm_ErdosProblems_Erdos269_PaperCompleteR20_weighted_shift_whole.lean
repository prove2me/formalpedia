-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_weighted_shift_whole
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.weighted_shift_whole
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T22:59:55.585987+00:00
-- url     : https://prove2.me/theorems/992f57b7-e40d-4489-99f3-9c17dbc8e69f
-- title:
--   Weighted shift whole
-- statement:
--   Every finite integer-coefficient weighted shift of the 2·3·5 paper series has phase factors in {1,1/3,1/5,1/15}, integral numerator and correction terms, an absolutely convergent exact shifted-series identity, and a quadratic numerator bound. A stated dominance condition on its last nonzero coefficient makes the leading coefficient nonzero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/WeightedShiftValue.lean#L218-L236
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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Module.FiniteDimension
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

-- `Summable.norm` (the alias of `summable_norm_iff`) no longer arrives transitively on Lean 4.30.0
-- / Mathlib c5ea0035, and dot notation no longer resolves it because `Summable` now unfolds to
-- `Exists`. Imported explicitly and applied by name below. Statements are unchanged.
namespace PaperR7
end PaperR7

/-!
# Weighted shifts of the literal series

Finite linear combinations of shifted digits retain the original value
with an integer prefix correction. All sums below converge absolutely.
-/


open PaperR7
open scoped BigOperators

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperCompleteR20.weighted_shift_whole (c : ℕ → ℤ) (σ r : ℕ) :
    (∀ a t, shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15) ∧
    (∀ a, ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ)) ∧
    (∃ z : ℤ, shiftedCorrection c σ r = (z : ℝ)) ∧
    HasSum (fun a : ℕ => shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ))
      ((shiftedLeading c σ r : ℝ) * (paperSeries235 / 2) - shiftedCorrection c σ r) ∧
    Summable (fun a : ℕ => |shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ)|) ∧
    (∀ a, |shiftedNumerator c σ r a| ≤
      shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ J : ℕ, J ≤ σ → (∀ j, J < j → j ≤ σ → c j = 0) →
      (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)| →
      shiftedLeading c σ r ≠ 0) := by sorry
