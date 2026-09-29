-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_actual_weighted_strip_decomposition
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:53:47.511497+00:00
-- url     : https://prove2.me/theorems/b21416ff-33fc-4382-b294-02b9e7d103c3
-- title:
--   Actual weighted strip decomposition
-- statement:
--   For any finite integer-coefficient shift, the shifted numerator divided by 15 is an exact sum over the points that first enter each nested literal triangle, weighted by the later coefficients and phase factors.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/PhaseStripDecomposition.lean#L131-L163
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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_PhaseStripDecomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The printed integer-floor weights and their exact crossing factors. -/


open scoped BigOperators

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r) := by sorry
