-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_PhaseStripDecomposition
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_PhaseStripDecomposition
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:19:41.310523+00:00
-- url     : https://prove2.me/theorems/7df938b2-bf50-456b-9e9c-04fc671cc09d
-- title:
--   PhaseStripDecomposition
-- statement:
--   Defines prime-channel floor phases, phase weights, shift carries and their correction factor, and the four coefficients of a cubic finite difference.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/PhaseStripDecomposition.lean#L1-L221
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

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

noncomputable def phaseFloor (p a : ℕ) (t : ℝ) : ℤ :=
  ⌊((a : ℝ) + t) * triangleTheta p⌋

noncomputable def phaseOmega (a : ℕ) (t : ℝ) : ℝ :=
  (3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
    (5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t)

noncomputable def phaseCarry (p a : ℕ) (t : ℝ) (u : ℕ) : ℤ :=
  phaseFloor p (a + u) t - phaseFloor p a t - phaseFloor p u 0

noncomputable def phaseChi (a : ℕ) (t : ℝ) (u : ℕ) : ℝ :=
  (3 : ℝ) ^ (-phaseCarry 3 a t u) * (5 : ℝ) ^ (-phaseCarry 5 a t u)























def cubicShiftCoefficient : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1




end ErdosProblems.Erdos269.PaperCompleteR20


