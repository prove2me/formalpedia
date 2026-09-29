-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.quadratic_cap_div_eight_pow_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:51:03.4305+00:00
-- url     : https://prove2.me/submissions/62e74d39-a201-49fe-b49d-05cdac1aa842

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
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Definitions.Def_ErdosProblems_Erdos269_SharpWindowCapR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_OcticEscapeWhole
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

namespace PaperR7
end PaperR7

/-! Complete octic escape statement, including the hypotheses for both named
caps and the automatic zero-cap case. The irrationality target stays open. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open Filter PaperR7 PaperR11 PaperR12
open scoped Topology
end ErdosProblems.Erdos269.PaperCompleteR20

open Filter PaperR7 PaperR11 PaperR12
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR11 in
open ErdosProblems.Erdos269.PaperR12 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (C : ℕ) :
    Tendsto (fun a : ℕ => ((C * (a + 1) ^ 2 : ℕ) : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (8 : ℝ) ^ n)
      atTop (𝓝 0) := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hmul := hshift.const_mul ((C : ℝ) * 8)
  convert hmul using 1
  · funext a
    dsimp
    push_cast
    rw [pow_add]
    field_simp
    <;> ring
  · simp
