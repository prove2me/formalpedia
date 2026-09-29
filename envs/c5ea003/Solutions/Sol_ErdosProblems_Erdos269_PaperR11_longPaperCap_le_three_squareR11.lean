-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR11.longPaperCap_le_three_squareR11
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:54:30.273699+00:00
-- url     : https://prove2.me/submissions/070ae482-319a-4b77-9704-f1362acadc26

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_paperJumpIndex_le_three_mul_r10
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

namespace ErdosProblems.Erdos269.PaperR11
end ErdosProblems.Erdos269.PaperR11

namespace PaperR10
end PaperR10

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-! Narrow long-cap endpoint composition. No historical broad bridge import,
no missing producer, and no alteration of the onset or window conventions. -/

namespace ErdosProblems.Erdos269.PaperR11
open PaperR7 PaperR8 PaperR10



theorem carryMajorantQ_jump_le_three_squareR11 (a : ℕ) :
    carryMajorantQ (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
  have hn : (paperJumpIndex a : ℚ) ≤ 3 * (a : ℚ) := by
    exact_mod_cast paperJumpIndex_le_three_mul_r10 a
  have hn0 : (0 : ℚ) ≤ paperJumpIndex a := Nat.cast_nonneg _
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
  have hprod : (0 : ℚ) ≤
      (3 * (a : ℚ) - paperJumpIndex a) * (3 * (a : ℚ) + paperJumpIndex a) :=
    mul_nonneg (sub_nonneg.mpr hn) (by positivity)
  have hsq : (paperJumpIndex a : ℚ) ^ 2 ≤ 9 * (a : ℚ) ^ 2 := by nlinarith only [hprod]
  unfold carryMajorantQ
  nlinarith only [hsq, hn, hn0, ha0, sq_nonneg (a : ℚ)]
end ErdosProblems.Erdos269.PaperR11

open PaperR7 PaperR8 PaperR10
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR11 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  unfold longPaperCap
  apply Nat.floor_le_of_le
  have h := mul_le_mul_of_nonneg_left (carryMajorantQ_jump_le_three_squareR11 a)
    (Nat.cast_nonneg B : (0 : ℚ) ≤ B)
  push_cast
  nlinarith only [h]
