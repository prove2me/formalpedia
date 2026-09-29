-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.integral_scaled_tail_le_sharpPaperCap
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:08:40.033669+00:00
-- url     : https://prove2.me/submissions/7a05d61d-b496-48db-a3d7-c3f95ef9e193

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_trueNormalizedState_le_carryMajorantQtilde
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

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-! Endpoint composition of the actual constrained majorant. This is an
additional valid escape criterion, not an assertion that escape has been
produced. The original paper cap and its quantifiers are left unchanged.
-/

namespace ErdosProblems.Erdos269.PaperR10
open PaperR7 PaperR8



theorem carryMajorantQtilde_nonneg (n : ℕ) : 0 ≤ carryMajorantQtilde n := by
  unfold carryMajorantQtilde
  positivity
end ErdosProblems.Erdos269.PaperR10

open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution {B a : ℕ} {z : ℤ}
    (hz0 : 0 ≤ z) (hz : (z : ℝ) = (B : ℝ) * trueNormalizedState a) :
    z ≤ (sharpPaperCap B a : ℤ) := by
  have hzabs : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hz0
  have hzabsR : (z.natAbs : ℝ) = (z : ℝ) :=
    congrArg (fun t : ℤ => (t : ℝ)) hzabs
  have hboundR : (z.natAbs : ℝ) ≤
      ((B : ℚ) * carryMajorantQtilde (paperJumpIndex a) : ℚ) := by
    rw [hzabsR, hz]
    push_cast
    exact mul_le_mul_of_nonneg_left (trueNormalizedState_le_carryMajorantQtilde a)
      (Nat.cast_nonneg B)
  have hboundQ : (z.natAbs : ℚ) ≤ (B : ℚ) * carryMajorantQtilde (paperJumpIndex a) := by
    exact_mod_cast hboundR
  have hf : z.natAbs ≤ sharpPaperCap B a := by
    unfold sharpPaperCap
    -- Mathlib/Algebra/Order/Floor/Defs.lean: Nat.le_floor_iff.
    exact (Nat.le_floor_iff
      (mul_nonneg (Nat.cast_nonneg B) (carryMajorantQtilde_nonneg _))).mpr hboundQ
  have hfZ : ((z.natAbs : ℕ) : ℤ) ≤ (sharpPaperCap B a : ℤ) := by exact_mod_cast hf
  simpa only [hzabs] using hfZ
