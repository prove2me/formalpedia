-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.sharp_fixed_split_bridge
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:37:53.834984+00:00
-- url     : https://prove2.me/submissions/70b488fd-7f37-436d-9660-69ae28ca5cae

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_integral_scaled_tail_le_sharpPaperCap
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_short_fixed_split_bridge
import Theorems.Thm_ErdosProblems_Erdos269_carryMajorantQtilde_lt_Q
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







theorem carryMajorantQtilde_jump_le_three_square (a : ℕ) :
    carryMajorantQtilde (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
  have hn : (paperJumpIndex a : ℚ) ≤ 3 * (a : ℚ) := by
    exact_mod_cast paperJumpIndex_le_three_mul_r10 a
  have hn0 : (0 : ℚ) ≤ paperJumpIndex a := Nat.cast_nonneg _
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
  have hprod : (0 : ℚ) ≤
      (3 * (a : ℚ) - paperJumpIndex a) * (3 * (a : ℚ) + paperJumpIndex a) :=
    mul_nonneg (sub_nonneg.mpr hn) (by positivity)
  have hsq : (paperJumpIndex a : ℚ) ^ 2 ≤ 9 * (a : ℚ) ^ 2 := by
    nlinarith only [hprod]
  have ha2 : (0 : ℚ) ≤ (a : ℚ) ^ 2 := sq_nonneg _
  have hQ : carryMajorantQ (paperJumpIndex a) ≤ 3 * ((a : ℚ) + 1) ^ 2 := by
    unfold carryMajorantQ
    nlinarith only [hsq, hn, hn0, ha0, ha2]
  exact (carryMajorantQtilde_lt_Q (paperJumpIndex a)).le.trans hQ

theorem sharpPaperCap_le_three_square (B a : ℕ) :
    sharpPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  unfold sharpPaperCap
  apply Nat.floor_le_of_le
  have h := mul_le_mul_of_nonneg_left (carryMajorantQtilde_jump_le_three_square a)
    (Nat.cast_nonneg B : (0 : ℚ) ≤ B)
  push_cast
  nlinarith only [h]

theorem sharpPaperCap_le_short (B a : ℕ) :
    sharpPaperCap B a ≤ 90 * B * (a + 1) ^ 2 := by
  exact (sharpPaperCap_le_three_square B a).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (by decide : 3 ≤ 90)))
end ErdosProblems.Erdos269.PaperR10

open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (sharpPaperCap B a : ℤ) ∧
      sharpPaperCap B a ≤ 90 * B * (a + 1) ^ 2 := by
  intro a ha
  obtain ⟨hc, hp, hr, _⟩ := short_fixed_split_bridge hB hD hval a ha
  have hcap := integral_scaled_tail_le_sharpPaperCap hp.le hc
  exact ⟨hc, by omega, hr, hcap, sharpPaperCap_le_short B a⟩
