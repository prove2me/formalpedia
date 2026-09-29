-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR12.actual_exact_modulus_pinning
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:58:53.244259+00:00
-- url     : https://prove2.me/submissions/9d68beea-92a7-433c-a499-8fc2d01bbd94

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
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_le_quadratic
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_pos
import Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_modEq
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_window
import Theorems.Thm_ErdosProblems_Erdos269_windowBase235_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR12_exact_modulus_pinning
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

namespace ErdosProblems.Erdos269.PaperR12
end ErdosProblems.Erdos269.PaperR12

namespace PaperR7
end PaperR7

/-!
# Exact-modulus pinning and eventual escape at a fixed start

The precise denominator is the actual window product, not its lower bound
2^len. A nonintegral real (even a nonintegral rational) is separated from the
integers. This yields eventual escape when the relative bound tends to zero.

-/

namespace ErdosProblems.Erdos269.PaperR12
open PaperR7 Filter
open scoped Topology
end ErdosProblems.Erdos269.PaperR12

open PaperR7 Filter
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR12 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (B lo len K : ℕ) (hB : 0 < B)
    (hK : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
      (-((B : ℤ) * actualWindowForcing lo len)) ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)| ≤
      (K : ℝ) / (actualWindowBase lo len : ℝ) := by
  let W : ℤ := actualWindowBase lo len
  let F : ℤ := actualWindowForcing lo len
  let r : ℕ := leastPositiveResidue (Int.natAbs W) (-((B : ℤ) * F))
  have hW : 0 < W := windowBase235_pos lo len
  have hnat : ((Int.natAbs W : ℕ) : ℤ) = W := Int.natAbs_of_nonneg hW.le
  have hnp : 0 < Int.natAbs W := Int.natAbs_pos.mpr hW.ne'
  have hmod : Int.ModEq (Int.natAbs W) (r : ℤ) (-((B : ℤ) * F)) :=
    leastPositiveResidue_modEq hnp _
  have hcong : W ∣ (B : ℤ) * F + (r : ℤ) := by
    obtain ⟨t, ht⟩ : W ∣ -((B : ℤ) * F) - (r : ℤ) := by
      have h := Int.ModEq.dvd hmod
      rwa [hnat] at h
    refine ⟨-t, ?_⟩
    nlinarith only [ht]
  have hwin : (B : ℝ) * trueNormalizedState (lo + len) =
      (W : ℝ) * ((B : ℝ) * trueNormalizedState lo) -
        (((B : ℤ) * F : ℤ) : ℝ) := by
    have h := trueNormalizedState_window lo len
    change trueNormalizedState (lo + len) =
      (W : ℝ) * trueNormalizedState lo - (F : ℝ) at h
    rw [h]
    push_cast
    ring
  have hY0 : 0 ≤ (B : ℝ) * trueNormalizedState (lo + len) :=
    mul_nonneg (Nat.cast_nonneg B) (trueNormalizedState_pos (lo + len)).le
  have hY : (B : ℝ) * trueNormalizedState (lo + len) ≤
      ((B * bridgeWidth (lo + len) : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (trueNormalizedState_le_quadratic (lo + len))
      (show (0 : ℝ) ≤ (B : ℝ) by positivity)
    simpa [bridgeWidth, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] using h
  have hYR : (B : ℝ) * trueNormalizedState (lo + len) ≤ (K : ℝ) :=
    hY.trans (by exact_mod_cast hK)
  have hr0 : (0 : ℝ) ≤ (r : ℤ) := by positivity
  have hrK : ((r : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hres
  exact exact_modulus_pinning hW hwin hcong hY0 hYR hr0 hrK
