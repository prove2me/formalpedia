-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.irrational_of_escape_dominating_sharp_cap
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:44:33.848172+00:00
-- url     : https://prove2.me/submissions/c136a7f0-a81e-4086-a17f-84aafd05aa95

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_sharp_fixed_split_bridge
import Theorems.Thm_ErdosProblems_Erdos269_exists_smooth_coprime_split
import Theorems.Thm_ErdosProblems_Erdos269_no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset
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
end ErdosProblems.Erdos269.PaperR10

open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (G : ℕ → ℕ → ℕ)
    (hdom : ∀ B a, 0 < B → sharpPaperCap B a ≤ G B a)
    (hesc : CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G) :
    Irrational paperSeries235 := by
  have hposden : ∀ N : ℤ, ∀ D : ℕ, 0 < D →
      paperSeries235 ≠ (N : ℝ) / (D : ℝ) := by
    intro N D hD hv
    obtain ⟨u, v, w, B, hsplit, hB, hcop⟩ := exists_smooth_coprime_split D hD
    have hbridge := sharp_fixed_split_bridge hB hsplit hv
    apply no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset
      dyadicBlockBase235 dyadicOrderedBlockDigit235 G hesc B hB hcop
      (u + 1 + 2 * v + 3 * w) (paperReducedCarry B)
    · intro a ha
      exact (hbridge a ha).2.2.1
    · intro a ha
      have hp := (hbridge a ha).2.1
      omega
    · intro a ha
      have hp : 0 ≤ paperReducedCarry B a := by
        have := (hbridge a ha).2.1
        omega
      have hcast : ((Int.natAbs (paperReducedCarry B a) : ℕ) : ℤ) =
          paperReducedCarry B a := Int.natAbs_of_nonneg hp
      have huZ := (hbridge a ha).2.2.2.1
      rw [← hcast] at huZ
      have hu : Int.natAbs (paperReducedCarry B a) ≤ sharpPaperCap B a := by
        exact_mod_cast huZ
      exact hu.trans (hdom B a hB)
  -- Same positive-denominator normalisation as the compiled round-7 bridge.
  rw [irrational_iff_ne_rational]
  intro a b hb
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · intro hv
    have hbn : 0 < (-b).toNat := by omega
    have hcast : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
    apply hposden (-a) (-b).toNat hbn
    have hR : (((-b).toNat : ℕ) : ℝ) = -(b : ℝ) := by exact_mod_cast hcast
    rw [hv, hR]
    push_cast
    rw [neg_div_neg_eq]
  · intro hv
    have hbn : 0 < b.toNat := by omega
    have hcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hbpos.le
    apply hposden a b.toNat hbn
    have hR : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hcast
    simpa only [hR] using hv
