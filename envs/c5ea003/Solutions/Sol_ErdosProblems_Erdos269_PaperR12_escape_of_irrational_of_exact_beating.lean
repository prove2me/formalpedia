-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR12.escape_of_irrational_of_exact_beating
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:00:14.080569+00:00
-- url     : https://prove2.me/submissions/18416b3a-70fc-4665-bb78-073acee58c9b

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
import Theorems.Thm_ErdosProblems_Erdos269_exists_dist_lower_bound_of_irrational
import Theorems.Thm_ErdosProblems_Erdos269_irrational_trueNormalizedState
import Theorems.Thm_ErdosProblems_Erdos269_windowBase235_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR12_actual_exact_modulus_pinning
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
theorem solution
    (h : Irrational (dyadicShellTsumTailR235 1)) (G : ℕ → ℕ → ℕ)
    (hbeat : ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ len : ℕ, 0 < len ∧
        ((max (G B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ) /
          (actualWindowBase lo len : ℝ) < ε) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G := by
  intro B hB _hcop lo₀
  classical
  set lo : ℕ := lo₀ + 1 with hlo
  obtain ⟨δ, hδ, hgap⟩ := exists_dist_lower_bound_of_irrational
    ((irrational_trueNormalizedState h lo (by omega)).natCast_mul
      (m := B) (by omega))
  obtain ⟨len, hlen, hlt⟩ := hbeat B lo hB δ hδ
  refine ⟨lo, len, by omega, hlen,
    Int.natAbs_pos.mpr (windowBase235_pos lo len).ne', ?_⟩
  by_contra hbad
  rw [not_lt] at hbad
  obtain ⟨k, hk⟩ := actual_exact_modulus_pinning B lo len
    (max (G B (lo + len)) (B * bridgeWidth (lo + len))) hB
    (le_max_right _ _) (hbad.trans (le_max_left _ _))
  exact (not_lt_of_ge ((hgap k).trans hk)) hlt
