-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR8.rank_fibre_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:02:20.180751+00:00
-- url     : https://prove2.me/submissions/adaa03e7-c7f2-495e-97ab-f9c736ea3262

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_sorted_height_profile
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_exponent_le_height_profile
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_profile_eq_of_heightRank_eq
import Theorems.Thm_ErdosProblems_Erdos269_smoothExponentShell_card_le_dropFirst
import Theorems.Thm_ErdosProblems_Erdos269_sorted_pair_quadratic
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

/-!
# The actual height-rank majorant (round 8)

This file supplies the missing geometric summation over height ranks, not a
comparison of the much larger dyadic-shell bound with `carryMajorantQ`.
It uses the live round-7 definitions without changing any of them.

Proof text: not elaborated in this return. No additional hypotheses are hidden
in the final theorem. Mathlib source checks use commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
-/

namespace ErdosProblems.Erdos269.PaperR8
open scoped BigOperators
open PaperR7
end ErdosProblems.Erdos269.PaperR8

open scoped BigOperators
open PaperR7
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR8 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (s : Finset Exponent235) (n : ℕ)
    (hn : ∀ e ∈ s, heightRank235 (exponentValue235 e) = n) :
    9 * s.card ≤ (n + 3) ^ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    simp
  · obtain ⟨e₀, he₀⟩ := hs
    let x := exponentValue235 e₀
    let A := Nat.log 2 x
    let B := Nat.log 3 x
    let C := Nat.log 5 x
    have hsub : s ⊆ smoothExponentShell 2 3 5 (2 ^ A) (2 ^ (A + 1)) A B C := by
      intro e he
      have hp := profile_eq_of_heightRank_eq ((hn e he).trans (hn e₀ he₀).symm)
      have hc := exponent_le_height_profile e
      have hA : Nat.log 2 (exponentValue235 e) = A := hp.1
      have hB : Nat.log 3 (exponentValue235 e) = B := hp.2.1
      have hC : Nat.log 5 (exponentValue235 e) = C := hp.2.2
      have heA : e.1 < A + 1 := by omega
      have heB : e.2.1 < B + 1 := by omega
      have heC : e.2.2 < C + 1 := by omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr heA,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr heB, Finset.mem_range.mpr heC⟩⟩, ?_⟩
      have hlo := Nat.pow_log_le_self 2 (exponentValue235_pos e).ne'
      have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (exponentValue235 e)
      rw [hA] at hlo hhi
      exact ⟨hlo, hhi⟩
    have hcount : s.card ≤ (B + 1) * (C + 1) :=
      (Finset.card_le_card hsub).trans
        (smoothExponentShell_card_le_dropFirst (by decide : 0 < (2 : ℕ))
          (by rw [pow_succ]; omega))
    have hsort := sorted_height_profile (exponentValue235_pos e₀).ne'
    have hsum : C + B + A = n := by
      have h := hn e₀ he₀
      change A + B + C = n at h
      omega
    have hquad : 9 * ((C + 1) * (B + 1)) ≤ (n + 3) ^ 2 :=
      sorted_pair_quadratic hsort.1 hsort.2 hsum
    have hmul : 9 * s.card ≤ 9 * ((B + 1) * (C + 1)) :=
      Nat.mul_le_mul_left 9 hcount
    have hquad' : 9 * ((B + 1) * (C + 1)) ≤ (n + 3) ^ 2 := by
      simpa only [Nat.mul_comm (C + 1) (B + 1)] using hquad
    exact hmul.trans hquad'
