-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR8.hasSum_rankMajorant
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:57:50.920278+00:00
-- url     : https://prove2.me/submissions/2b72bde0-cf9f-4d76-90f0-6636eead0962

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
import Theorems.Thm_ErdosProblems_Erdos269_hasSum_succ_sq_div_two_pow
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
theorem solution (n : ℕ) :
    HasSum (rankMajorant n) (carryMajorantQ n : ℝ) := by
  have hs := hasSum_succ_sq_div_two_pow
  -- Mathlib/Analysis/SpecificLimits/Normed.lean:
  -- hasSum_choose_mul_geometric_of_norm_lt_one.
  have hg0 := hasSum_choose_mul_geometric_of_norm_lt_one 0
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hg1 := hasSum_choose_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h0 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    norm_num at hg0
    exact hg0
  have h1 : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) 4 := by
    convert hg1 using 1 <;> norm_num [Nat.choose_one_right]
  have hh := ((hs.add (h1.mul_left (2 * ((n : ℝ) + 2)))).add
    (h0.mul_left (((n : ℝ) + 2) ^ 2))).div_const 18
  have hval : (12 + 2 * ((n : ℝ) + 2) * 4 + ((n : ℝ) + 2) ^ 2 * 2) / 18 =
      (carryMajorantQ n : ℝ) := by
    simp only [carryMajorantQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
    ring
  rw [hval] at hh
  apply hh.congr_fun
  intro k
  simp only [rankMajorant, Nat.cast_add, Nat.cast_ofNat, one_div_pow]
  ring
