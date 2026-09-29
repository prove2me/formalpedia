-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR8.exponent_le_height_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:59:10.147779+00:00
-- url     : https://prove2.me/submissions/0a2144e0-d88f-448f-9df7-e632c913c64d

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
theorem solution (e : Exponent235) :
    e.1 ≤ Nat.log 2 (exponentValue235 e) ∧
    e.2.1 ≤ Nat.log 3 (exponentValue235 e) ∧
    e.2.2 ≤ Nat.log 5 (exponentValue235 e) := by
  have hx : 0 < exponentValue235 e := exponentValue235_pos e
  have d2 : 2 ^ e.1 ∣ exponentValue235 e := by
    refine ⟨3 ^ e.2.1 * 5 ^ e.2.2, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  have d3 : 3 ^ e.2.1 ∣ exponentValue235 e := by
    refine ⟨2 ^ e.1 * 5 ^ e.2.2, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  have d5 : 5 ^ e.2.2 ∣ exponentValue235 e := by
    refine ⟨2 ^ e.1 * 3 ^ e.2.1, ?_⟩
    simp only [exponentValue235, smooth3Val]
    ring
  -- Mathlib/Data/Nat/Log.lean: Nat.le_log_of_pow_le.
  exact ⟨Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d2),
    Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d3),
    Nat.le_log_of_pow_le (by decide) (Nat.le_of_dvd hx d5)⟩
