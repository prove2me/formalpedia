-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR8.sorted_height_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:55:59.537565+00:00
-- url     : https://prove2.me/submissions/ffedca2a-8b8b-48ec-af3c-28a521283fdc

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
theorem solution {x : ℕ} (hx : x ≠ 0) :
    Nat.log 5 x ≤ Nat.log 3 x ∧ Nat.log 3 x ≤ Nat.log 2 x := by
  -- Mathlib/Data/Nat/Log.lean: Nat.pow_log_le_self.
  have h5 : 5 ^ Nat.log 5 x ≤ x := Nat.pow_log_le_self 5 hx
  have h3 : 3 ^ Nat.log 3 x ≤ x := Nat.pow_log_le_self 3 hx
  exact ⟨Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left (by decide : 3 ≤ 5) _).trans h5),
    Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 3) _).trans h3)⟩
