-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.trueNormalizedState_le_carryMajorantQtilde
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:07:07.40661+00:00
-- url     : https://prove2.me/submissions/7362dcba-8001-4057-9e36-1dec4b18bb67

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_tsum_exponentKernel235_shell
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_finite_normalised_tail_le_Qtilde
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_summable_exponentKernel235
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_tailShellExponent_injective
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_tailShellExponent_lower
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

/-!
# The jump-constrained bound for the literal tail

The extra growth is proved directly for the three floor logarithms. This avoids
assuming an enumeration of the jump word or an unproved majorisation supplier.
At a dyadic starting point, d₂ ≤ 2d₃+1. Consequently the first k rank increases
multiply the height by at least 2^(k-j)3^j, j=(k+1)/3. The residue-three sum
then gives precisely the printed Q̃, with the existing actual rank-fibre bound.


-/

namespace ErdosProblems.Erdos269.PaperR10
open scoped BigOperators
open PaperR7 PaperR8
end ErdosProblems.Erdos269.PaperR10

open scoped BigOperators
open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (a : ℕ) :
    trueNormalizedState a ≤ (carryMajorantQtilde (paperJumpIndex a) : ℝ) := by
  classical
  let f : TailShellIndex a → ℝ := fun z =>
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 *
      exponentKernel235 (tailShellExponent a z)
  have hs0 : Summable (fun z : TailShellIndex a =>
      exponentKernel235 (tailShellExponent a z)) :=
    summable_exponentKernel235.comp_injective (tailShellExponent_injective a)
  have hs : Summable f := hs0.mul_left _
  have htsum : (∑' z : TailShellIndex a, f z) = trueNormalizedState a := by
    rw [hs.tsum_sigma]
    change (∑' n : ℕ, ∑' e : {e : Exponent235 // e ∈ dyadicSmoothShell235 (a + n)},
      (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e.val) = _
    simp_rw [tsum_mul_left, tsum_exponentKernel235_shell]
    rfl
  rw [← htsum]
  apply hs.tsum_le_of_sum_le
  intro t
  let s := t.image (tailShellExponent a)
  have heq : (∑ z ∈ t, f z) =
      ∑ e ∈ s, (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2 * exponentKernel235 e := by
    symm
    apply Finset.sum_image
    intro z _ w _ h
    exact tailShellExponent_injective a h
  rw [heq]
  apply finite_normalised_tail_le_Qtilde a s
  intro e he
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp he
  exact tailShellExponent_lower a z
