-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_card_le_dropFirst
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:39:17.562258+00:00
-- url     : https://prove2.me/submissions/c5fd4eb9-aa17-40f3-9d29-63b36980ae17

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_exponent_unique_in_real_short_interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
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

namespace PaperR10
end PaperR10

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open Finset
open scoped BigOperators

noncomputable section

open PaperR10
end
end ErdosProblems.Erdos269.PaperCompleteR20

open Finset
open scoped BigOperators
open PaperR10
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR10 in
theorem solution
    {p q r hp hq hr : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hwidth : hi ≤ (p : ℝ) * lo) :
    (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1) := by
  classical
  let target := (range (hq + 1)).product (range (hr + 1))
  have hcard :
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      rcases e with ⟨a, b, c⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr ⟨hinner.1, hinner.2⟩
    · intro e₁ he₁ e₂ he₂ hproj
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he₁ he₂
      have hw : 0 ≤ (q : ℝ) ^ b₁ * (r : ℝ) ^ c₁ := by positivity
      have ha : a₁ = a₂ := exponent_unique_in_real_short_interval
        hpPos hw hwidth
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₁.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₁.2.2)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₂.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₂.2.2)
      simp [ha]
  simpa [target] using hcard
