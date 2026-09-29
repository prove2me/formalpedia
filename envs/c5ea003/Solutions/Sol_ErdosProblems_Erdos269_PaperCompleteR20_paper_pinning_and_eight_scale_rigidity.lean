-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:17:54.66746+00:00
-- url     : https://prove2.me/submissions/51dd8f82-611e-4352-84ca-241ddf22a3ed

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
import Theorems.Thm_ErdosProblems_Erdos269_dyadicNormalizedShellTsumTailR235_succ
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_geometric_bounds
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_paper_pinning_and_rigidity
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

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

namespace PaperR7
end PaperR7

/-!
# Uniqueness for the full printed eight-scale width

The actual radix product grows as `8^k`, uniformly in the starting scale.
Keep that product in the homogeneous recurrence instead of replacing each
radix by two. This admits exactly the paper's `o(8^k)` width condition.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators
open PaperR7

theorem actual_orbit_difference (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n → y (n + 1) =
      (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ))
    (k : ℕ) :
    y (A + k) - trueNormalizedState (A + k) =
      (actualWindowProduct A k : ℝ) * (y A - trueNormalizedState A) := by
  induction k with
  | zero => simp [actualWindowProduct]
  | succ k ih =>
    have h1 := hrec (A + k) (by omega)
    have h2 := dyadicNormalizedShellTsumTailR235_succ (A + k)
    have hts : ∀ n : ℕ, trueNormalizedState n =
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 n := fun _ => rfl
    have hdiff : y (A + k + 1) - trueNormalizedState (A + k + 1) =
        (dyadicBlockBase235 (A + k) : ℝ) *
          (y (A + k) - trueNormalizedState (A + k)) := by
      rw [h1, hts (A + k + 1), h2, hts (A + k)]
      ring
    have hprod : actualWindowProduct A (k + 1) =
        actualWindowProduct A k * dyadicBlockBase235 (A + k) := by
      simp only [actualWindowProduct, Finset.prod_range_succ]
    rw [show A + (k + 1) = A + k + 1 by omega, hdiff, ih, hprod]
    push_cast
    ring

theorem surviving_eight_scale_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n → y (n + 1) =
      (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
      y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
      trueNormalizedState n ≤
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) :
    y A = trueNormalizedState A := by
  by_contra hne
  have hepos : 0 < |y A - trueNormalizedState A| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨k₀, hk₀⟩ := hvanish (|y A - trueNormalizedState A| / 30) (by positivity)
  have hprodpos : (0 : ℝ) < (actualWindowProduct A k₀ : ℝ) := by
    exact_mod_cast actualWindowProduct_pos A k₀
  have hdev : |y (A + k₀) - trueNormalizedState (A + k₀)| =
      (actualWindowProduct A k₀ : ℝ) * |y A - trueNormalizedState A| := by
    rw [actual_orbit_difference A y hrec, abs_mul, abs_of_pos hprodpos]
  have hlarge : (8 : ℝ) ^ k₀ / 15 * |y A - trueNormalizedState A| <
      |y (A + k₀) - trueNormalizedState (A + k₀)| := by
    rw [hdev]
    exact mul_lt_mul_of_pos_right (actualWindowProduct_geometric_bounds A k₀).1 hepos
  have hbound : |y (A + k₀) - trueNormalizedState (A + k₀)| ≤ width (A + k₀) := by
    obtain ⟨hy, hy'⟩ := hwin (A + k₀) (by omega)
    obtain ⟨hx, hx'⟩ := hwidth (A + k₀) (by omega)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow : (0 : ℝ) < (8 : ℝ) ^ k₀ := by positivity
  have hsmall : width (A + k₀) < |y A - trueNormalizedState A| / 30 * 8 ^ k₀ :=
    (div_lt_iff₀ hpow).mp (hk₀ k₀ le_rfl)
  nlinarith [mul_pos hpow hepos]
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open PaperR7
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A) := by
  refine ⟨paper_pinning_and_rigidity.1, paper_pinning_and_rigidity.2.1, ?_⟩
  intro width A y _ hrec hwin hwidth hvanish
  exact surviving_eight_scale_window_orbit_eq_true_state width A y hrec hwin hwidth hvanish
