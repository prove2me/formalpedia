-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.shiftedLeading_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:49:25.589989+00:00
-- url     : https://prove2.me/submissions/31dcc645-3f61-4137-be7a-bcc02e6aee7a

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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftValue
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_two_pow_le_windowBase235
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowBase_eq_product
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_height_windowProduct
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_actualWindowProduct_pos
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Module.FiniteDimension
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

-- `Summable.norm` (the alias of `summable_norm_iff`) no longer arrives transitively on Lean 4.30.0
-- / Mathlib c5ea0035, and dot notation no longer resolves it because `Summable` now unfolds to
-- `Exists`. Imported explicitly and applied by name below. Statements are unchanged.
namespace PaperR7
end PaperR7

/-!
# Weighted shifts of the literal series

Finite linear combinations of shifted digits retain the original value
with an integer prefix correction. All sums below converge absolutely.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7
open scoped BigOperators





























theorem shiftHeight_ratio_le_binary {m n : ℕ} (h : m ≤ n) :
    (shiftHeight m : ℝ) / (shiftHeight n : ℝ) ≤ 1 / (2 : ℝ) ^ (n - m) := by
  have hp : (0 : ℝ) < (shiftHeight m : ℝ) := threePrimeHeight235_cast_pos _
  have hW : (0 : ℝ) < (actualWindowProduct m (n - m) : ℝ) := by
    exact_mod_cast actualWindowProduct_pos m (n - m)
  have hpow : (2 : ℝ) ^ (n - m) ≤ (actualWindowProduct m (n - m) : ℝ) := by
    have hZ : (2 : ℤ) ^ (n - m) ≤ (actualWindowProduct m (n - m) : ℤ) := by
      rw [← actualWindowBase_eq_product]
      exact two_pow_le_windowBase235 m (n - m)
    exact_mod_cast hZ
  have he : (shiftHeight n : ℝ) =
      (shiftHeight m : ℝ) * (actualWindowProduct m (n - m) : ℝ) := by
    exact_mod_cast (show shiftHeight n = shiftHeight m * actualWindowProduct m (n - m) by
      simpa only [Nat.add_sub_of_le h] using height_windowProduct m (n - m))
  rw [he]
  calc
    (shiftHeight m : ℝ) / ((shiftHeight m : ℝ) * (actualWindowProduct m (n - m) : ℝ))
        = 1 / (actualWindowProduct m (n - m) : ℝ) := by field_simp
    _ ≤ 1 / (2 : ℝ) ^ (n - m) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (c : ℕ → ℤ) (σ r J : ℕ)
    (hJ : J ≤ σ)
    (hmax : ∀ j, J < j → j ≤ σ → c j = 0)
    (hmargin : (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)|) :
    shiftedLeading c σ r ≠ 0 := by
  intro hz
  have hsum : (∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ)) = 0 := by
    have he : (shiftedLeading c σ r : ℝ) = 0 := by rw [hz]; norm_num
    simp only [shiftedLeading, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_natCast] at he
    linarith
  have htrunc : (∑ j ∈ Finset.range (J + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ)) =
      ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    have hjs : j ≤ σ := by have := Finset.mem_range.mp hj; omega
    have hJj : J < j := by
      have hn : ¬ j < J + 1 := by simpa only [Finset.mem_range] using hj'
      omega
    simp [hmax j hJj hjs]
  rw [← htrunc, Finset.sum_range_succ] at hsum
  have hp : (0 : ℝ) < (shiftHeight (J * r) : ℝ) := threePrimeHeight235_cast_pos _
  have hnormalized :
      (∑ j ∈ Finset.range J, (c j : ℝ) * (shiftHeight (j * r) : ℝ) /
        (shiftHeight (J * r) : ℝ)) = -(c J : ℝ) := by
    rw [← Finset.sum_div]
    apply (div_eq_iff hp.ne').2
    linarith
  have hbound : |(c J : ℝ)| ≤
      ∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r) := by
    calc
      |(c J : ℝ)| = |∑ j ∈ Finset.range J,
          (c j : ℝ) * (shiftHeight (j * r) : ℝ) / (shiftHeight (J * r) : ℝ)| := by
        rw [hnormalized, abs_neg]
      _ ≤ ∑ j ∈ Finset.range J,
          |(c j : ℝ) * (shiftHeight (j * r) : ℝ) / (shiftHeight (J * r) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
        have hratio := shiftHeight_ratio_le_binary (Nat.mul_le_mul_right r hjJ)
        rw [← Nat.sub_mul] at hratio
        have hjp : (0 : ℝ) < (shiftHeight (j * r) : ℝ) := threePrimeHeight235_cast_pos _
        rw [abs_div, abs_mul, abs_of_pos hjp, abs_of_pos hp, mul_div_assoc]
        simpa only [← mul_div_assoc, mul_one] using
          mul_le_mul_of_nonneg_left hratio (abs_nonneg (c j : ℝ))
  exact (not_lt_of_ge hbound) hmargin
