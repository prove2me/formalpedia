-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.shiftGamma_four_values
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:48:13.1756+00:00
-- url     : https://prove2.me/submissions/4de655cb-84a1-4b9e-9f9f-039e13412425

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
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
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

namespace PaperR7
end PaperR7

/-!
# Exact arithmetic of the paper's weighted shifts

The ratio is defined from the actual dyadic heights. Integer logarithms
prove its four-element alphabet without numerical logarithms. The factor
15 clears both the shifted coefficients and the finite prefix correction.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7
open scoped BigOperators





theorem natLog_dyadic_add_cases {b : ℕ} (hb : 1 < b) (m n : ℕ) :
    Nat.log b (2 ^ (m + n)) = Nat.log b (2 ^ m) + Nat.log b (2 ^ n) ∨
    Nat.log b (2 ^ (m + n)) = Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 1 := by
  have hm : (2 : ℕ) ^ m ≠ 0 := by positivity
  have hn : (2 : ℕ) ^ n ≠ 0 := by positivity
  have hmn : (2 : ℕ) ^ (m + n) ≠ 0 := by positivity
  have hlo : Nat.log b (2 ^ m) + Nat.log b (2 ^ n) ≤ Nat.log b (2 ^ (m + n)) := by
    apply Nat.le_log_of_pow_le hb
    simpa only [pow_add] using Nat.mul_le_mul (Nat.pow_log_le_self b hm) (Nat.pow_log_le_self b hn)
  have hup : Nat.log b (2 ^ (m + n)) < Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 2 := by
    apply Nat.log_lt_of_lt_pow hmn
    have h := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self hb (2 ^ m))
      (Nat.lt_pow_succ_log_self hb (2 ^ n))
    simpa only [← pow_add, Nat.succ_eq_add_one,
      show Nat.log b (2 ^ m) + 1 + (Nat.log b (2 ^ n) + 1) =
        Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 2 by omega] using h
  omega

theorem shiftHeight_add_factor (m n : ℕ) :
    ∃ d : ℕ, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15) ∧
      shiftHeight (m + n) = d * (shiftHeight m * shiftHeight n) := by
  rcases natLog_dyadic_add_cases (by decide : 1 < (3 : ℕ)) m n with h3 | h3 <;>
    rcases natLog_dyadic_add_cases (by decide : 1 < (5 : ℕ)) m n with h5 | h5
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨5, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨3, Or.inr (Or.inl rfl), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨15, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (a t : ℕ) :
    shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15 := by
  obtain ⟨d, hd, hh⟩ := shiftHeight_add_factor t (a + 1)
  have ht : (shiftHeight t : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have ha : (shiftHeight (a + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have hd0 : (d : ℝ) ≠ 0 := by
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have hhR : (shiftHeight (a + t + 1) : ℝ) = (d : ℝ) *
      ((shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ)) := by
    exact_mod_cast (show shiftHeight (a + t + 1) = d * (shiftHeight t * shiftHeight (a + 1)) by
      simpa only [show t + (a + 1) = a + t + 1 by omega] using hh)
  have he : shiftGamma a t = 1 / (d : ℝ) := by
    unfold shiftGamma
    rw [hhR]
    field_simp
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all
