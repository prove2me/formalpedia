-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:07.550772+00:00
-- url     : https://prove2.me/submissions/cb0133ff-26d7-43fd-8beb-aa0ddfe1fa7f

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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_FixedBaseRecoding
import Theorems.Thm_ErdosProblems_Erdos269_dyadicOrderedBlockDigit235_le_quadratic
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_all_dyadic_heights_dvd_base_powers_iff
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_orderedDigit235_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_recodedCoefficient_integral
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_eight_pow_lt_fifteen_dyadic_height
import Theorems.Thm_ErdosProblems_Erdos269_summable_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_paperSeries235_eq_shellTsum
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_le_cube
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

-- `Summable.norm` (the alias of `summable_norm_iff`) no longer arrives transitively on Lean 4.30.0
-- / Mathlib c5ea0035, and dot notation no longer resolves it because `Summable` now unfolds to
-- `Exists`. Imported explicitly and applied by name below. Statements are unchanged.
namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# Direct fixed-base recoding of the actual series

The coefficient is the literal termwise rescaling of the actual ordered
digit. Base 30 retains integrality; base 8 retains the quadratic bound and
has denominators supported on 3 and 5. No echoing hypothesis is asserted.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7 PaperR8
open scoped BigOperators





theorem dyadic_height_le_eight_pow (n : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ n) ≤ 8 ^ n := by
  have h := threePrimeHeight_le_cube 2 3 5 (2 ^ n)
    (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  have hp : (2 ^ n : ℕ) ^ 3 = 8 ^ n := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
    norm_num
  rwa [hp] at h



theorem recodedCoefficient_pos {q : ℕ} (hq : 0 < q) (a : ℕ) :
    0 < recodedCoefficient q a := by
  have hm : (0 : ℝ) < dyadicOrderedBlockDigit235 a := by exact_mod_cast orderedDigit235_pos a
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact div_pos (mul_pos hm (pow_pos hqR _)) (threePrimeHeight235_cast_pos _)



theorem recodedCoefficient_lower {q : ℕ} (_hq : 0 < q) (a : ℕ) :
    ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a := by
  have hp := threePrimeHeight235_cast_pos (2 ^ (a + 1))
  have hu : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≤ (8 : ℝ) ^ (a + 1) := by
    exact_mod_cast dyadic_height_le_eight_pow (a + 1)
  have hm : (1 : ℝ) ≤ dyadicOrderedBlockDigit235 a := by
    exact_mod_cast orderedDigit235_pos a
  have hqpow : (0 : ℝ) ≤ (q : ℝ) ^ (a + 1) := pow_nonneg (Nat.cast_nonneg _) _
  rw [div_pow]
  apply (div_le_div_of_nonneg_left hqpow hp hu).trans
  apply div_le_div_of_nonneg_right _ hp.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) hqpow]

theorem base_eight_coefficient_upper (a : ℕ) :
    recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2 := by
  have hp := threePrimeHeight235_cast_pos (2 ^ (a + 1))
  have hl := eight_pow_lt_fifteen_dyadic_height (a + 1)
  have hratio : (8 : ℝ) ^ (a + 1) /
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) < 15 :=
    (div_lt_iff₀ hp).2 hl
  have hm : (0 : ℝ) < dyadicOrderedBlockDigit235 a := by exact_mod_cast orderedDigit235_pos a
  have hmu : (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * ((a + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a
  have hh := mul_lt_mul_of_pos_left hratio hm
  unfold recodedCoefficient
  norm_num only [Nat.cast_ofNat]
  rw [mul_div_assoc]
  nlinarith only [hh, hmu]

/-- A fixed power of 15 clears each base-eight coefficient. -/
theorem base_eight_coefficient_in_localization (a : ℕ) :
    ∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1) := by
  obtain ⟨z, _, hz⟩ := recodedCoefficient_integral (q := 120) (by decide) (by decide) a
  refine ⟨z, ?_⟩
  rw [← hz]
  unfold recodedCoefficient
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  norm_num only [Nat.cast_ofNat]
  rw [show (120 : ℝ) = 8 * 15 by norm_num, mul_pow]
  field_simp
  <;> ring

theorem recoded_term_eq_half_shell {q : ℕ} (hq : 0 < q) (a : ℕ) :
    recodedCoefficient q a / (q : ℝ) ^ (a + 1) = dyadicShellMassR235 a / 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : (q : ℝ) ^ (a + 1) ≠ 0 := pow_ne_zero _ hqR
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  have hd := half_threePrimeHeight_mul_dyadicShellMassR235 a
  calc
    recodedCoefficient q a / (q : ℝ) ^ (a + 1) =
        (dyadicOrderedBlockDigit235 a : ℝ) /
          (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) := by
      unfold recodedCoefficient
      field_simp
    _ = dyadicShellMassR235 a / 2 := by
      apply (div_eq_div_iff hp (by norm_num : (2 : ℝ) ≠ 0)).2
      nlinarith only [hd]

theorem hasSum_recoded_actual_value {q : ℕ} (hq : 0 < q) :
    HasSum (fun a : ℕ => recodedCoefficient q a / (q : ℝ) ^ (a + 1))
      (paperSeries235 / 2) := by
  have hs := summable_dyadicShellMassR235.hasSum.div_const (2 : ℝ)
  have hv : (∑' a : ℕ, dyadicShellMassR235 a) = paperSeries235 := by
    simpa only [dyadicShellTsumTailR235, Nat.zero_add] using paperSeries235_eq_shellTsum.symm
  rw [hv] at hs
  exact hs.congr_fun (fun a => recoded_term_eq_half_shell hq a)

theorem recoded_actual_value_absolute {q : ℕ} (hq : 0 < q) :
    Summable (fun a : ℕ => |recodedCoefficient q a / (q : ℝ) ^ (a + 1)|) := by
  simpa only [Real.norm_eq_abs] using Summable.norm (hasSum_recoded_actual_value hq).summable
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR8
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a) := by
  refine ⟨hasSum_recoded_actual_value (by decide), recoded_actual_value_absolute (by decide),
    hasSum_recoded_actual_value (by decide), recoded_actual_value_absolute (by decide),
    ?_, ?_, ?_⟩
  · intro a
    refine ⟨recodedCoefficient_integral (by decide) (by decide) a, ?_⟩
    have h := recodedCoefficient_lower (q := 30) (by decide) a
    norm_num only [Nat.cast_ofNat, show (30 / 8 : ℝ) = 15 / 4 by norm_num] at h
    exact h
  · intro a
    exact ⟨base_eight_coefficient_in_localization a,
      recodedCoefficient_pos (by decide) a, base_eight_coefficient_upper a⟩
  · intro q hq
    exact ⟨all_dyadic_heights_dvd_base_powers_iff q,
      fun a => recodedCoefficient_lower (by omega) a⟩
