-- Prove2me | solution 1 for mme_released_joint_owner3_cell32_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:04:28.827406+00:00
-- url     : https://prove2.me/submissions/7bd65949-a5bf-402f-94e3-54e0a676c653

import Theorems.Thm_mme_parent_mixture_rational_identity
import Theorems.Thm_mme_rational_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedJointInterior MME.RecursiveYZ
open MME.MoreAsymmetryExactSeed MME.CompleteSplit

private def wordIndex (w : Fin 2 → CompleteWord 2) : ℕ :=
  27 * (w 0 0).val + 9 * (w 0 1).val + 3 * (w 1 0).val + (w 1 1).val

private def pNumerator (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 335753092000000000000000000000000, 0, 0, 0, 0, 0, 19796518952750000000000000000000000, 0, 19796518952750000000000000000000000, 0, 0, 0, 689689509867062415486188828188163, 0, 20651255777904653249189622343623674, 0, 689689509867062415486188828188163, 0, 0, 0, 0, 0, 0, 0, 19796518952750000000000000000000000, 0, 19796518952750000000000000000000000, 0, 0, 0, 20651255639876161263364622343623674, 0, 755592565412970121312946755312752652, 0, 20651255639876161263364622343623674, 0, 0, 0, 19796513896750000000000000000000000, 0, 19796513896750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 689689509867062415486188828188163, 0, 20651255777904653249189622343623674, 0, 689689509867062415486188828188163, 0, 0, 0, 19796513896750000000000000000000000, 0, 19796513896750000000000000000000000, 0, 0, 0, 0, 0, 335769222000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999134513371, 0, 0, 0, 0, 0, 3922249167206, 0, 3922249167206, 0, 0, 0, 7279269047347, 0, 3879979148935, 0, 7279269047347, 0, 0, 0, 0, 0, 0, 0, 3922249167206, 0, 3922249167206, 0, 0, 0, 3879979155619, 0, 280252982720, 0, 3879979155619, 0, 0, 0, 3922249422604, 0, 3922249422604, 0, 0, 0, 0, 0, 0, 0, 7279269047347, 0, 3879979148935, 0, 7279269047347, 0, 0, 0, 3922249422604, 0, 3922249422604, 0, 0, 0, 0, 0, 7999086473269, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999134513370, 0, 0, 0, 0, 0, 3922249167205, 0, 3922249167205, 0, 0, 0, 7279269047346, 0, 3879979148934, 0, 7279269047346, 0, 0, 0, 0, 0, 0, 0, 3922249167205, 0, 3922249167205, 0, 0, 0, 3879979155618, 0, 280252982719, 0, 3879979155618, 0, 0, 0, 3922249422603, 0, 3922249422603, 0, 0, 0, 0, 0, 0, 0, 7279269047346, 0, 3879979148934, 0, 7279269047346, 0, 0, 0, 3922249422603, 0, 3922249422603, 0, 0, 0, 0, 0, 7999086473268, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def p (w : Fin 2 → CompleteWord 2) : ℚ :=
  (pNumerator w : ℚ) / 1000000000000000000000000000000000000

private def lower (w : Fin 2 → CompleteWord 2) : ℚ :=
  -(lowerMagnitude w : ℚ) / 1000000000000

private def upper (w : Fin 2 → CompleteWord 2) : ℚ :=
  -(upperMagnitude w : ℚ) / 1000000000000

private theorem p_nonneg : ∀ w, 0 ≤ p w := by decide +kernel

private theorem log_bounds (w : Fin 2 → CompleteWord 2) (hp : 0 < p w) :
    (lower w : ℝ) ≤ Real.log (p w : ℝ) ∧
      Real.log (p w : ℝ) ≤ (upper w : ℝ) := by
  apply mme_rational_log_series_certificate (p w) hp (logScale w) 16
  all_goals revert w; decide +kernel

/-- A certified entropy lower bound for an actual pooled parent distribution,
including its owner, parent grade, regional orientation, and retained mode. -/
theorem solution :
    (1178891140 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 167) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 167 c : ℚ) *
        (((integerProfile 0 1 1) ⟨167, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨167, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨167, complement (parent_total 0 167) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨167, complement (parent_total 0 167) c⟩ v : ℕ))) /
      (size 0 1 167 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 167 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1178891140 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
