-- Prove2me | solution 1 for mme_released_joint_owner4_cell32_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:05:34.309864+00:00
-- url     : https://prove2.me/submissions/245df8a2-7cce-420e-8007-b636111e6b3f

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 335740368000000000000000000000000, 0, 0, 0, 0, 0, 19796234360000000000000000000000000, 0, 19796234360000000000000000000000000, 0, 0, 0, 689712829411108429692580474198082, 0, 20650879243886384162688839051603836, 0, 689712829411108429692580474198082, 0, 0, 0, 0, 0, 0, 0, 19796234360000000000000000000000000, 0, 19796234360000000000000000000000000, 0, 0, 0, 20650879283020310853888839051603836, 0, 755596275854542176248074321896792328, 0, 20650879283020310853888839051603836, 0, 0, 0, 19796234018250000000000000000000000, 0, 19796234018250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 689712829411108429692580474198082, 0, 20650879243886384162688839051603836, 0, 689712829411108429692580474198082, 0, 0, 0, 19796234018250000000000000000000000, 0, 19796234018250000000000000000000000, 0, 0, 0, 0, 0, 335741893000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999172410985, 0, 0, 0, 0, 0, 3922263543208, 0, 3922263543208, 0, 0, 0, 7279235236264, 0, 3879997382086, 0, 7279235236264, 0, 0, 0, 0, 0, 0, 0, 3922263543208, 0, 3922263543208, 0, 0, 0, 3879997380191, 0, 280248072094, 0, 3879997380191, 0, 0, 0, 3922263560471, 0, 3922263560471, 0, 0, 0, 0, 0, 0, 0, 7279235236264, 0, 3879997382086, 0, 7279235236264, 0, 0, 0, 3922263560471, 0, 3922263560471, 0, 0, 0, 0, 0, 7999167868795, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999172410984, 0, 0, 0, 0, 0, 3922263543207, 0, 3922263543207, 0, 0, 0, 7279235236263, 0, 3879997382085, 0, 7279235236263, 0, 0, 0, 0, 0, 0, 0, 3922263543207, 0, 3922263543207, 0, 0, 0, 3879997380190, 0, 280248072093, 0, 3879997380190, 0, 0, 0, 3922263560470, 0, 3922263560470, 0, 0, 0, 0, 0, 0, 0, 7279235236263, 0, 3879997382085, 0, 7279235236263, 0, 0, 0, 3922263560470, 0, 3922263560470, 0, 0, 0, 0, 0, 7999167868794, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1178877840 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 212) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 212 c : ℚ) *
        (((integerProfile 1 1 1) ⟨212, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨212, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨212, complement (parent_total 1 212) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨212, complement (parent_total 1 212) c⟩ v : ℕ))) /
      (size 1 1 212 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 212 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1178877840 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
