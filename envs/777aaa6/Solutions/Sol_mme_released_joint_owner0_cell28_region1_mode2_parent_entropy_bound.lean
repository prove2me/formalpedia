-- Prove2me | solution 1 for mme_released_joint_owner0_cell28_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:29:28.550426+00:00
-- url     : https://prove2.me/submissions/16dad9e1-c7c5-4e38-bc99-df22b62da6ff

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328490354000000000000000000000000, 0, 0, 0, 0, 0, 19431324493500000000000000000000000, 0, 19431324493500000000000000000000000, 0, 0, 0, 24833642782069317488204247955910, 0, 20304074581284477172645591504088180, 0, 24833642782069317488204247955910, 0, 0, 0, 0, 0, 0, 0, 19431324493500000000000000000000000, 0, 19431324493500000000000000000000000, 0, 0, 0, 20304074550545281147909591504088180, 0, 762576788707212206088936816991823640, 0, 20304074550545281147909591504088180, 0, 0, 0, 19431323456000000000000000000000000, 0, 19431323456000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 24833642782069317488204247955910, 0, 20304074581284477172645591504088180, 0, 24833642782069317488204247955910, 0, 0, 0, 19431323456000000000000000000000000, 0, 19431323456000000000000000000000000, 0, 0, 0, 0, 0, 328496306000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021003084246, 0, 0, 0, 0, 0, 3940868850469, 0, 3940868850469, 0, 0, 0, 10603311260302, 0, 3896933694786, 0, 10603311260302, 0, 0, 0, 0, 0, 0, 0, 3940868850469, 0, 3940868850469, 0, 0, 0, 3896933696300, 0, 271052069070, 0, 3896933696300, 0, 0, 0, 3940868903863, 0, 3940868903863, 0, 0, 0, 0, 0, 0, 0, 10603311260302, 0, 3896933694786, 0, 10603311260302, 0, 0, 0, 3940868903863, 0, 3940868903863, 0, 0, 0, 0, 0, 8020984965157, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021003084245, 0, 0, 0, 0, 0, 3940868850468, 0, 3940868850468, 0, 0, 0, 10603311260301, 0, 3896933694785, 0, 10603311260301, 0, 0, 0, 0, 0, 0, 0, 3940868850468, 0, 3940868850468, 0, 0, 0, 3896933696299, 0, 271052069069, 0, 3896933696299, 0, 0, 0, 3940868903862, 0, 3940868903862, 0, 0, 0, 0, 0, 0, 0, 10603311260301, 0, 3896933694785, 0, 10603311260301, 0, 0, 0, 3940868903862, 0, 3940868903862, 0, 0, 0, 0, 0, 8020984965156, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1142125906 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 28) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 28 c : ℚ) *
        (((integerProfile 1 1 2) ⟨28, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨28, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨28, complement (parent_total 1 28) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨28, complement (parent_total 1 28) c⟩ v : ℕ))) /
      (size 1 1 28 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 28 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1142125906 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
