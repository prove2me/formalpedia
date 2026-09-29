-- Prove2me | solution 1 for mme_released_joint_owner0_cell18_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:37:25.329067+00:00
-- url     : https://prove2.me/submissions/ab23d904-e182-405d-8f48-9608c7e24d25

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3315328604500000000000000000000000, 0, 0, 0, 0, 0, 4069319496073253690380000000000000, 0, 4069319496073253690380000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3315328604500000000000000000000000, 0, 0, 0, 0, 0, 238546054899853492619240000000000000, 0, 238546054899853492619240000000000000, 0, 0, 0, 4069317775627725059412500000000000, 0, 238545943084244549881175000000000000, 0, 4069317775627725059412500000000000, 0, 0, 0, 0, 0, 0, 0, 4069319496073253690380000000000000, 0, 4069319496073253690380000000000000, 0, 0, 0, 4069317775627725059412500000000000, 0, 238545943084244549881175000000000000, 0, 4069317775627725059412500000000000, 0, 0, 0, 3315398868000000000000000000000000, 0, 3315398868000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5709198533712, 0, 0, 0, 0, 0, 5504279493490, 0, 5504279493490, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5709198533712, 0, 0, 0, 0, 0, 1433192884991, 0, 1433192884991, 0, 0, 0, 5504279916274, 0, 1433193353729, 0, 5504279916274, 0, 0, 0, 0, 0, 0, 0, 5504279493490, 0, 5504279493490, 0, 0, 0, 5504279916274, 0, 1433193353729, 0, 5504279916274, 0, 0, 0, 5709177340411, 0, 5709177340411, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5709198533711, 0, 0, 0, 0, 0, 5504279493489, 0, 5504279493489, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5709198533711, 0, 0, 0, 0, 0, 1433192884990, 0, 1433192884990, 0, 0, 0, 5504279916273, 0, 1433193353728, 0, 5504279916273, 0, 0, 0, 0, 0, 0, 0, 5504279493489, 0, 5504279493489, 0, 0, 0, 5504279916273, 0, 1433193353728, 0, 5504279916273, 0, 0, 0, 5709177340410, 0, 5709177340410, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1622431420 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 18) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 18 c : ℚ) *
        (((integerProfile 1 1 1) ⟨18, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨18, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨18, complement (parent_total 1 18) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨18, complement (parent_total 1 18) c⟩ v : ℕ))) /
      (size 1 1 18 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 18 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1622431420 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
