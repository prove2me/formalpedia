-- Prove2me | solution 1 for mme_released_joint_owner2_cell36_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:59:13.130974+00:00
-- url     : https://prove2.me/submissions/7c65d400-112c-4be2-8b7f-ea0dc8397629

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3665098342500000000000000000000000, 0, 0, 0, 0, 0, 6660612982970581323839500000000000, 0, 6660612982970581323839500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3665098342500000000000000000000000, 0, 0, 0, 0, 0, 233013674003058837352321000000000000, 0, 233013674003058837352321000000000000, 0, 0, 0, 6660611156167875108660000000000000, 0, 233013611908664249782680000000000000, 0, 6660611156167875108660000000000000, 0, 0, 0, 0, 0, 0, 0, 6660612982970581323839500000000000, 0, 6660612982970581323839500000000000, 0, 0, 0, 6660611156167875108660000000000000, 0, 233013611908664249782680000000000000, 0, 6660611156167875108660000000000000, 0, 0, 0, 3665167467500000000000000000000000, 0, 3665167467500000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5608900111125, 0, 0, 0, 0, 0, 5011543759181, 0, 5011543759181, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5608900111125, 0, 0, 0, 0, 0, 1456658140431, 0, 1456658140431, 0, 0, 0, 5011544033450, 0, 1456658406914, 0, 5011544033450, 0, 0, 0, 0, 0, 0, 0, 5011543759181, 0, 5011543759181, 0, 0, 0, 5011544033450, 0, 1456658406914, 0, 5011544033450, 0, 0, 0, 5608881250964, 0, 5608881250964, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5608900111124, 0, 0, 0, 0, 0, 5011543759180, 0, 5011543759180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5608900111124, 0, 0, 0, 0, 0, 1456658140430, 0, 1456658140430, 0, 0, 0, 5011544033449, 0, 1456658406913, 0, 5011544033449, 0, 0, 0, 0, 0, 0, 0, 5011543759180, 0, 5011543759180, 0, 0, 0, 5011544033449, 0, 1456658406913, 0, 5011544033449, 0, 0, 0, 5608881250963, 0, 5608881250963, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1706953920 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 126) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 126 c : ℚ) *
        (((integerProfile 0 1 1) ⟨126, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨126, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨126, complement (parent_total 0 126) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨126, complement (parent_total 0 126) c⟩ v : ℕ))) /
      (size 0 1 126 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 126 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1706953920 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
