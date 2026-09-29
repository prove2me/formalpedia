-- Prove2me | solution 1 for mme_released_joint_owner1_cell11_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:31:40.44789+00:00
-- url     : https://prove2.me/submissions/806d3ee5-43ce-40e7-92cf-fee39cfeed8b

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3294857911000000000000000000000000, 0, 0, 0, 0, 0, 4112231555765060244494000000000000, 0, 4112231555765060244494000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3294857911000000000000000000000000, 0, 0, 0, 0, 0, 238480681292969879511012000000000000, 0, 238480681292969879511012000000000000, 0, 0, 0, 4112231118861874530702000000000000, 0, 238480660041776250938596000000000000, 0, 4112231118861874530702000000000000, 0, 0, 0, 0, 0, 0, 0, 4112231555765060244494000000000000, 0, 4112231555765060244494000000000000, 0, 0, 0, 4112231118861874530702000000000000, 0, 238480660041776250938596000000000000, 0, 4112231118861874530702000000000000, 0, 0, 0, 3294875405000000000000000000000000, 0, 3294875405000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5715392234568, 0, 0, 0, 0, 0, 5493789440216, 0, 5493789440216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5715392234568, 0, 0, 0, 0, 0, 1433466972803, 0, 1433466972803, 0, 0, 0, 5493789546460, 0, 1433467061914, 0, 5493789546460, 0, 0, 0, 0, 0, 0, 0, 5493789440216, 0, 5493789440216, 0, 0, 0, 5493789546460, 0, 1433467061914, 0, 5493789546460, 0, 0, 0, 5715386925097, 0, 5715386925097, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5715392234567, 0, 0, 0, 0, 0, 5493789440215, 0, 5493789440215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5715392234567, 0, 0, 0, 0, 0, 1433466972802, 0, 1433466972802, 0, 0, 0, 5493789546459, 0, 1433467061913, 0, 5493789546459, 0, 0, 0, 0, 0, 0, 0, 5493789440215, 0, 5493789440215, 0, 0, 0, 5493789546459, 0, 1433467061913, 0, 5493789546459, 0, 0, 0, 5715386925096, 0, 5715386925096, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1623476355 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 56) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 56 c : ℚ) *
        (((integerProfile 1 1 2) ⟨56, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨56, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨56, complement (parent_total 1 56) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨56, complement (parent_total 1 56) c⟩ v : ℕ))) /
      (size 1 1 56 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 56 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1623476355 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
