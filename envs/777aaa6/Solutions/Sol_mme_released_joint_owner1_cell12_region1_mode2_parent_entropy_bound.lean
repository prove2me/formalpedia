-- Prove2me | solution 1 for mme_released_joint_owner1_cell12_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:33:04.91899+00:00
-- url     : https://prove2.me/submissions/729287d9-4132-4a7a-9e5c-73a22c8a3fb8

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 326253823000000000000000000000000, 0, 0, 0, 0, 0, 18397528426750000000000000000000000, 0, 18397528426750000000000000000000000, 0, 0, 0, 10801118773041341823085715983752, 0, 19676035958560169575957828568032496, 0, 10801118773041341823085715983752, 0, 0, 0, 0, 0, 0, 0, 18397528426750000000000000000000000, 0, 18397528426750000000000000000000000, 0, 0, 0, 19676023984244801669507828568032496, 0, 773419845522297892141776342863935008, 0, 19676023984244801669507828568032496, 0, 0, 0, 18397537860250000000000000000000000, 0, 18397537860250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 10801118773041341823085715983752, 0, 19676035958560169575957828568032496, 0, 10801118773041341823085715983752, 0, 0, 0, 18397537860250000000000000000000000, 0, 18397537860250000000000000000000000, 0, 0, 0, 0, 0, 326311146000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027834881389, 0, 0, 0, 0, 0, 3995538948023, 0, 3995538948023, 0, 0, 0, 11435860839103, 0, 3928353832517, 0, 11435860839103, 0, 0, 0, 0, 0, 0, 0, 3995538948023, 0, 3995538948023, 0, 0, 0, 3928354441091, 0, 256933240037, 0, 3928354441091, 0, 0, 0, 3995538435264, 0, 3995538435264, 0, 0, 0, 0, 0, 0, 0, 11435860839103, 0, 3928353832517, 0, 11435860839103, 0, 0, 0, 3995538435264, 0, 3995538435264, 0, 0, 0, 0, 0, 8027659196199, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027834881388, 0, 0, 0, 0, 0, 3995538948022, 0, 3995538948022, 0, 0, 0, 11435860839102, 0, 3928353832516, 0, 11435860839102, 0, 0, 0, 0, 0, 0, 0, 3995538948022, 0, 3995538948022, 0, 0, 0, 3928354441090, 0, 256933240036, 0, 3928354441090, 0, 0, 0, 3995538435263, 0, 3995538435263, 0, 0, 0, 0, 0, 0, 0, 11435860839102, 0, 3928353832516, 0, 11435860839102, 0, 0, 0, 3995538435263, 0, 3995538435263, 0, 0, 0, 0, 0, 8027659196198, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1101692072 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 57) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 57 c : ℚ) *
        (((integerProfile 1 1 2) ⟨57, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨57, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨57, complement (parent_total 1 57) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨57, complement (parent_total 1 57) c⟩ v : ℕ))) /
      (size 1 1 57 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 57 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1101692072 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
