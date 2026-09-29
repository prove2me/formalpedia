-- Prove2me | solution 1 for mme_released_joint_owner5_cell21_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T19:03:47.715731+00:00
-- url     : https://prove2.me/submissions/d7740a8d-662c-41ed-a744-93e08613def6

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 333657778000000000000000000000000, 0, 0, 0, 0, 0, 19386728788500000000000000000000000, 0, 19386728788500000000000000000000000, 0, 0, 0, 812955975618347484442869062800988, 0, 15893610481372906580011261874398024, 0, 812955975618347484442869062800988, 0, 0, 0, 0, 0, 0, 0, 19386728788500000000000000000000000, 0, 19386728788500000000000000000000000, 0, 0, 0, 15893610486555389076562261874398024, 0, 777412624864670018749081476251203952, 0, 15893610486555389076562261874398024, 0, 0, 0, 19386704332000000000000000000000000, 0, 19386704332000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 812955975618347484442869062800988, 0, 15893610481372906580011261874398024, 0, 812955975618347484442869062800988, 0, 0, 0, 19386704332000000000000000000000000, 0, 19386704332000000000000000000000000, 0, 0, 0, 0, 0, 333719037000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8005394707033, 0, 0, 0, 0, 0, 3943166530072, 0, 3943166530072, 0, 0, 0, 7114833600414, 0, 4141838107040, 0, 7114833600414, 0, 0, 0, 0, 0, 0, 0, 3943166530072, 0, 3943166530072, 0, 0, 0, 4141838106714, 0, 251784020840, 0, 4141838106714, 0, 0, 0, 3943167791580, 0, 3943167791580, 0, 0, 0, 0, 0, 0, 0, 7114833600414, 0, 4141838107040, 0, 7114833600414, 0, 0, 0, 3943167791580, 0, 3943167791580, 0, 0, 0, 0, 0, 8005211125588, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8005394707032, 0, 0, 0, 0, 0, 3943166530071, 0, 3943166530071, 0, 0, 0, 7114833600413, 0, 4141838107039, 0, 7114833600413, 0, 0, 0, 0, 0, 0, 0, 3943166530071, 0, 3943166530071, 0, 0, 0, 4141838106713, 0, 251784020839, 0, 4141838106713, 0, 0, 0, 3943167791579, 0, 3943167791579, 0, 0, 0, 0, 0, 0, 0, 7114833600413, 0, 4141838107039, 0, 7114833600413, 0, 0, 0, 3943167791579, 0, 3943167791579, 0, 0, 0, 0, 0, 8005211125587, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1099094375 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 246) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 246 c : ℚ) *
        (((integerProfile 1 1 2) ⟨246, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨246, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨246, complement (parent_total 1 246) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨246, complement (parent_total 1 246) c⟩ v : ℕ))) /
      (size 1 1 246 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 246 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1099094375 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
