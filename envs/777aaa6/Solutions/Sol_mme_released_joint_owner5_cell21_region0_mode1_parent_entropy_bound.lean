-- Prove2me | solution 1 for mme_released_joint_owner5_cell21_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:15:11.729798+00:00
-- url     : https://prove2.me/submissions/837b4aed-9880-4d02-81fa-3fbad404028e

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328805138000000000000000000000000, 0, 0, 0, 0, 0, 19046862918500000000000000000000000, 0, 19046862918500000000000000000000000, 0, 0, 0, 655959098071729451224364198692100, 0, 20112781876035644630119271602615800, 0, 655959098071729451224364198692100, 0, 0, 0, 0, 0, 0, 0, 19046862918500000000000000000000000, 0, 19046862918500000000000000000000000, 0, 0, 0, 20112781063476591056969271602615800, 0, 763892563129688610820925456794768400, 0, 20112781063476591056969271602615800, 0, 0, 0, 19046848160250000000000000000000000, 0, 19046848160250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 655959098071729451224364198692100, 0, 20112781876035644630119271602615800, 0, 655959098071729451224364198692100, 0, 0, 0, 19046848160250000000000000000000000, 0, 19046848160250000000000000000000000, 0, 0, 0, 0, 0, 328825146000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020045268384, 0, 0, 0, 0, 0, 3960852867165, 0, 3960852867165, 0, 0, 0, 7329412121465, 0, 3906399751795, 0, 7329412121465, 0, 0, 0, 0, 0, 0, 0, 3960852867165, 0, 3960852867165, 0, 0, 0, 3906399792195, 0, 269328123880, 0, 3906399792195, 0, 0, 0, 3960853642004, 0, 3960853642004, 0, 0, 0, 0, 0, 0, 0, 7329412121465, 0, 3906399751795, 0, 7329412121465, 0, 0, 0, 3960853642004, 0, 3960853642004, 0, 0, 0, 0, 0, 8019984419605, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020045268383, 0, 0, 0, 0, 0, 3960852867164, 0, 3960852867164, 0, 0, 0, 7329412121464, 0, 3906399751794, 0, 7329412121464, 0, 0, 0, 0, 0, 0, 0, 3960852867164, 0, 3960852867164, 0, 0, 0, 3906399792194, 0, 269328123879, 0, 3906399792194, 0, 0, 0, 3960853642003, 0, 3960853642003, 0, 0, 0, 0, 0, 0, 0, 7329412121464, 0, 3906399751794, 0, 7329412121464, 0, 0, 0, 3960853642003, 0, 3960853642003, 0, 0, 0, 0, 0, 8019984419604, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1148051791 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 246) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 246 c : ℚ) *
        (((integerProfile 0 1 1) ⟨246, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨246, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨246, complement (parent_total 0 246) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨246, complement (parent_total 0 246) c⟩ v : ℕ))) /
      (size 0 1 246 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 246 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1148051791 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
