-- Prove2me | solution 1 for mme_released_joint_owner4_cell33_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:02:33.513103+00:00
-- url     : https://prove2.me/submissions/b2a7b18f-70f6-4ce6-915a-81648cc96819

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328612996000000000000000000000000, 0, 0, 0, 0, 0, 20121690246750000000000000000000000, 0, 20121690246750000000000000000000000, 0, 0, 0, 40239216114620173457241502367146, 0, 20560594659817182545367516995265708, 0, 40239216114620173457241502367146, 0, 0, 0, 0, 0, 0, 0, 20121690246750000000000000000000000, 0, 20121690246750000000000000000000000, 0, 0, 0, 20560594485270748373523516995265708, 0, 755965914211365657468388966009468584, 0, 20560594485270748373523516995265708, 0, 0, 0, 20121691000500000000000000000000000, 0, 20121691000500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40239216114620173457241502367146, 0, 20560594659817182545367516995265708, 0, 40239216114620173457241502367146, 0, 0, 0, 20121691000500000000000000000000000, 0, 20121691000500000000000000000000000, 0, 0, 0, 0, 0, 328612649000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020629803539, 0, 0, 0, 0, 0, 3905956928992, 0, 3905956928992, 0, 0, 0, 10120668512616, 0, 3884378915671, 0, 10120668512616, 0, 0, 0, 0, 0, 0, 0, 3905956928992, 0, 3905956928992, 0, 0, 0, 3884378924160, 0, 279758990842, 0, 3884378924160, 0, 0, 0, 3905956891532, 0, 3905956891532, 0, 0, 0, 0, 0, 0, 0, 10120668512616, 0, 3884378915671, 0, 10120668512616, 0, 0, 0, 3905956891532, 0, 3905956891532, 0, 0, 0, 0, 0, 8020630859493, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020629803538, 0, 0, 0, 0, 0, 3905956928991, 0, 3905956928991, 0, 0, 0, 10120668512615, 0, 3884378915670, 0, 10120668512615, 0, 0, 0, 0, 0, 0, 0, 3905956928991, 0, 3905956928991, 0, 0, 0, 3884378924159, 0, 279758990841, 0, 3884378924159, 0, 0, 0, 3905956891531, 0, 3905956891531, 0, 0, 0, 0, 0, 0, 0, 10120668512615, 0, 3884378915670, 0, 10120668512615, 0, 0, 0, 3905956891531, 0, 3905956891531, 0, 0, 0, 0, 0, 8020630859492, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1166604829 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 213) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 213 c : ℚ) *
        (((integerProfile 0 1 2) ⟨213, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨213, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨213, complement (parent_total 0 213) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨213, complement (parent_total 0 213) c⟩ v : ℕ))) /
      (size 0 1 213 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 213 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1166604829 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
