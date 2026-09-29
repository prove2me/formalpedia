-- Prove2me | solution 1 for mme_released_joint_owner2_cell33_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:44:46.179392+00:00
-- url     : https://prove2.me/submissions/62ccc0bb-550c-41e5-aed3-bd623c82558c

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328658716000000000000000000000000, 0, 0, 0, 0, 0, 20121499558500000000000000000000000, 0, 20121499558500000000000000000000000, 0, 0, 0, 40231067578846561490773501616904, 0, 20560582532709132030018452996766192, 0, 40231067578846561490773501616904, 0, 0, 0, 0, 0, 0, 0, 20121499558500000000000000000000000, 0, 20121499558500000000000000000000000, 0, 0, 0, 20560581112326297792498452996766192, 0, 755967420245613754109003094006467616, 0, 20560581112326297792498452996766192, 0, 0, 0, 20121502041250000000000000000000000, 0, 20121502041250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40231067578846561490773501616904, 0, 20560582532709132030018452996766192, 0, 40231067578846561490773501616904, 0, 0, 0, 20121502041250000000000000000000000, 0, 20121502041250000000000000000000000, 0, 0, 0, 0, 0, 328663079000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020490682992, 0, 0, 0, 0, 0, 3905966405788, 0, 3905966405788, 0, 0, 0, 10120871035471, 0, 3884379505494, 0, 10120871035471, 0, 0, 0, 0, 0, 0, 0, 3905966405788, 0, 3905966405788, 0, 0, 0, 3884379574577, 0, 279756998645, 0, 3884379574577, 0, 0, 0, 3905966282400, 0, 3905966282400, 0, 0, 0, 0, 0, 0, 0, 10120871035471, 0, 3884379505494, 0, 10120871035471, 0, 0, 0, 3905966282400, 0, 3905966282400, 0, 0, 0, 0, 0, 8020477407911, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020490682991, 0, 0, 0, 0, 0, 3905966405787, 0, 3905966405787, 0, 0, 0, 10120871035470, 0, 3884379505493, 0, 10120871035470, 0, 0, 0, 0, 0, 0, 0, 3905966405787, 0, 3905966405787, 0, 0, 0, 3884379574576, 0, 279756998644, 0, 3884379574576, 0, 0, 0, 3905966282399, 0, 3905966282399, 0, 0, 0, 0, 0, 0, 0, 10120871035470, 0, 3884379505493, 0, 10120871035470, 0, 0, 0, 3905966282399, 0, 3905966282399, 0, 0, 0, 0, 0, 8020477407910, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1166599562 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 123) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 123 c : ℚ) *
        (((integerProfile 1 1 2) ⟨123, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨123, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨123, complement (parent_total 1 123) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨123, complement (parent_total 1 123) c⟩ v : ℕ))) /
      (size 1 1 123 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 123 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1166599562 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
