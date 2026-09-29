-- Prove2me | solution 1 for mme_released_joint_owner4_cell12_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:51:23.238075+00:00
-- url     : https://prove2.me/submissions/754a526a-2b3d-4c7f-a593-c1f7fe2a2f96

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 323417201000000000000000000000000, 0, 0, 0, 0, 0, 18399685899500000000000000000000000, 0, 18399685899500000000000000000000000, 0, 0, 0, 10819262000892878576491713406284, 0, 19679916881547915862043016573187432, 0, 10819262000892878576491713406284, 0, 0, 0, 0, 0, 0, 0, 18399685899500000000000000000000000, 0, 18399685899500000000000000000000000, 0, 0, 0, 19679918879160932018851016573187432, 0, 773392746106578732723905966853625136, 0, 19679918879160932018851016573187432, 0, 0, 0, 18399679844000000000000000000000000, 0, 18399679844000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 10819262000892878576491713406284, 0, 19679916881547915862043016573187432, 0, 10819262000892878576491713406284, 0, 0, 0, 18399679844000000000000000000000000, 0, 18399679844000000000000000000000000, 0, 0, 0, 0, 0, 323425149000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8036567424234, 0, 0, 0, 0, 0, 3995421685193, 0, 3995421685193, 0, 0, 0, 11434182493814, 0, 3928156610866, 0, 11434182493814, 0, 0, 0, 0, 0, 0, 0, 3995421685193, 0, 3995421685193, 0, 0, 0, 3928156509361, 0, 256968279079, 0, 3928156509361, 0, 0, 0, 3995422014302, 0, 3995422014302, 0, 0, 0, 0, 0, 0, 0, 11434182493814, 0, 3928156610866, 0, 11434182493814, 0, 0, 0, 3995422014302, 0, 3995422014302, 0, 0, 0, 0, 0, 8036542849467, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8036567424233, 0, 0, 0, 0, 0, 3995421685192, 0, 3995421685192, 0, 0, 0, 11434182493813, 0, 3928156610865, 0, 11434182493813, 0, 0, 0, 0, 0, 0, 0, 3995421685192, 0, 3995421685192, 0, 0, 0, 3928156509360, 0, 256968279078, 0, 3928156509360, 0, 0, 0, 3995422014301, 0, 3995422014301, 0, 0, 0, 0, 0, 0, 0, 11434182493813, 0, 3928156610865, 0, 11434182493813, 0, 0, 0, 3995422014301, 0, 3995422014301, 0, 0, 0, 0, 0, 8036542849466, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1101769778 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 192) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 192 c : ℚ) *
        (((integerProfile 1 1 2) ⟨192, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨192, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨192, complement (parent_total 1 192) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨192, complement (parent_total 1 192) c⟩ v : ℕ))) /
      (size 1 1 192 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 192 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1101769778 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
