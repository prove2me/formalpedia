-- Prove2me | solution 1 for mme_released_joint_owner4_cell11_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:51:00.817592+00:00
-- url     : https://prove2.me/submissions/ca1ded10-a2c6-43f6-9e27-182901665299

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3305954747000000000000000000000000, 0, 0, 0, 0, 0, 4106402068354898114572000000000000, 0, 4106402068354898114572000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3305954747000000000000000000000000, 0, 0, 0, 0, 0, 238481239566790203770856000000000000, 0, 238481239566790203770856000000000000, 0, 0, 0, 4106402160018437605172000000000000, 0, 238481225844463124789656000000000000, 0, 4106402160018437605172000000000000, 0, 0, 0, 0, 0, 0, 0, 4106402068354898114572000000000000, 0, 4106402068354898114572000000000000, 0, 0, 0, 4106402160018437605172000000000000, 0, 238481225844463124789656000000000000, 0, 4106402160018437605172000000000000, 0, 0, 0, 3305971385000000000000000000000000, 0, 3305971385000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5712029967820, 0, 0, 0, 0, 0, 5495208043028, 0, 5495208043028, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5712029967820, 0, 0, 0, 0, 0, 1433464631845, 0, 1433464631845, 0, 0, 0, 5495208020706, 0, 1433464689386, 0, 5495208020706, 0, 0, 0, 0, 0, 0, 0, 5495208043028, 0, 5495208043028, 0, 0, 0, 5495208020706, 0, 1433464689386, 0, 5495208020706, 0, 0, 0, 5712024935096, 0, 5712024935096, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5712029967819, 0, 0, 0, 0, 0, 5495208043027, 0, 5495208043027, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5712029967819, 0, 0, 0, 0, 0, 1433464631844, 0, 1433464631844, 0, 0, 0, 5495208020705, 0, 1433464689385, 0, 5495208020705, 0, 0, 0, 0, 0, 0, 0, 5495208043027, 0, 5495208043027, 0, 0, 0, 5495208020705, 0, 1433464689385, 0, 5495208020705, 0, 0, 0, 5712024935095, 0, 5712024935095, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1623476955 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 191) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 191 c : ℚ) *
        (((integerProfile 1 1 2) ⟨191, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨191, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨191, complement (parent_total 1 191) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨191, complement (parent_total 1 191) c⟩ v : ℕ))) /
      (size 1 1 191 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 191 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1623476955 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
