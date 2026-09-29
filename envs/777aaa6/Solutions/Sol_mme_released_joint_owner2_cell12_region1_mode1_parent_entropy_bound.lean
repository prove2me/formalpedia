-- Prove2me | solution 1 for mme_released_joint_owner2_cell12_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:53:10.571895+00:00
-- url     : https://prove2.me/submissions/9f9aa433-860c-4bff-8ce4-4a09845e3874

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 325728024000000000000000000000000, 0, 0, 0, 0, 0, 17651277955000000000000000000000000, 0, 17651277955000000000000000000000000, 0, 0, 0, 24768192236119643128615940150932, 0, 19795331493275353526623768119698136, 0, 24768192236119643128615940150932, 0, 0, 0, 0, 0, 0, 0, 17651277955000000000000000000000000, 0, 17651277955000000000000000000000000, 0, 0, 0, 19795331044274322614638768119698136, 0, 778857921248956169144960463760603728, 0, 19795331044274322614638768119698136, 0, 0, 0, 17651279289750000000000000000000000, 0, 17651279289750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 24768192236119643128615940150932, 0, 19795331493275353526623768119698136, 0, 24768192236119643128615940150932, 0, 0, 0, 17651279289750000000000000000000000, 0, 17651279289750000000000000000000000, 0, 0, 0, 0, 0, 325723904000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8029447807014, 0, 0, 0, 0, 0, 4036947092842, 0, 4036947092842, 0, 0, 0, 10605950299116, 0, 3922309152251, 0, 10605950299116, 0, 0, 0, 0, 0, 0, 0, 4036947092842, 0, 4036947092842, 0, 0, 0, 3922309174933, 0, 249926635819, 0, 3922309174933, 0, 0, 0, 4036947017224, 0, 4036947017224, 0, 0, 0, 0, 0, 0, 0, 10605950299116, 0, 3922309152251, 0, 10605950299116, 0, 0, 0, 4036947017224, 0, 4036947017224, 0, 0, 0, 0, 0, 8029460455683, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8029447807013, 0, 0, 0, 0, 0, 4036947092841, 0, 4036947092841, 0, 0, 0, 10605950299115, 0, 3922309152250, 0, 10605950299115, 0, 0, 0, 0, 0, 0, 0, 4036947092841, 0, 4036947092841, 0, 0, 0, 3922309174932, 0, 249926635818, 0, 3922309174932, 0, 0, 0, 4036947017223, 0, 4036947017223, 0, 0, 0, 0, 0, 0, 0, 10605950299115, 0, 3922309152250, 0, 10605950299115, 0, 0, 0, 4036947017223, 0, 4036947017223, 0, 0, 0, 0, 0, 8029460455682, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1081570759 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 102) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 102 c : ℚ) *
        (((integerProfile 1 1 1) ⟨102, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨102, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨102, complement (parent_total 1 102) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨102, complement (parent_total 1 102) c⟩ v : ℕ))) /
      (size 1 1 102 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 102 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1081570759 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
