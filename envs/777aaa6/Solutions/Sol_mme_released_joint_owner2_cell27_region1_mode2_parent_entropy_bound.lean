-- Prove2me | solution 1 for mme_released_joint_owner2_cell27_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:44:00.353977+00:00
-- url     : https://prove2.me/submissions/67a2a958-9569-4e97-b83d-1206f05ccf63

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
  ([0, 0, 0, 0, 0, 6888739711500000000000000000000000, 0, 6888739711500000000000000000000000, 0, 0, 0, 4908157288646149823622000000000000, 0, 233294937259207700352756000000000000, 0, 4908157288646149823622000000000000, 0, 0, 0, 4908159379352173884680000000000000, 0, 4908159379352173884680000000000000, 0, 0, 0, 0, 0, 0, 0, 4908157288646149823622000000000000, 0, 233294937259207700352756000000000000, 0, 4908157288646149823622000000000000, 0, 0, 0, 233294897134295652230640000000000000, 0, 233294897134295652230640000000000000, 0, 0, 0, 0, 0, 6888792559000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4908159379352173884680000000000000, 0, 4908159379352173884680000000000000, 0, 0, 0, 0, 0, 6888792559000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4977867126290, 0, 4977867126290, 0, 0, 0, 5316856705246, 0, 1455451800751, 0, 5316856705246, 0, 0, 0, 5316856279281, 0, 5316856279281, 0, 0, 0, 0, 0, 0, 0, 5316856705246, 0, 1455451800751, 0, 5316856705246, 0, 0, 0, 1455451972744, 0, 1455451972744, 0, 0, 0, 0, 0, 4977859454743, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5316856279281, 0, 5316856279281, 0, 0, 0, 0, 0, 4977859454743, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4977867126289, 0, 4977867126289, 0, 0, 0, 5316856705245, 0, 1455451800750, 0, 5316856705245, 0, 0, 0, 5316856279280, 0, 5316856279280, 0, 0, 0, 0, 0, 0, 0, 5316856705245, 0, 1455451800750, 0, 5316856705245, 0, 0, 0, 1455451972743, 0, 1455451972743, 0, 0, 0, 0, 0, 4977859454741, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5316856279280, 0, 5316856279280, 0, 0, 0, 0, 0, 4977859454741, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1704131241 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 117) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 117 c : ℚ) *
        (((integerProfile 1 1 2) ⟨117, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨117, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨117, complement (parent_total 1 117) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨117, complement (parent_total 1 117) c⟩ v : ℕ))) /
      (size 1 1 117 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 117 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1704131241 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
