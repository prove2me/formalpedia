-- Prove2me | solution 1 for mme_released_joint_owner3_cell28_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:04:04.27878+00:00
-- url     : https://prove2.me/submissions/d1a8b14f-c27f-45e9-8903-a7a0ecaf2503

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
  ([0, 0, 0, 0, 0, 6475513599000000000000000000000000, 0, 6475513599000000000000000000000000, 0, 0, 0, 10734624666385098789873000000000000, 0, 222055241960229802420254000000000000, 0, 10734624666385098789873000000000000, 0, 0, 0, 10734623714276370398344000000000000, 0, 10734623714276370398344000000000000, 0, 0, 0, 0, 0, 0, 0, 10734624666385098789873000000000000, 0, 222055241960229802420254000000000000, 0, 10734624666385098789873000000000000, 0, 0, 0, 222055216391447259203312000000000000, 0, 222055216391447259203312000000000000, 0, 0, 0, 0, 0, 6475531288000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10734623714276370398344000000000000, 0, 10734623714276370398344000000000000, 0, 0, 0, 0, 0, 6475531288000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5039727354234, 0, 5039727354234, 0, 0, 0, 4534280811804, 0, 1504829090407, 0, 4534280811804, 0, 0, 0, 4534280900499, 0, 4534280900499, 0, 0, 0, 0, 0, 0, 0, 4534280811804, 0, 1504829090407, 0, 4534280811804, 0, 0, 0, 1504829205553, 0, 1504829205553, 0, 0, 0, 0, 0, 5039724622562, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4534280900499, 0, 4534280900499, 0, 0, 0, 0, 0, 5039724622562, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5039727354233, 0, 5039727354233, 0, 0, 0, 4534280811803, 0, 1504829090406, 0, 4534280811803, 0, 0, 0, 4534280900498, 0, 4534280900498, 0, 0, 0, 0, 0, 0, 0, 4534280811803, 0, 1504829090406, 0, 4534280811803, 0, 0, 0, 1504829205552, 0, 1504829205552, 0, 0, 0, 0, 0, 5039724622561, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4534280900498, 0, 4534280900498, 0, 0, 0, 0, 0, 5039724622561, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1856550568 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 163) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 163 c : ℚ) *
        (((integerProfile 0 1 1) ⟨163, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨163, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨163, complement (parent_total 0 163) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨163, complement (parent_total 0 163) c⟩ v : ℕ))) /
      (size 0 1 163 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 163 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1856550568 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
