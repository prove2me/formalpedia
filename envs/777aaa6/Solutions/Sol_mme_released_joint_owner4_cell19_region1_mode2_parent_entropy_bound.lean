-- Prove2me | solution 1 for mme_released_joint_owner4_cell19_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:55:07.965136+00:00
-- url     : https://prove2.me/submissions/fe9e55f5-38b5-4d13-a9ae-6fc9e67fa0ac

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 319717447000000000000000000000000, 0, 0, 0, 0, 0, 18245739670750000000000000000000000, 0, 18245739670750000000000000000000000, 0, 0, 0, 805846262056422442501046858618544, 0, 14625378794470089094569906282762912, 0, 805846262056422442501046858618544, 0, 0, 0, 0, 0, 0, 0, 18245739670750000000000000000000000, 0, 18245739670750000000000000000000000, 0, 0, 0, 14625378794496496024323906282762912, 0, 791669752263841139992208187434474176, 0, 14625378794496496024323906282762912, 0, 0, 0, 18245723195750000000000000000000000, 0, 18245723195750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 805846262056422442501046858618544, 0, 14625378794470089094569906282762912, 0, 805846262056422442501046858618544, 0, 0, 0, 18245723195750000000000000000000000, 0, 18245723195750000000000000000000000, 0, 0, 0, 0, 0, 319778597000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 7, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 7, 0, 1, 0, 7, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 7, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8048072930351, 0, 0, 0, 0, 0, 4003823668905, 0, 4003823668905, 0, 0, 0, 7123617575517, 0, 4224996985724, 0, 7123617575517, 0, 0, 0, 0, 0, 0, 0, 4003823668905, 0, 4003823668905, 0, 0, 0, 4224996985722, 0, 233610953593, 0, 4224996985722, 0, 0, 0, 4003824571856, 0, 4003824571856, 0, 0, 0, 0, 0, 0, 0, 7123617575517, 0, 4224996985724, 0, 7123617575517, 0, 0, 0, 4003824571856, 0, 4003824571856, 0, 0, 0, 0, 0, 8047881686008, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8048072930350, 0, 0, 0, 0, 0, 4003823668904, 0, 4003823668904, 0, 0, 0, 7123617575516, 0, 4224996985723, 0, 7123617575516, 0, 0, 0, 0, 0, 0, 0, 4003823668904, 0, 4003823668904, 0, 0, 0, 4224996985721, 0, 233610953592, 0, 4224996985721, 0, 0, 0, 4003824571855, 0, 4003824571855, 0, 0, 0, 0, 0, 0, 0, 7123617575516, 0, 4224996985723, 0, 7123617575516, 0, 0, 0, 4003824571855, 0, 4003824571855, 0, 0, 0, 0, 0, 8047881686007, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1044641859 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 199) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 199 c : ℚ) *
        (((integerProfile 1 1 2) ⟨199, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨199, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨199, complement (parent_total 1 199) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨199, complement (parent_total 1 199) c⟩ v : ℕ))) /
      (size 1 1 199 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 199 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1044641859 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
