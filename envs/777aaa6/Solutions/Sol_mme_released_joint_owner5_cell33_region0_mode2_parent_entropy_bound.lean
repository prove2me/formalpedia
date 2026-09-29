-- Prove2me | solution 1 for mme_released_joint_owner5_cell33_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:09:24.644382+00:00
-- url     : https://prove2.me/submissions/f194b6ec-4eeb-49d0-b000-4d9f41d0b365

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 329930355000000000000000000000000, 0, 0, 0, 0, 0, 20139914286500000000000000000000000, 0, 20139914286500000000000000000000000, 0, 0, 0, 40231038438631764694573295475900, 0, 20557045558448006683792853409048200, 0, 40231038438631764694573295475900, 0, 0, 0, 0, 0, 0, 0, 20139914286500000000000000000000000, 0, 20139914286500000000000000000000000, 0, 0, 0, 20557046980107233098888853409048200, 0, 755831725564134993375858293181903600, 0, 20557046980107233098888853409048200, 0, 0, 0, 20139912076500000000000000000000000, 0, 20139912076500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40231038438631764694573295475900, 0, 20557045558448006683792853409048200, 0, 40231038438631764694573295475900, 0, 0, 0, 20139912076500000000000000000000000, 0, 20139912076500000000000000000000000, 0, 0, 0, 0, 0, 329929398000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8016628971232, 0, 0, 0, 0, 0, 3905051647585, 0, 3905051647585, 0, 0, 0, 10120871759793, 0, 3884551547240, 0, 10120871759793, 0, 0, 0, 0, 0, 0, 0, 3905051647585, 0, 3905051647585, 0, 0, 0, 3884551478084, 0, 279936512811, 0, 3884551478084, 0, 0, 0, 3905051757317, 0, 3905051757317, 0, 0, 0, 0, 0, 0, 0, 10120871759793, 0, 3884551547240, 0, 10120871759793, 0, 0, 0, 3905051757317, 0, 3905051757317, 0, 0, 0, 0, 0, 8016631871848, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8016628971231, 0, 0, 0, 0, 0, 3905051647584, 0, 3905051647584, 0, 0, 0, 10120871759792, 0, 3884551547239, 0, 10120871759792, 0, 0, 0, 0, 0, 0, 0, 3905051647584, 0, 3905051647584, 0, 0, 0, 3884551478083, 0, 279936512810, 0, 3884551478083, 0, 0, 0, 3905051757316, 0, 3905051757316, 0, 0, 0, 0, 0, 0, 0, 10120871759792, 0, 3884551547239, 0, 10120871759792, 0, 0, 0, 3905051757316, 0, 3905051757316, 0, 0, 0, 0, 0, 8016631871847, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1167102280 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 258) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 258 c : ℚ) *
        (((integerProfile 0 1 2) ⟨258, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨258, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨258, complement (parent_total 0 258) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨258, complement (parent_total 0 258) c⟩ v : ℕ))) /
      (size 0 1 258 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 258 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1167102280 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
