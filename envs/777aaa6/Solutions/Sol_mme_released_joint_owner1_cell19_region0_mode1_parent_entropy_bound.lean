-- Prove2me | solution 1 for mme_released_joint_owner1_cell19_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:45:19.657969+00:00
-- url     : https://prove2.me/submissions/10375cd6-ad12-464d-a1a4-34ed68eb64dc

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 318870682000000000000000000000000, 0, 0, 0, 0, 0, 17942152725500000000000000000000000, 0, 17942152725500000000000000000000000, 0, 0, 0, 596469938360997299714176992624716, 0, 19045728800533314385609646014750568, 0, 596469938360997299714176992624716, 0, 0, 0, 0, 0, 0, 0, 17942152725500000000000000000000000, 0, 17942152725500000000000000000000000, 0, 0, 0, 19045728751676471553353646014750568, 0, 777256297253136438923216707970498864, 0, 19045728751676471553353646014750568, 0, 0, 0, 17942131384500000000000000000000000, 0, 17942131384500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 596469938360997299714176992624716, 0, 19045728800533314385609646014750568, 0, 596469938360997299714176992624716, 0, 0, 0, 17942131384500000000000000000000000, 0, 17942131384500000000000000000000000, 0, 0, 0, 0, 0, 318900767000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050724922951, 0, 0, 0, 0, 0, 4020602433704, 0, 4020602433704, 0, 0, 0, 7424481714409, 0, 3960912412494, 0, 7424481714409, 0, 0, 0, 0, 0, 0, 0, 4020602433704, 0, 4020602433704, 0, 0, 0, 3960912415060, 0, 251985128111, 0, 3960912415060, 0, 0, 0, 4020603623138, 0, 4020603623138, 0, 0, 0, 0, 0, 0, 0, 7424481714409, 0, 3960912412494, 0, 7424481714409, 0, 0, 0, 4020603623138, 0, 4020603623138, 0, 0, 0, 0, 0, 8050630578809, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050724922950, 0, 0, 0, 0, 0, 4020602433703, 0, 4020602433703, 0, 0, 0, 7424481714408, 0, 3960912412493, 0, 7424481714408, 0, 0, 0, 0, 0, 0, 0, 4020602433703, 0, 4020602433703, 0, 0, 0, 3960912415059, 0, 251985128110, 0, 3960912415059, 0, 0, 0, 4020603623137, 0, 4020603623137, 0, 0, 0, 0, 0, 0, 0, 7424481714408, 0, 3960912412493, 0, 7424481714408, 0, 0, 0, 4020603623137, 0, 4020603623137, 0, 0, 0, 0, 0, 8050630578808, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1097565140 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 64) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 64 c : ℚ) *
        (((integerProfile 0 1 1) ⟨64, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨64, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨64, complement (parent_total 0 64) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨64, complement (parent_total 0 64) c⟩ v : ℕ))) /
      (size 0 1 64 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 64 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1097565140 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
