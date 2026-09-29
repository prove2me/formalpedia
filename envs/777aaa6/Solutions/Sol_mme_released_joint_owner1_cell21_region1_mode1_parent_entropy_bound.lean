-- Prove2me | solution 1 for mme_released_joint_owner1_cell21_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:47:37.059649+00:00
-- url     : https://prove2.me/submissions/0cab1e50-40aa-4081-8923-e3ff44485dae

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328671728000000000000000000000000, 0, 0, 0, 0, 0, 19044727436000000000000000000000000, 0, 19044727436000000000000000000000000, 0, 0, 0, 656061156100115884108242255694478, 0, 20113165000526984007643515488611044, 0, 656061156100115884108242255694478, 0, 0, 0, 0, 0, 0, 0, 19044727436000000000000000000000000, 0, 19044727436000000000000000000000000, 0, 0, 0, 20113165003732116375105515488611044, 0, 763907931411081335698068969022777912, 0, 20113165003732116375105515488611044, 0, 0, 0, 19044727325500000000000000000000000, 0, 19044727325500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 656061156100115884108242255694478, 0, 20113165000526984007643515488611044, 0, 656061156100115884108242255694478, 0, 0, 0, 19044727325500000000000000000000000, 0, 19044727325500000000000000000000000, 0, 0, 0, 0, 0, 328673182000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020451092555, 0, 0, 0, 0, 0, 3960964990732, 0, 3960964990732, 0, 0, 0, 7329256547604, 0, 3906380703170, 0, 7329256547604, 0, 0, 0, 0, 0, 0, 0, 3960964990732, 0, 3960964990732, 0, 0, 0, 3906380703010, 0, 269308005702, 0, 3906380703010, 0, 0, 0, 3960964996534, 0, 3960964996534, 0, 0, 0, 0, 0, 0, 0, 7329256547604, 0, 3906380703170, 0, 7329256547604, 0, 0, 0, 3960964996534, 0, 3960964996534, 0, 0, 0, 0, 0, 8020446668697, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8020451092553, 0, 0, 0, 0, 0, 3960964990731, 0, 3960964990731, 0, 0, 0, 7329256547603, 0, 3906380703169, 0, 7329256547603, 0, 0, 0, 0, 0, 0, 0, 3960964990731, 0, 3960964990731, 0, 0, 0, 3906380703009, 0, 269308005701, 0, 3906380703009, 0, 0, 0, 3960964996533, 0, 3960964996533, 0, 0, 0, 0, 0, 0, 0, 7329256547603, 0, 3906380703169, 0, 7329256547603, 0, 0, 0, 3960964996533, 0, 3960964996533, 0, 0, 0, 0, 0, 8020446668696, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1147995191 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 66) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 66 c : ℚ) *
        (((integerProfile 1 1 1) ⟨66, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨66, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨66, complement (parent_total 1 66) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨66, complement (parent_total 1 66) c⟩ v : ℕ))) /
      (size 1 1 66 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 66 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1147995191 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
