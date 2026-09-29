-- Prove2me | solution 1 for mme_released_joint_owner1_cell25_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:48:30.06447+00:00
-- url     : https://prove2.me/submissions/106833f8-0971-43e6-a1b9-dd3f9876b9c5

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328162106000000000000000000000000, 0, 0, 0, 0, 0, 17656337262500000000000000000000000, 0, 17656337262500000000000000000000000, 0, 0, 0, 24543930730399775674739822160800, 0, 19825732784972258961960520355678400, 0, 24543930730399775674739822160800, 0, 0, 0, 0, 0, 0, 0, 17656337262500000000000000000000000, 0, 17656337262500000000000000000000000, 0, 0, 0, 19825732414124843142244520355678400, 0, 778691869246884196688890959288643200, 0, 19825732414124843142244520355678400, 0, 0, 0, 17656336915250000000000000000000000, 0, 17656336915250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 24543930730399775674739822160800, 0, 19825732784972258961960520355678400, 0, 24543930730399775674739822160800, 0, 0, 0, 17656336915250000000000000000000000, 0, 17656336915250000000000000000000000, 0, 0, 0, 0, 0, 328165815000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8022002846060, 0, 0, 0, 0, 0, 4036660508347, 0, 4036660508347, 0, 0, 0, 10615045955046, 0, 3920774549473, 0, 10615045955046, 0, 0, 0, 0, 0, 0, 0, 4036660508347, 0, 4036660508347, 0, 0, 0, 3920774568178, 0, 250139857899, 0, 3920774568178, 0, 0, 0, 4036660528014, 0, 4036660528014, 0, 0, 0, 0, 0, 0, 0, 10615045955046, 0, 3920774549473, 0, 10615045955046, 0, 0, 0, 4036660528014, 0, 4036660528014, 0, 0, 0, 0, 0, 8021991543783, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8022002846059, 0, 0, 0, 0, 0, 4036660508346, 0, 4036660508346, 0, 0, 0, 10615045955045, 0, 3920774549472, 0, 10615045955045, 0, 0, 0, 0, 0, 0, 0, 4036660508346, 0, 4036660508346, 0, 0, 0, 3920774568177, 0, 250139857898, 0, 3920774568177, 0, 0, 0, 4036660528013, 0, 4036660528013, 0, 0, 0, 0, 0, 0, 0, 10615045955045, 0, 3920774549472, 0, 10615045955045, 0, 0, 0, 4036660528013, 0, 4036660528013, 0, 0, 0, 0, 0, 8021991543782, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1082199096 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 70) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 70 c : ℚ) *
        (((integerProfile 0 1 1) ⟨70, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨70, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨70, complement (parent_total 0 70) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨70, complement (parent_total 0 70) c⟩ v : ℕ))) /
      (size 0 1 70 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 70 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1082199096 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
