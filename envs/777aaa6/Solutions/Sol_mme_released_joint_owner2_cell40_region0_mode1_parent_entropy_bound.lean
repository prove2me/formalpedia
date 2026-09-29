-- Prove2me | solution 1 for mme_released_joint_owner2_cell40_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:00:40.668337+00:00
-- url     : https://prove2.me/submissions/b534aba6-059f-4404-b9f9-a1b48b96fca4

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2499731810974895691645000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 113606051391050208616710000000000000, 0, 0, 0, 0, 0, 190693480863250000000000000000000000, 0, 190693480863250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2499731810974895691645000000000000, 0, 0, 0, 0, 0, 190693480863250000000000000000000000, 0, 190693480863250000000000000000000000, 0, 0, 0, 2500048931702241964110000000000000, 0, 113620463670595516071780000000000000, 0, 2500048931702241964110000000000000, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 9, 0, 4, 0, 9, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5991571828473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2175018504827, 0, 0, 0, 0, 0, 1657087952261, 0, 1657087952261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5991571828473, 0, 0, 0, 0, 0, 1657087952261, 0, 1657087952261, 0, 0, 0, 5991444974619, 0, 2174891650973, 0, 5991444974619, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5991571828472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2175018504826, 0, 0, 0, 0, 0, 1657087952260, 0, 1657087952260, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5991571828472, 0, 0, 0, 0, 0, 1657087952260, 0, 1657087952260, 0, 0, 0, 5991444974618, 0, 2174891650972, 0, 5991444974618, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1818103397 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 130) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 130 c : ℚ) *
        (((integerProfile 0 1 1) ⟨130, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨130, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨130, complement (parent_total 0 130) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨130, complement (parent_total 0 130) c⟩ v : ℕ))) /
      (size 0 1 130 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 130 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1818103397 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
