-- Prove2me | solution 1 for mme_released_joint_owner0_cell21_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:26:30.070532+00:00
-- url     : https://prove2.me/submissions/e7238e60-d3cf-43a0-bd87-e948365b35c2

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 333571569000000000000000000000000, 0, 0, 0, 0, 0, 19386468195000000000000000000000000, 0, 19386468195000000000000000000000000, 0, 0, 0, 813040332035727421511211729453129, 0, 15881227400670682610706576541093742, 0, 813040332035727421511211729453129, 0, 0, 0, 0, 0, 0, 0, 19386468195000000000000000000000000, 0, 19386468195000000000000000000000000, 0, 0, 0, 15881227402106248275236576541093742, 0, 777464075485303228542068846917812516, 0, 15881227402106248275236576541093742, 0, 0, 0, 19386443823250000000000000000000000, 0, 19386443823250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 813040332035727421511211729453129, 0, 15881227400670682610706576541093742, 0, 813040332035727421511211729453129, 0, 0, 0, 19386443823250000000000000000000000, 0, 19386443823250000000000000000000000, 0, 0, 0, 0, 0, 333633939000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8005653115932, 0, 0, 0, 0, 0, 3943179972012, 0, 3943179972012, 0, 0, 0, 7114729840747, 0, 4142617533917, 0, 7114729840747, 0, 0, 0, 0, 0, 0, 0, 3943179972012, 0, 3943179972012, 0, 0, 0, 4142617533826, 0, 251717841160, 0, 4142617533826, 0, 0, 0, 3943181229166, 0, 3943181229166, 0, 0, 0, 0, 0, 0, 0, 7114729840747, 0, 4142617533917, 0, 7114729840747, 0, 0, 0, 3943181229166, 0, 3943181229166, 0, 0, 0, 0, 0, 8005466157043, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8005653115931, 0, 0, 0, 0, 0, 3943179972011, 0, 3943179972011, 0, 0, 0, 7114729840746, 0, 4142617533916, 0, 7114729840746, 0, 0, 0, 0, 0, 0, 0, 3943179972011, 0, 3943179972011, 0, 0, 0, 4142617533825, 0, 251717841159, 0, 4142617533825, 0, 0, 0, 3943181229165, 0, 3943181229165, 0, 0, 0, 0, 0, 0, 0, 7114729840746, 0, 4142617533916, 0, 7114729840746, 0, 0, 0, 3943181229165, 0, 3943181229165, 0, 0, 0, 0, 0, 8005466157042, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1098894963 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 21) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 21 c : ℚ) *
        (((integerProfile 1 1 2) ⟨21, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨21, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨21, complement (parent_total 1 21) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨21, complement (parent_total 1 21) c⟩ v : ℕ))) /
      (size 1 1 21 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 21 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1098894963 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
