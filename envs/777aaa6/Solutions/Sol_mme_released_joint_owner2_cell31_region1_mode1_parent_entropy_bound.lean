-- Prove2me | solution 1 for mme_released_joint_owner2_cell31_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:55:32.18447+00:00
-- url     : https://prove2.me/submissions/ae311883-b233-452b-8b81-7e278bb562f2

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
  ([0, 0, 0, 0, 0, 6520796223500000000000000000000000, 0, 6520796223500000000000000000000000, 0, 0, 0, 10806027953263392982306000000000000, 0, 221867122104473214035388000000000000, 0, 10806027953263392982306000000000000, 0, 0, 0, 10806034982829102473689000000000000, 0, 10806034982829102473689000000000000, 0, 0, 0, 0, 0, 0, 0, 10806027953263392982306000000000000, 0, 221867122104473214035388000000000000, 0, 10806027953263392982306000000000000, 0, 0, 0, 221867318769341795052622000000000000, 0, 221867318769341795052622000000000000, 0, 0, 0, 0, 0, 6520637030500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10806034982829102473689000000000000, 0, 10806034982829102473689000000000000, 0, 0, 0, 0, 0, 6520637030500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5032758790331, 0, 5032758790331, 0, 0, 0, 4527651156736, 0, 1505676625391, 0, 4527651156736, 0, 0, 0, 4527650506214, 0, 4527650506214, 0, 0, 0, 0, 0, 0, 0, 4527651156736, 0, 1505676625391, 0, 4527651156736, 0, 0, 0, 1505675738983, 0, 1505675738983, 0, 0, 0, 0, 0, 5032783203752, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4527650506214, 0, 4527650506214, 0, 0, 0, 0, 0, 5032783203752, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5032758790330, 0, 5032758790330, 0, 0, 0, 4527651156735, 0, 1505676625390, 0, 4527651156735, 0, 0, 0, 4527650506213, 0, 4527650506213, 0, 0, 0, 0, 0, 0, 0, 4527651156735, 0, 1505676625390, 0, 4527651156735, 0, 0, 0, 1505675738982, 0, 1505675738982, 0, 0, 0, 0, 0, 5032783203751, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4527650506213, 0, 4527650506213, 0, 0, 0, 0, 0, 5032783203751, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1858917350 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 121) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 121 c : ℚ) *
        (((integerProfile 1 1 1) ⟨121, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨121, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨121, complement (parent_total 1 121) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨121, complement (parent_total 1 121) c⟩ v : ℕ))) /
      (size 1 1 121 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 121 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1858917350 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
