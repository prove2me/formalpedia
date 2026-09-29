-- Prove2me | solution 1 for mme_released_joint_owner1_cell28_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:49:52.679904+00:00
-- url     : https://prove2.me/submissions/7c857c2c-db27-413a-9edf-6fe98d0b6799

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328253343000000000000000000000000, 0, 0, 0, 0, 0, 18719454810500000000000000000000000, 0, 18719454810500000000000000000000000, 0, 0, 0, 47637708272658571482750336768264, 0, 20472564350899418745958499326463472, 0, 47637708272658571482750336768264, 0, 0, 0, 0, 0, 0, 0, 18719454810500000000000000000000000, 0, 18719454810500000000000000000000000, 0, 0, 0, 20472564453347433722833499326463472, 0, 767507045917415660776485001347073056, 0, 20472564453347433722833499326463472, 0, 0, 0, 18719455399500000000000000000000000, 0, 18719455399500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 47637708272658571482750336768264, 0, 20472564350899418745958499326463472, 0, 47637708272658571482750336768264, 0, 0, 0, 18719455399500000000000000000000000, 0, 18719455399500000000000000000000000, 0, 0, 0, 0, 0, 328251458000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021724860523, 0, 0, 0, 0, 0, 3978191931728, 0, 3978191931728, 0, 0, 0, 9951885919743, 0, 3888669613541, 0, 9951885919743, 0, 0, 0, 0, 0, 0, 0, 3978191931728, 0, 3978191931728, 0, 0, 0, 3888669608536, 0, 264607619215, 0, 3888669608536, 0, 0, 0, 3978191900263, 0, 3978191900263, 0, 0, 0, 0, 0, 0, 0, 9951885919743, 0, 3888669613541, 0, 9951885919743, 0, 0, 0, 3978191900263, 0, 3978191900263, 0, 0, 0, 0, 0, 8021730603055, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021724860522, 0, 0, 0, 0, 0, 3978191931727, 0, 3978191931727, 0, 0, 0, 9951885919742, 0, 3888669613540, 0, 9951885919742, 0, 0, 0, 0, 0, 0, 0, 3978191931727, 0, 3978191931727, 0, 0, 0, 3888669608535, 0, 264607619214, 0, 3888669608535, 0, 0, 0, 3978191900262, 0, 3978191900262, 0, 0, 0, 0, 0, 0, 0, 9951885919742, 0, 3888669613540, 0, 9951885919742, 0, 0, 0, 3978191900262, 0, 3978191900262, 0, 0, 0, 0, 0, 8021730603054, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1124451691 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 73) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 73 c : ℚ) *
        (((integerProfile 1 1 1) ⟨73, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨73, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨73, complement (parent_total 1 73) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨73, complement (parent_total 1 73) c⟩ v : ℕ))) /
      (size 1 1 73 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 73 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1124451691 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
