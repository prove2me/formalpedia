-- Prove2me | solution 1 for mme_released_joint_owner4_cell19_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:07:48.083449+00:00
-- url     : https://prove2.me/submissions/7e826325-6238-4c1e-a662-37423ca5bc82

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 318804818000000000000000000000000, 0, 0, 0, 0, 0, 17940376261000000000000000000000000, 0, 17940376261000000000000000000000000, 0, 0, 0, 596699107536845178472200002986109, 0, 19051339465018231752992599994027782, 0, 596699107536845178472200002986109, 0, 0, 0, 0, 0, 0, 0, 17940376261000000000000000000000000, 0, 17940376261000000000000000000000000, 0, 0, 0, 19051339406536772046018599994027782, 0, 777247274417742611688088800011944436, 0, 19051339406536772046018599994027782, 0, 0, 0, 17940356675750000000000000000000000, 0, 17940356675750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 596699107536845178472200002986109, 0, 19051339465018231752992599994027782, 0, 596699107536845178472200002986109, 0, 0, 0, 17940356675750000000000000000000000, 0, 17940356675750000000000000000000000, 0, 0, 0, 0, 0, 318834844000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050931498239, 0, 0, 0, 0, 0, 4020701449272, 0, 4020701449272, 0, 0, 0, 7424097579103, 0, 3960617866757, 0, 7424097579103, 0, 0, 0, 0, 0, 0, 0, 4020701449272, 0, 4020701449272, 0, 0, 0, 3960617869827, 0, 251996736750, 0, 3960617869827, 0, 0, 0, 4020702540958, 0, 4020702540958, 0, 0, 0, 0, 0, 0, 0, 7424097579103, 0, 3960617866757, 0, 7424097579103, 0, 0, 0, 4020702540958, 0, 4020702540958, 0, 0, 0, 0, 0, 8050837319656, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050931498238, 0, 0, 0, 0, 0, 4020701449271, 0, 4020701449271, 0, 0, 0, 7424097579102, 0, 3960617866756, 0, 7424097579102, 0, 0, 0, 0, 0, 0, 0, 4020701449271, 0, 4020701449271, 0, 0, 0, 3960617869826, 0, 251996736749, 0, 3960617869826, 0, 0, 0, 4020702540957, 0, 4020702540957, 0, 0, 0, 0, 0, 0, 0, 7424097579102, 0, 3960617866756, 0, 7424097579102, 0, 0, 0, 4020702540957, 0, 4020702540957, 0, 0, 0, 0, 0, 8050837319655, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1097600389 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 199) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 199 c : ℚ) *
        (((integerProfile 0 1 1) ⟨199, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨199, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨199, complement (parent_total 0 199) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨199, complement (parent_total 0 199) c⟩ v : ℕ))) /
      (size 0 1 199 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 199 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1097600389 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
