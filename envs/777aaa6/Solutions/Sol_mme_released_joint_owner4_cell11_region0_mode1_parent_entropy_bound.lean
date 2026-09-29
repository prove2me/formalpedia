-- Prove2me | solution 1 for mme_released_joint_owner4_cell11_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:07:02.719983+00:00
-- url     : https://prove2.me/submissions/fad6268e-a60d-40dc-8a6e-a3734ad13987

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3317040170500000000000000000000000, 0, 0, 0, 0, 0, 4068834921994338725311500000000000, 0, 4068834921994338725311500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3317040170500000000000000000000000, 0, 0, 0, 0, 0, 238545313075511322549377000000000000, 0, 238545313075511322549377000000000000, 0, 0, 0, 4068833446267423235979500000000000, 0, 238545175160965153528041000000000000, 0, 4068833446267423235979500000000000, 0, 0, 0, 0, 0, 0, 0, 4068834921994338725311500000000000, 0, 4068834921994338725311500000000000, 0, 0, 0, 4068833446267423235979500000000000, 0, 238545175160965153528041000000000000, 0, 4068833446267423235979500000000000, 0, 0, 0, 3317134856500000000000000000000000, 0, 3317134856500000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5708682408600, 0, 0, 0, 0, 0, 5504398580461, 0, 5504398580461, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5708682408600, 0, 0, 0, 0, 0, 1433195994770, 0, 1433195994770, 0, 0, 0, 5504398943151, 0, 1433196572918, 0, 5504398943151, 0, 0, 0, 0, 0, 0, 0, 5504398580461, 0, 5504398580461, 0, 0, 0, 5504398943151, 0, 1433196572918, 0, 5504398943151, 0, 0, 0, 5708653863679, 0, 5708653863679, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5708682408599, 0, 0, 0, 0, 0, 5504398580460, 0, 5504398580460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5708682408599, 0, 0, 0, 0, 0, 1433195994769, 0, 1433195994769, 0, 0, 0, 5504398943150, 0, 1433196572917, 0, 5504398943150, 0, 0, 0, 0, 0, 0, 0, 5504398580460, 0, 5504398580460, 0, 0, 0, 5504398943150, 0, 1433196572917, 0, 5504398943150, 0, 0, 0, 5708653863678, 0, 5708653863678, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1622445123 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 191) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 191 c : ℚ) *
        (((integerProfile 0 1 1) ⟨191, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨191, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨191, complement (parent_total 0 191) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨191, complement (parent_total 0 191) c⟩ v : ℕ))) /
      (size 0 1 191 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 191 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1622445123 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
