-- Prove2me | solution 1 for mme_released_joint_owner0_cell25_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:38:23.534682+00:00
-- url     : https://prove2.me/submissions/766c67c3-8d9d-4967-a1e7-0b89bf1bf685

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328196851000000000000000000000000, 0, 0, 0, 0, 0, 17655290679500000000000000000000000, 0, 17655290679500000000000000000000000, 0, 0, 0, 24583758032650171400740984756412, 0, 19829694950787075366769518030487176, 0, 24583758032650171400740984756412, 0, 0, 0, 0, 0, 0, 0, 17655290679500000000000000000000000, 0, 17655290679500000000000000000000000, 0, 0, 0, 19829695079892091080065518030487176, 0, 778684170112511066420726963939025648, 0, 19829695079892091080065518030487176, 0, 0, 0, 17655289462750000000000000000000000, 0, 17655289462750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 24583758032650171400740984756412, 0, 19829694950787075366769518030487176, 0, 24583758032650171400740984756412, 0, 0, 0, 17655289462750000000000000000000000, 0, 17655289462750000000000000000000000, 0, 0, 0, 0, 0, 328197374000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021896974114, 0, 0, 0, 0, 0, 4036719785308, 0, 4036719785308, 0, 0, 0, 10613424575658, 0, 3920574719787, 0, 10613424575658, 0, 0, 0, 0, 0, 0, 0, 4036719785308, 0, 4036719785308, 0, 0, 0, 3920574713277, 0, 250149745215, 0, 3920574713277, 0, 0, 0, 4036719854226, 0, 4036719854226, 0, 0, 0, 0, 0, 0, 0, 10613424575658, 0, 3920574719787, 0, 10613424575658, 0, 0, 0, 4036719854226, 0, 4036719854226, 0, 0, 0, 0, 0, 8021895380560, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021896974113, 0, 0, 0, 0, 0, 4036719785307, 0, 4036719785307, 0, 0, 0, 10613424575657, 0, 3920574719786, 0, 10613424575657, 0, 0, 0, 0, 0, 0, 0, 4036719785307, 0, 4036719785307, 0, 0, 0, 3920574713276, 0, 250149745214, 0, 3920574713276, 0, 0, 0, 4036719854225, 0, 4036719854225, 0, 0, 0, 0, 0, 0, 0, 10613424575657, 0, 3920574719786, 0, 10613424575657, 0, 0, 0, 4036719854225, 0, 4036719854225, 0, 0, 0, 0, 0, 8021895380559, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1082227723 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 25) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 25 c : ℚ) *
        (((integerProfile 1 1 1) ⟨25, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨25, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨25, complement (parent_total 1 25) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨25, complement (parent_total 1 25) c⟩ v : ℕ))) /
      (size 1 1 25 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 25 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1082227723 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
