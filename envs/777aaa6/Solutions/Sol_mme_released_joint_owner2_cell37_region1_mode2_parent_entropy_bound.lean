-- Prove2me | solution 1 for mme_released_joint_owner2_cell37_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:45:14.327703+00:00
-- url     : https://prove2.me/submissions/4819a4b4-e19d-4492-b56f-68b98666b2a5

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3675964853500000000000000000000000, 0, 0, 0, 0, 0, 5024449369523113631055000000000000, 0, 5024449369523113631055000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3675964853500000000000000000000000, 0, 0, 0, 0, 0, 236275140746453772737890000000000000, 0, 236275140746453772737890000000000000, 0, 0, 0, 5024439495331795002789000000000000, 0, 236274703442336409994422000000000000, 0, 5024439495331795002789000000000000, 0, 0, 0, 0, 0, 0, 0, 5024449369523113631055000000000000, 0, 5024449369523113631055000000000000, 0, 0, 0, 5024439495331795002789000000000000, 0, 236274703442336409994422000000000000, 0, 5024439495331795002789000000000000, 0, 0, 0, 3676413228000000000000000000000000, 0, 3676413228000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5605939635607, 0, 0, 0, 0, 0, 5293439409246, 0, 5293439409246, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5605939635607, 0, 0, 0, 0, 0, 1442758302413, 0, 1442758302413, 0, 0, 0, 5293441374476, 0, 1442760153240, 0, 5293441374476, 0, 0, 0, 0, 0, 0, 0, 5293439409246, 0, 5293439409246, 0, 0, 0, 5293441374476, 0, 1442760153240, 0, 5293441374476, 0, 0, 0, 5605817668402, 0, 5605817668402, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5605939635606, 0, 0, 0, 0, 0, 5293439409245, 0, 5293439409245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5605939635606, 0, 0, 0, 0, 0, 1442758302412, 0, 1442758302412, 0, 0, 0, 5293441374475, 0, 1442760153239, 0, 5293441374475, 0, 0, 0, 0, 0, 0, 0, 5293439409245, 0, 5293439409245, 0, 0, 0, 5293441374475, 0, 1442760153239, 0, 5293441374475, 0, 0, 0, 5605817668401, 0, 5605817668401, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1658757152 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 127) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 127 c : ℚ) *
        (((integerProfile 1 1 2) ⟨127, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨127, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨127, complement (parent_total 1 127) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨127, complement (parent_total 1 127) c⟩ v : ℕ))) /
      (size 1 1 127 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 127 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1658757152 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
