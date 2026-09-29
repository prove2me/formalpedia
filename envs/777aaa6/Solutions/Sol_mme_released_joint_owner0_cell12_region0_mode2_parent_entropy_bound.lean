-- Prove2me | solution 1 for mme_released_joint_owner0_cell12_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:18:08.052777+00:00
-- url     : https://prove2.me/submissions/3b83a918-2dd4-4431-a11f-daac53b15d1a

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 326218906000000000000000000000000, 0, 0, 0, 0, 0, 18396909451750000000000000000000000, 0, 18396909451750000000000000000000000, 0, 0, 0, 10824042074204576331705373265112, 0, 19680081471140888956649589253469776, 0, 10824042074204576331705373265112, 0, 0, 0, 0, 0, 0, 0, 18396909451750000000000000000000000, 0, 18396909451750000000000000000000000, 0, 0, 0, 19680085671525141439669589253469776, 0, 773408686160371120902034821493060448, 0, 19680085671525141439669589253469776, 0, 0, 0, 18396901390000000000000000000000000, 0, 18396901390000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 10824042074204576331705373265112, 0, 19680081471140888956649589253469776, 0, 10824042074204576331705373265112, 0, 0, 0, 18396901390000000000000000000000000, 0, 18396901390000000000000000000000000, 0, 0, 0, 0, 0, 326221113000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027941911150, 0, 0, 0, 0, 0, 3995572593054, 0, 3995572593054, 0, 0, 0, 11433740779982, 0, 3928148247573, 0, 11433740779982, 0, 0, 0, 0, 0, 0, 0, 3995572593054, 0, 3995572593054, 0, 0, 0, 3928148034140, 0, 256947668737, 0, 3928148034140, 0, 0, 0, 3995573031266, 0, 3995573031266, 0, 0, 0, 0, 0, 0, 0, 11433740779982, 0, 3928148247573, 0, 11433740779982, 0, 0, 0, 3995573031266, 0, 3995573031266, 0, 0, 0, 0, 0, 8027935145777, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027941911149, 0, 0, 0, 0, 0, 3995572593053, 0, 3995572593053, 0, 0, 0, 11433740779981, 0, 3928148247572, 0, 11433740779981, 0, 0, 0, 0, 0, 0, 0, 3995572593053, 0, 3995572593053, 0, 0, 0, 3928148034139, 0, 256947668736, 0, 3928148034139, 0, 0, 0, 3995573031265, 0, 3995573031265, 0, 0, 0, 0, 0, 0, 0, 11433740779981, 0, 3928148247572, 0, 11433740779981, 0, 0, 0, 3995573031265, 0, 3995573031265, 0, 0, 0, 0, 0, 8027935145776, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1101732880 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 12) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 12 c : ℚ) *
        (((integerProfile 0 1 2) ⟨12, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨12, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨12, complement (parent_total 0 12) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨12, complement (parent_total 0 12) c⟩ v : ℕ))) /
      (size 0 1 12 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 12 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1101732880 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
