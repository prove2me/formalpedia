-- Prove2me | solution 1 for mme_released_joint_owner3_cell33_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:49:50.517324+00:00
-- url     : https://prove2.me/submissions/aa1ce97d-f35f-414b-8cd9-69f66bb6eea7

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 330159803000000000000000000000000, 0, 0, 0, 0, 0, 20138398217000000000000000000000000, 0, 20138398217000000000000000000000000, 0, 0, 0, 40227087031747755659406377905216, 0, 20557033561037387594817187244189568, 0, 40227087031747755659406377905216, 0, 0, 0, 0, 0, 0, 0, 20138398217000000000000000000000000, 0, 20138398217000000000000000000000000, 0, 0, 0, 20557023360099110659617187244189568, 0, 755843381065600012468493625511620864, 0, 20557023360099110659617187244189568, 0, 0, 0, 20138411638500000000000000000000000, 0, 20138411638500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40227087031747755659406377905216, 0, 20557033561037387594817187244189568, 0, 40227087031747755659406377905216, 0, 0, 0, 20138411638500000000000000000000000, 0, 20138411638500000000000000000000000, 0, 0, 0, 0, 0, 330197519000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8015933769201, 0, 0, 0, 0, 0, 3905126927278, 0, 3905126927278, 0, 0, 0, 10120969982486, 0, 3884552130856, 0, 10120969982486, 0, 0, 0, 0, 0, 0, 0, 3905126927278, 0, 3905126927278, 0, 0, 0, 3884552627082, 0, 279921092168, 0, 3884552627082, 0, 0, 0, 3905126260815, 0, 3905126260815, 0, 0, 0, 0, 0, 0, 0, 10120969982486, 0, 3884552130856, 0, 10120969982486, 0, 0, 0, 3905126260815, 0, 3905126260815, 0, 0, 0, 0, 0, 8015819540135, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8015933769200, 0, 0, 0, 0, 0, 3905126927277, 0, 3905126927277, 0, 0, 0, 10120969982485, 0, 3884552130855, 0, 10120969982485, 0, 0, 0, 0, 0, 0, 0, 3905126927277, 0, 3905126927277, 0, 0, 0, 3884552627081, 0, 279921092167, 0, 3884552627081, 0, 0, 0, 3905126260814, 0, 3905126260814, 0, 0, 0, 0, 0, 0, 0, 10120969982485, 0, 3884552130855, 0, 10120969982485, 0, 0, 0, 3905126260814, 0, 3905126260814, 0, 0, 0, 0, 0, 8015819540134, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1167061976 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 168) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 168 c : ℚ) *
        (((integerProfile 1 1 2) ⟨168, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨168, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨168, complement (parent_total 1 168) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨168, complement (parent_total 1 168) c⟩ v : ℕ))) /
      (size 1 1 168 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 168 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1167061976 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
