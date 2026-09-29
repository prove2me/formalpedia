-- Prove2me | solution 1 for mme_released_joint_owner5_cell31_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:10:58.341102+00:00
-- url     : https://prove2.me/submissions/0ff87bf3-26ef-4e84-bbdc-b9a4af77d3d0

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 324737443000000000000000000000000, 0, 0, 0, 0, 0, 19434159719250000000000000000000000, 0, 19434159719250000000000000000000000, 0, 0, 0, 69969666355157469044662168954560, 0, 20729042369354995758450675662090880, 0, 69969666355157469044662168954560, 0, 0, 0, 0, 0, 0, 0, 19434159719250000000000000000000000, 0, 19434159719250000000000000000000000, 0, 0, 0, 20729041889088875972746675662090880, 0, 760681195433691626661426648675818240, 0, 20729041889088875972746675662090880, 0, 0, 0, 19434161085750000000000000000000000, 0, 19434161085750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 69969666355157469044662168954560, 0, 20729042369354995758450675662090880, 0, 69969666355157469044662168954560, 0, 0, 0, 19434161085750000000000000000000000, 0, 19434161085750000000000000000000000, 0, 0, 0, 0, 0, 324736721000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8032493569828, 0, 0, 0, 0, 0, 3940722951052, 0, 3940722951052, 0, 0, 0, 9567448747617, 0, 3876219549002, 0, 9567448747617, 0, 0, 0, 0, 0, 0, 0, 3940722951052, 0, 3940722951052, 0, 0, 0, 3876219572171, 0, 273540937367, 0, 3876219572171, 0, 0, 0, 3940722880737, 0, 3940722880737, 0, 0, 0, 0, 0, 0, 0, 9567448747617, 0, 3876219549002, 0, 9567448747617, 0, 0, 0, 3940722880737, 0, 3940722880737, 0, 0, 0, 0, 0, 8032495793165, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8032493569827, 0, 0, 0, 0, 0, 3940722951051, 0, 3940722951051, 0, 0, 0, 9567448747616, 0, 3876219549001, 0, 9567448747616, 0, 0, 0, 0, 0, 0, 0, 3940722951051, 0, 3940722951051, 0, 0, 0, 3876219572170, 0, 273540937366, 0, 3876219572170, 0, 0, 0, 3940722880736, 0, 3940722880736, 0, 0, 0, 0, 0, 0, 0, 9567448747616, 0, 3876219549001, 0, 9567448747616, 0, 0, 0, 3940722880736, 0, 3940722880736, 0, 0, 0, 0, 0, 8032495793164, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1150050474 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 256) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 256 c : ℚ) *
        (((integerProfile 1 1 1) ⟨256, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨256, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨256, complement (parent_total 1 256) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨256, complement (parent_total 1 256) c⟩ v : ℕ))) /
      (size 1 1 256 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 256 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1150050474 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
