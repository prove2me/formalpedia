-- Prove2me | solution 1 for mme_released_joint_owner5_cell13_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:12:58.90638+00:00
-- url     : https://prove2.me/submissions/43fb57e8-e120-4d0e-8103-fed2d71029e5

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 323999607000000000000000000000000, 0, 0, 0, 0, 0, 18716752910500000000000000000000000, 0, 18716752910500000000000000000000000, 0, 0, 0, 48439554133068043470615153016296, 0, 20419699005353710795924769693967408, 0, 48439554133068043470615153016296, 0, 0, 0, 0, 0, 0, 0, 18716752910500000000000000000000000, 0, 18716752910500000000000000000000000, 0, 0, 0, 20419699409506260009574769693967408, 0, 767745422539747786215118460612065184, 0, 20419699409506260009574769693967408, 0, 0, 0, 18716750470750000000000000000000000, 0, 18716750470750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 48439554133068043470615153016296, 0, 20419699005353710795924769693967408, 0, 48439554133068043470615153016296, 0, 0, 0, 18716750470750000000000000000000000, 0, 18716750470750000000000000000000000, 0, 0, 0, 0, 0, 324009282000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8034768255136, 0, 0, 0, 0, 0, 3978336278614, 0, 3978336278614, 0, 0, 0, 9935193843842, 0, 3891255206543, 0, 9935193843842, 0, 0, 0, 0, 0, 0, 0, 3978336278614, 0, 3978336278614, 0, 0, 0, 3891255186751, 0, 264297081855, 0, 3891255186751, 0, 0, 0, 3978336408965, 0, 3978336408965, 0, 0, 0, 0, 0, 0, 0, 9935193843842, 0, 3891255206543, 0, 9935193843842, 0, 0, 0, 3978336408965, 0, 3978336408965, 0, 0, 0, 0, 0, 8034738394435, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8034768255135, 0, 0, 0, 0, 0, 3978336278613, 0, 3978336278613, 0, 0, 0, 9935193843841, 0, 3891255206542, 0, 9935193843841, 0, 0, 0, 0, 0, 0, 0, 3978336278613, 0, 3978336278613, 0, 0, 0, 3891255186750, 0, 264297081854, 0, 3891255186750, 0, 0, 0, 3978336408964, 0, 3978336408964, 0, 0, 0, 0, 0, 0, 0, 9935193843841, 0, 3891255206542, 0, 9935193843841, 0, 0, 0, 3978336408964, 0, 3978336408964, 0, 0, 0, 0, 0, 8034738394434, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1123569802 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 238) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 238 c : ℚ) *
        (((integerProfile 0 1 1) ⟨238, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨238, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨238, complement (parent_total 0 238) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨238, complement (parent_total 0 238) c⟩ v : ℕ))) /
      (size 0 1 238 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 238 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1123569802 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
