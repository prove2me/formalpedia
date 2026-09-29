-- Prove2me | solution 1 for mme_released_joint_owner5_cell26_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:09:23.128835+00:00
-- url     : https://prove2.me/submissions/3c8cbf8a-680c-4e30-84e4-c9d5bb1b9ea2

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
  ([0, 0, 0, 0, 0, 6885397103000000000000000000000000, 0, 6885397103000000000000000000000000, 0, 0, 0, 4901073048404061301177500000000000, 0, 233312452636191877397645000000000000, 0, 4901073048404061301177500000000000, 0, 0, 0, 4901073897277871077765000000000000, 0, 4901073897277871077765000000000000, 0, 0, 0, 0, 0, 0, 0, 4901073048404061301177500000000000, 0, 233312452636191877397645000000000000, 0, 4901073048404061301177500000000000, 0, 0, 0, 233312455001444257844470000000000000, 0, 233312455001444257844470000000000000, 0, 0, 0, 0, 0, 6885401368000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4901073897277871077765000000000000, 0, 4901073897277871077765000000000000, 0, 0, 0, 0, 0, 6885401368000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4978352471922, 0, 4978352471922, 0, 0, 0, 5318301108371, 0, 1455376725314, 0, 5318301108371, 0, 0, 0, 5318300935169, 0, 5318300935169, 0, 0, 0, 0, 0, 0, 0, 5318301108371, 0, 1455376725314, 0, 5318301108371, 0, 0, 0, 1455376715176, 0, 1455376715176, 0, 0, 0, 0, 0, 4978351852495, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5318300935169, 0, 5318300935169, 0, 0, 0, 0, 0, 4978351852495, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4978352471921, 0, 4978352471921, 0, 0, 0, 5318301108370, 0, 1455376725313, 0, 5318301108370, 0, 0, 0, 5318300935168, 0, 5318300935168, 0, 0, 0, 0, 0, 0, 0, 5318301108370, 0, 1455376725313, 0, 5318301108370, 0, 0, 0, 1455376715175, 0, 1455376715175, 0, 0, 0, 0, 0, 4978351852494, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5318300935168, 0, 5318300935168, 0, 0, 0, 0, 0, 4978351852494, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1703864896 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 251) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 251 c : ℚ) *
        (((integerProfile 0 1 2) ⟨251, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨251, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨251, complement (parent_total 0 251) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨251, complement (parent_total 0 251) c⟩ v : ℕ))) /
      (size 0 1 251 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 251 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1703864896 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
