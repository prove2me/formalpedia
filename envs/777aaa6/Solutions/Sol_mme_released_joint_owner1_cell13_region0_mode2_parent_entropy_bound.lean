-- Prove2me | solution 1 for mme_released_joint_owner1_cell13_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:23:54.659945+00:00
-- url     : https://prove2.me/submissions/cf5a6b33-57a0-431d-9bd7-63841d8eaa23

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 327283836000000000000000000000000, 0, 0, 0, 0, 0, 19427062971250000000000000000000000, 0, 19427062971250000000000000000000000, 0, 0, 0, 25446140219306955633336282453750, 0, 20256974584506551060013327435092500, 0, 25446140219306955633336282453750, 0, 0, 0, 0, 0, 0, 0, 19427062971250000000000000000000000, 0, 19427062971250000000000000000000000, 0, 0, 0, 20256977390690105680973327435092500, 0, 762799260682729458695493345129815000, 0, 20256977390690105680973327435092500, 0, 0, 0, 19427057974250000000000000000000000, 0, 19427057974250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 25446140219306955633336282453750, 0, 20256974584506551060013327435092500, 0, 25446140219306955633336282453750, 0, 0, 0, 19427057974250000000000000000000000, 0, 19427057974250000000000000000000000, 0, 0, 0, 0, 0, 327283188000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024682763562, 0, 0, 0, 0, 0, 3941088186502, 0, 3941088186502, 0, 0, 0, 10578946487794, 0, 3899256120804, 0, 10578946487794, 0, 0, 0, 0, 0, 0, 0, 3941088186502, 0, 3941088186502, 0, 0, 0, 3899255982275, 0, 270760374472, 0, 3899255982275, 0, 0, 0, 3941088443720, 0, 3941088443720, 0, 0, 0, 0, 0, 0, 0, 10578946487794, 0, 3899256120804, 0, 10578946487794, 0, 0, 0, 3941088443720, 0, 3941088443720, 0, 0, 0, 0, 0, 8024684743496, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024682763561, 0, 0, 0, 0, 0, 3941088186501, 0, 3941088186501, 0, 0, 0, 10578946487793, 0, 3899256120803, 0, 10578946487793, 0, 0, 0, 0, 0, 0, 0, 3941088186501, 0, 3941088186501, 0, 0, 0, 3899255982274, 0, 270760374471, 0, 3899255982274, 0, 0, 0, 3941088443719, 0, 3941088443719, 0, 0, 0, 0, 0, 0, 0, 10578946487793, 0, 3899256120803, 0, 10578946487793, 0, 0, 0, 3941088443719, 0, 3941088443719, 0, 0, 0, 0, 0, 8024684743495, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1141323913 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 58) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 58 c : ℚ) *
        (((integerProfile 0 1 2) ⟨58, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨58, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨58, complement (parent_total 0 58) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨58, complement (parent_total 0 58) c⟩ v : ℕ))) /
      (size 0 1 58 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 58 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1141323913 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
