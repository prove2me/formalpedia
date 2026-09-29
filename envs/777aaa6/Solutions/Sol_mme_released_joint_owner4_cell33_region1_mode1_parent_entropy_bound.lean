-- Prove2me | solution 1 for mme_released_joint_owner4_cell33_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:05:56.848761+00:00
-- url     : https://prove2.me/submissions/8686338e-71fb-4190-921b-d0fd3ff46657

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 326462765000000000000000000000000, 0, 0, 0, 0, 0, 19435083333000000000000000000000000, 0, 19435083333000000000000000000000000, 0, 0, 0, 69461575994649112190162064665652, 0, 20752429441390122040555675870668696, 0, 69461575994649112190162064665652, 0, 0, 0, 0, 0, 0, 0, 19435083333000000000000000000000000, 0, 19435083333000000000000000000000000, 0, 0, 0, 20752429438764206782204675870668696, 0, 760578842784712745905718648258662608, 0, 20752429438764206782204675870668696, 0, 0, 0, 19435083798250000000000000000000000, 0, 19435083798250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 69461575994649112190162064665652, 0, 20752429441390122040555675870668696, 0, 69461575994649112190162064665652, 0, 0, 0, 19435083798250000000000000000000000, 0, 19435083798250000000000000000000000, 0, 0, 0, 0, 0, 326461861000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027194658631, 0, 0, 0, 0, 0, 3940675426908, 0, 3940675426908, 0, 0, 0, 9574736821666, 0, 3875091957647, 0, 9574736821666, 0, 0, 0, 0, 0, 0, 0, 3940675426908, 0, 3940675426908, 0, 0, 0, 3875091957773, 0, 273675500356, 0, 3875091957773, 0, 0, 0, 3940675402969, 0, 3940675402969, 0, 0, 0, 0, 0, 0, 0, 9574736821666, 0, 3875091957647, 0, 9574736821666, 0, 0, 0, 3940675402969, 0, 3940675402969, 0, 0, 0, 0, 0, 8027197427710, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8027194658630, 0, 0, 0, 0, 0, 3940675426907, 0, 3940675426907, 0, 0, 0, 9574736821665, 0, 3875091957646, 0, 9574736821665, 0, 0, 0, 0, 0, 0, 0, 3940675426907, 0, 3940675426907, 0, 0, 0, 3875091957772, 0, 273675500355, 0, 3875091957772, 0, 0, 0, 3940675402968, 0, 3940675402968, 0, 0, 0, 0, 0, 0, 0, 9574736821665, 0, 3875091957646, 0, 9574736821665, 0, 0, 0, 3940675402968, 0, 3940675402968, 0, 0, 0, 0, 0, 8027197427709, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1150422392 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 213) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 213 c : ℚ) *
        (((integerProfile 1 1 1) ⟨213, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨213, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨213, complement (parent_total 1 213) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨213, complement (parent_total 1 213) c⟩ v : ℕ))) /
      (size 1 1 213 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 213 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1150422392 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
