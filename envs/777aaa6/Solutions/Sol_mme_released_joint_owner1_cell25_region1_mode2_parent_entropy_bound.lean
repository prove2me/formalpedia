-- Prove2me | solution 1 for mme_released_joint_owner1_cell25_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:36:40.691282+00:00
-- url     : https://prove2.me/submissions/edd89908-abf7-4034-9cd8-d2581007a01b

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 325012709000000000000000000000000, 0, 0, 0, 0, 0, 18409601949000000000000000000000000, 0, 18409601949000000000000000000000000, 0, 0, 0, 10679076690682228384227973498288, 0, 19704590396341616272859544053003424, 0, 10679076690682228384227973498288, 0, 0, 0, 0, 0, 0, 0, 18409601949000000000000000000000000, 0, 18409601949000000000000000000000000, 0, 0, 0, 19704589360140097761479544053003424, 0, 773212082718273843017784911893993152, 0, 19704589360140097761479544053003424, 0, 0, 0, 18409600852250000000000000000000000, 0, 18409600852250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 10679076690682228384227973498288, 0, 19704590396341616272859544053003424, 0, 10679076690682228384227973498288, 0, 0, 0, 18409600852250000000000000000000000, 0, 18409600852250000000000000000000000, 0, 0, 0, 0, 0, 325017548000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 17, 0, 6, 0, 17, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8031646271784, 0, 0, 0, 0, 0, 3994882905427, 0, 3994882905427, 0, 0, 0, 11447224180353, 0, 3926903655340, 0, 11447224180353, 0, 0, 0, 0, 0, 0, 0, 3994882905427, 0, 3994882905427, 0, 0, 0, 3926903707927, 0, 257201904872, 0, 3926903707927, 0, 0, 0, 3994882965002, 0, 3994882965002, 0, 0, 0, 0, 0, 0, 0, 11447224180353, 0, 3926903655340, 0, 11447224180353, 0, 0, 0, 3994882965002, 0, 3994882965002, 0, 0, 0, 0, 0, 8031631383247, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8031646271783, 0, 0, 0, 0, 0, 3994882905426, 0, 3994882905426, 0, 0, 0, 11447224180352, 0, 3926903655339, 0, 11447224180352, 0, 0, 0, 0, 0, 0, 0, 3994882905426, 0, 3994882905426, 0, 0, 0, 3926903707926, 0, 257201904871, 0, 3926903707926, 0, 0, 0, 3994882965001, 0, 3994882965001, 0, 0, 0, 0, 0, 0, 0, 11447224180352, 0, 3926903655339, 0, 11447224180352, 0, 0, 0, 3994882965001, 0, 3994882965001, 0, 0, 0, 0, 0, 8031631383245, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1102447137 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 70) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 70 c : ℚ) *
        (((integerProfile 1 1 2) ⟨70, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨70, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨70, complement (parent_total 1 70) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨70, complement (parent_total 1 70) c⟩ v : ℕ))) /
      (size 1 1 70 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 70 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1102447137 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
