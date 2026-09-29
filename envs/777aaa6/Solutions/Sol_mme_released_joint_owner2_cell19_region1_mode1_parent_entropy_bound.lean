-- Prove2me | solution 1 for mme_released_joint_owner2_cell19_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:53:11.97235+00:00
-- url     : https://prove2.me/submissions/5e666bc6-14b0-4cd5-bbfe-cce5029868fe

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 318882525000000000000000000000000, 0, 0, 0, 0, 0, 17940665006250000000000000000000000, 0, 17940665006250000000000000000000000, 0, 0, 0, 596372298187616530624382282163558, 0, 19044214472078563497621235435672884, 0, 596372298187616530624382282163558, 0, 0, 0, 0, 0, 0, 0, 17940665006250000000000000000000000, 0, 17940665006250000000000000000000000, 0, 0, 0, 19044214509255415857189235435672884, 0, 777274574670581575167881529128654232, 0, 19044214509255415857189235435672884, 0, 0, 0, 17940663344250000000000000000000000, 0, 17940663344250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 596372298187616530624382282163558, 0, 19044214472078563497621235435672884, 0, 596372298187616530624382282163558, 0, 0, 0, 17940663344250000000000000000000000, 0, 17940663344250000000000000000000000, 0, 0, 0, 0, 0, 318882247000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050687783192, 0, 0, 0, 0, 0, 4020685354686, 0, 4020685354686, 0, 0, 0, 7424645424531, 0, 3960991925790, 0, 7424645424531, 0, 0, 0, 0, 0, 0, 0, 4020685354686, 0, 4020685354686, 0, 0, 0, 3960991923838, 0, 251961613084, 0, 3960991923838, 0, 0, 0, 4020685447325, 0, 4020685447325, 0, 0, 0, 0, 0, 0, 0, 7424645424531, 0, 3960991925790, 0, 7424645424531, 0, 0, 0, 4020685447325, 0, 4020685447325, 0, 0, 0, 0, 0, 8050688654987, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8050687783191, 0, 0, 0, 0, 0, 4020685354685, 0, 4020685354685, 0, 0, 0, 7424645424530, 0, 3960991925789, 0, 7424645424530, 0, 0, 0, 0, 0, 0, 0, 4020685354685, 0, 4020685354685, 0, 0, 0, 3960991923837, 0, 251961613083, 0, 3960991923837, 0, 0, 0, 4020685447324, 0, 4020685447324, 0, 0, 0, 0, 0, 0, 0, 7424645424530, 0, 3960991925789, 0, 7424645424530, 0, 0, 0, 4020685447324, 0, 4020685447324, 0, 0, 0, 0, 0, 8050688654986, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1097495263 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 109) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 109 c : ℚ) *
        (((integerProfile 1 1 1) ⟨109, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨109, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨109, complement (parent_total 1 109) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨109, complement (parent_total 1 109) c⟩ v : ℕ))) /
      (size 1 1 109 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 109 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1097495263 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
