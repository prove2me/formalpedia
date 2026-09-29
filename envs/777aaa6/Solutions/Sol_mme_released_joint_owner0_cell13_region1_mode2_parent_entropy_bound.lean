-- Prove2me | solution 1 for mme_released_joint_owner0_cell13_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:25:56.842423+00:00
-- url     : https://prove2.me/submissions/df9654ef-27f0-4f3e-9c3c-840f38755b08

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 327360604000000000000000000000000, 0, 0, 0, 0, 0, 19428142026500000000000000000000000, 0, 19428142026500000000000000000000000, 0, 0, 0, 25344625868014136390864853129200, 0, 20249693708552961144889270293741600, 0, 25344625868014136390864853129200, 0, 0, 0, 0, 0, 0, 0, 19428142026500000000000000000000000, 0, 19428142026500000000000000000000000, 0, 0, 0, 20249681457565266912317270293741600, 0, 762819905654291487340023459412516800, 0, 20249681457565266912317270293741600, 0, 0, 0, 19428157383250000000000000000000000, 0, 19428157383250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 25344625868014136390864853129200, 0, 20249693708552961144889270293741600, 0, 25344625868014136390864853129200, 0, 0, 0, 19428157383250000000000000000000000, 0, 19428157383250000000000000000000000, 0, 0, 0, 0, 0, 327407267000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024448230140, 0, 0, 0, 0, 0, 3941032644123, 0, 3941032644123, 0, 0, 0, 10582943847719, 0, 3899615611048, 0, 10582943847719, 0, 0, 0, 0, 0, 0, 0, 3941032644123, 0, 3941032644123, 0, 0, 0, 3899616216044, 0, 270733310088, 0, 3899616216044, 0, 0, 0, 3941031853685, 0, 3941031853685, 0, 0, 0, 0, 0, 0, 0, 10582943847719, 0, 3899615611048, 0, 10582943847719, 0, 0, 0, 3941031853685, 0, 3941031853685, 0, 0, 0, 0, 0, 8024305697184, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024448230139, 0, 0, 0, 0, 0, 3941032644122, 0, 3941032644122, 0, 0, 0, 10582943847718, 0, 3899615611047, 0, 10582943847718, 0, 0, 0, 0, 0, 0, 0, 3941032644122, 0, 3941032644122, 0, 0, 0, 3899616216043, 0, 270733310087, 0, 3899616216043, 0, 0, 0, 3941031853684, 0, 3941031853684, 0, 0, 0, 0, 0, 0, 0, 10582943847718, 0, 3899615611047, 0, 10582943847718, 0, 0, 0, 3941031853684, 0, 3941031853684, 0, 0, 0, 0, 0, 8024305697183, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1141247477 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 13) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 13 c : ℚ) *
        (((integerProfile 1 1 2) ⟨13, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨13, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨13, complement (parent_total 1 13) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨13, complement (parent_total 1 13) c⟩ v : ℕ))) /
      (size 1 1 13 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 13 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1141247477 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
