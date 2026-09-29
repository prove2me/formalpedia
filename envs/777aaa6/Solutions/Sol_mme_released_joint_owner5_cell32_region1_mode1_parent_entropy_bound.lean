-- Prove2me | solution 1 for mme_released_joint_owner5_cell32_region1_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:10:58.885554+00:00
-- url     : https://prove2.me/submissions/ebf314fc-52d4-4a28-98fd-c03c967638fa

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 335754372000000000000000000000000, 0, 0, 0, 0, 0, 19796095039000000000000000000000000, 0, 19796095039000000000000000000000000, 0, 0, 0, 689678306574553208340545256807552, 0, 20651269052184431914712909486384896, 0, 689678306574553208340545256807552, 0, 0, 0, 0, 0, 0, 0, 19796095039000000000000000000000000, 0, 19796095039000000000000000000000000, 0, 0, 0, 20651268378986189532662909486384896, 0, 755595975613360544271886181027230208, 0, 20651268378986189532662909486384896, 0, 0, 0, 19796086522000000000000000000000000, 0, 19796086522000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 689678306574553208340545256807552, 0, 20651269052184431914712909486384896, 0, 689678306574553208340545256807552, 0, 0, 0, 19796086522000000000000000000000000, 0, 19796086522000000000000000000000000, 0, 0, 0, 0, 0, 335755682000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999130701053, 0, 0, 0, 0, 0, 3922270580985, 0, 3922270580985, 0, 0, 0, 7279285291445, 0, 3879978506152, 0, 7279285291445, 0, 0, 0, 0, 0, 0, 0, 3922270580985, 0, 3922270580985, 0, 0, 0, 3879978538751, 0, 280248469450, 0, 3879978538751, 0, 0, 0, 3922271011222, 0, 3922271011222, 0, 0, 0, 0, 0, 0, 0, 7279285291445, 0, 3879978506152, 0, 7279285291445, 0, 0, 0, 3922271011222, 0, 3922271011222, 0, 0, 0, 0, 0, 7999126799399, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 7999130701052, 0, 0, 0, 0, 0, 3922270580984, 0, 3922270580984, 0, 0, 0, 7279285291444, 0, 3879978506151, 0, 7279285291444, 0, 0, 0, 0, 0, 0, 0, 3922270580984, 0, 3922270580984, 0, 0, 0, 3879978538750, 0, 280248469449, 0, 3879978538750, 0, 0, 0, 3922271011221, 0, 3922271011221, 0, 0, 0, 0, 0, 0, 0, 7279285291444, 0, 3879978506151, 0, 7279285291444, 0, 0, 0, 3922271011221, 0, 3922271011221, 0, 0, 0, 0, 0, 7999126799398, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1178878517 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 257) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 257 c : ℚ) *
        (((integerProfile 1 1 1) ⟨257, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 1) ⟨257, c⟩ v : ℕ)) *
        (((integerProfile 1 1 1) ⟨257, complement (parent_total 1 257) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 1) ⟨257, complement (parent_total 1 257) c⟩ v : ℕ))) /
      (size 1 1 257 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 1) 257 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1178878517 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
