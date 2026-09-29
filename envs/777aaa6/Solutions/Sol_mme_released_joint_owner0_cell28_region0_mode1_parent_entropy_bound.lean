-- Prove2me | solution 1 for mme_released_joint_owner0_cell28_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:41:11.215465+00:00
-- url     : https://prove2.me/submissions/f242d821-c5a6-42da-88b4-291a6767c0bb

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 328217830000000000000000000000000, 0, 0, 0, 0, 0, 18720503460750000000000000000000000, 0, 18720503460750000000000000000000000, 0, 0, 0, 47489970849623410563869024391296, 0, 20465142063593789983692261951217408, 0, 47489970849623410563869024391296, 0, 0, 0, 0, 0, 0, 0, 18720503460750000000000000000000000, 0, 18720503460750000000000000000000000, 0, 0, 0, 20465142792756146915052261951217408, 0, 767529009979901632560255476097565184, 0, 20465142792756146915052261951217408, 0, 0, 0, 18720500109750000000000000000000000, 0, 18720500109750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 47489970849623410563869024391296, 0, 20465142063593789983692261951217408, 0, 47489970849623410563869024391296, 0, 0, 0, 18720500109750000000000000000000000, 0, 18720500109750000000000000000000000, 0, 0, 0, 0, 0, 328228312000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021833054154, 0, 0, 0, 0, 0, 3978135914024, 0, 3978135914024, 0, 0, 0, 9954992009225, 0, 3889032227279, 0, 9954992009225, 0, 0, 0, 0, 0, 0, 0, 3978135914024, 0, 3978135914024, 0, 0, 0, 3889032191650, 0, 264579002216, 0, 3889032191650, 0, 0, 0, 3978136093026, 0, 3978136093026, 0, 0, 0, 0, 0, 0, 0, 9954992009225, 0, 3889032227279, 0, 9954992009225, 0, 0, 0, 3978136093026, 0, 3978136093026, 0, 0, 0, 0, 0, 8021801118556, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8021833054153, 0, 0, 0, 0, 0, 3978135914023, 0, 3978135914023, 0, 0, 0, 9954992009224, 0, 3889032227278, 0, 9954992009224, 0, 0, 0, 0, 0, 0, 0, 3978135914023, 0, 3978135914023, 0, 0, 0, 3889032191649, 0, 264579002215, 0, 3889032191649, 0, 0, 0, 3978136093025, 0, 3978136093025, 0, 0, 0, 0, 0, 0, 0, 9954992009224, 0, 3889032227278, 0, 9954992009224, 0, 0, 0, 3978136093025, 0, 3978136093025, 0, 0, 0, 0, 0, 8021801118555, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1124369009 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 28) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 28 c : ℚ) *
        (((integerProfile 0 1 1) ⟨28, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨28, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨28, complement (parent_total 0 28) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨28, complement (parent_total 0 28) c⟩ v : ℕ))) /
      (size 0 1 28 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 28 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1124369009 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
