-- Prove2me | solution 1 for mme_released_joint_owner1_cell26_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:48:53.658992+00:00
-- url     : https://prove2.me/submissions/23b2c8fb-0b3b-44a5-8260-054771e2170a

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
  ([0, 0, 0, 0, 0, 6478129056000000000000000000000000, 0, 6478129056000000000000000000000000, 0, 0, 0, 5559475998783287553174000000000000, 0, 232402915795933424893652000000000000, 0, 5559475998783287553174000000000000, 0, 0, 0, 5559475972441304914318000000000000, 0, 5559475972441304914318000000000000, 0, 0, 0, 0, 0, 0, 0, 5559475998783287553174000000000000, 0, 232402915795933424893652000000000000, 0, 5559475998783287553174000000000000, 0, 0, 0, 232402883534617390171364000000000000, 0, 232402883534617390171364000000000000, 0, 0, 0, 0, 0, 6478167671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5559475972441304914318000000000000, 0, 5559475972441304914318000000000000, 0, 0, 0, 0, 0, 6478167671000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5039323536234, 0, 5039323536234, 0, 0, 0, 5192251419985, 0, 1459282707629, 0, 5192251419985, 0, 0, 0, 5192251424723, 0, 5192251424723, 0, 0, 0, 0, 0, 0, 0, 5192251419985, 0, 1459282707629, 0, 5192251419985, 0, 0, 0, 1459282846446, 0, 1459282846446, 0, 0, 0, 0, 0, 5039317575426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5192251424723, 0, 5192251424723, 0, 0, 0, 0, 0, 5039317575426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 5039323536233, 0, 5039323536233, 0, 0, 0, 5192251419984, 0, 1459282707628, 0, 5192251419984, 0, 0, 0, 5192251424722, 0, 5192251424722, 0, 0, 0, 0, 0, 0, 0, 5192251419984, 0, 1459282707628, 0, 5192251419984, 0, 0, 0, 1459282846445, 0, 1459282846445, 0, 0, 0, 0, 0, 5039317575425, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5192251424722, 0, 5192251424722, 0, 0, 0, 0, 0, 5039317575425, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1718077636 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 71) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 71 c : ℚ) *
        (((integerProfile 0 1 1) ⟨71, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨71, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨71, complement (parent_total 0 71) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨71, complement (parent_total 0 71) c⟩ v : ℕ))) /
      (size 0 1 71 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 71 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1718077636 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
