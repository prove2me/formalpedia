-- Prove2me | solution 1 for mme_released_joint_owner3_cell31_region1_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:49:05.535263+00:00
-- url     : https://prove2.me/submissions/069386e4-782e-40b8-9bf2-ba0b245dd28b

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 327499294000000000000000000000000, 0, 0, 0, 0, 0, 20115563487750000000000000000000000, 0, 20115563487750000000000000000000000, 0, 0, 0, 40598536623121297773109792908864, 0, 20537179897939713589748780414182272, 0, 40598536623121297773109792908864, 0, 0, 0, 0, 0, 0, 0, 20115563487750000000000000000000000, 0, 20115563487750000000000000000000000, 0, 0, 0, 20537178609625038677878780414182272, 0, 756109367974378010273652439171635456, 0, 20537178609625038677878780414182272, 0, 0, 0, 20115565947750000000000000000000000, 0, 20115565947750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40598536623121297773109792908864, 0, 20537179897939713589748780414182272, 0, 40598536623121297773109792908864, 0, 0, 0, 20115565947750000000000000000000000, 0, 20115565947750000000000000000000000, 0, 0, 0, 0, 0, 327503828000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024024658617, 0, 0, 0, 0, 0, 3906261460662, 0, 3906261460662, 0, 0, 0, 10111778535772, 0, 3885518381964, 0, 10111778535772, 0, 0, 0, 0, 0, 0, 0, 3906261460662, 0, 3906261460662, 0, 0, 0, 3885518444695, 0, 279569246634, 0, 3885518444695, 0, 0, 0, 3906261338369, 0, 3906261338369, 0, 0, 0, 0, 0, 0, 0, 10111778535772, 0, 3885518381964, 0, 10111778535772, 0, 0, 0, 3906261338369, 0, 3906261338369, 0, 0, 0, 0, 0, 8024010814408, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024024658616, 0, 0, 0, 0, 0, 3906261460661, 0, 3906261460661, 0, 0, 0, 10111778535771, 0, 3885518381963, 0, 10111778535771, 0, 0, 0, 0, 0, 0, 0, 3906261460661, 0, 3906261460661, 0, 0, 0, 3885518444694, 0, 279569246633, 0, 3885518444694, 0, 0, 0, 3906261338368, 0, 3906261338368, 0, 0, 0, 0, 0, 0, 0, 10111778535771, 0, 3885518381963, 0, 10111778535771, 0, 0, 0, 3906261338368, 0, 3906261338368, 0, 0, 0, 0, 0, 8024010814407, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1166086361 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 166) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 1 1 166 c : ℚ) *
        (((integerProfile 1 1 2) ⟨166, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 1 1 2) ⟨166, c⟩ v : ℕ)) *
        (((integerProfile 1 1 2) ⟨166, complement (parent_total 1 166) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 1 1 2) ⟨166, complement (parent_total 1 166) c⟩ v : ℕ))) /
      (size 1 1 166 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 1) (size 1 1)
        (splitCount 1 1) (integerProfile 1 1 2) 166 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1166086361 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
