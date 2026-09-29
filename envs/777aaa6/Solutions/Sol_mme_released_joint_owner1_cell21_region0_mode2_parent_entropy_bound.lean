-- Prove2me | solution 1 for mme_released_joint_owner1_cell21_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:27:27.474676+00:00
-- url     : https://prove2.me/submissions/25aba819-b907-430b-9f5a-ce2b28ca4cb6

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 333448562000000000000000000000000, 0, 0, 0, 0, 0, 19386007335000000000000000000000000, 0, 19386007335000000000000000000000000, 0, 0, 0, 812949509151111221702462384621888, 0, 15894171197691034277663075230756224, 0, 812949509151111221702462384621888, 0, 0, 0, 0, 0, 0, 0, 19386007335000000000000000000000000, 0, 19386007335000000000000000000000000, 0, 0, 0, 15894171197641005724487075230756224, 0, 777416560980731475108889849538487552, 0, 15894171197641005724487075230756224, 0, 0, 0, 19386008209250000000000000000000000, 0, 19386008209250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 812949509151111221702462384621888, 0, 15894171197691034277663075230756224, 0, 812949509151111221702462384621888, 0, 0, 0, 19386008209250000000000000000000000, 0, 19386008209250000000000000000000000, 0, 0, 0, 0, 0, 333445453000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8006021941386, 0, 0, 0, 0, 0, 3943203744546, 0, 3943203744546, 0, 0, 0, 7114841554711, 0, 4141802828308, 0, 7114841554711, 0, 0, 0, 0, 0, 0, 0, 3943203744546, 0, 3943203744546, 0, 0, 0, 4141802828311, 0, 251778957755, 0, 4141802828311, 0, 0, 0, 3943203699450, 0, 3943203699450, 0, 0, 0, 0, 0, 0, 0, 7114841554711, 0, 4141802828308, 0, 7114841554711, 0, 0, 0, 3943203699450, 0, 3943203699450, 0, 0, 0, 0, 0, 8006031265207, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8006021941385, 0, 0, 0, 0, 0, 3943203744545, 0, 3943203744545, 0, 0, 0, 7114841554710, 0, 4141802828307, 0, 7114841554710, 0, 0, 0, 0, 0, 0, 0, 3943203744545, 0, 3943203744545, 0, 0, 0, 4141802828310, 0, 251778957754, 0, 4141802828310, 0, 0, 0, 3943203699448, 0, 3943203699448, 0, 0, 0, 0, 0, 0, 0, 7114841554710, 0, 4141802828307, 0, 7114841554710, 0, 0, 0, 3943203699448, 0, 3943203699448, 0, 0, 0, 0, 0, 8006031265206, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1099078247 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 66) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 66 c : ℚ) *
        (((integerProfile 0 1 2) ⟨66, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨66, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨66, complement (parent_total 0 66) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨66, complement (parent_total 0 66) c⟩ v : ℕ))) /
      (size 0 1 66 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 66 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1099078247 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
