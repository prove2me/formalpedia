-- Prove2me | solution 1 for mme_released_joint_owner4_cell27_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:00:58.233205+00:00
-- url     : https://prove2.me/submissions/1876f1f0-5fdb-4e54-93df-fb771d32c8bf

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
  ([0, 0, 0, 0, 0, 6888042099500000000000000000000000, 0, 6888042099500000000000000000000000, 0, 0, 0, 4908210225922678271953500000000000, 0, 233295534924654643456093000000000000, 0, 4908210225922678271953500000000000, 0, 0, 0, 4908210733795923397816500000000000, 0, 4908210733795923397816500000000000, 0, 0, 0, 0, 0, 0, 0, 4908210225922678271953500000000000, 0, 233295534924654643456093000000000000, 0, 4908210225922678271953500000000000, 0, 0, 0, 233295534376408153204367000000000000, 0, 233295534376408153204367000000000000, 0, 0, 0, 0, 0, 6888046680000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4908210733795923397816500000000000, 0, 4908210733795923397816500000000000, 0, 0, 0, 0, 0, 6888046680000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4977968399870, 0, 4977968399870, 0, 0, 0, 5316845919734, 0, 1455449238910, 0, 5316845919734, 0, 0, 0, 5316845816259, 0, 5316845816259, 0, 0, 0, 0, 0, 0, 0, 5316845919734, 0, 1455449238910, 0, 5316845919734, 0, 0, 0, 1455449241260, 0, 1455449241260, 0, 0, 0, 0, 0, 4977967734877, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5316845816259, 0, 5316845816259, 0, 0, 0, 0, 0, 4977967734877, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 4977968399868, 0, 4977968399868, 0, 0, 0, 5316845919733, 0, 1455449238909, 0, 5316845919733, 0, 0, 0, 5316845816258, 0, 5316845816258, 0, 0, 0, 0, 0, 0, 0, 5316845919733, 0, 1455449238909, 0, 5316845919733, 0, 0, 0, 1455449241259, 0, 1455449241259, 0, 0, 0, 0, 0, 4977967734876, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5316845816258, 0, 5316845816258, 0, 0, 0, 0, 0, 4977967734876, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1704122683 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 207) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 207 c : ℚ) *
        (((integerProfile 0 1 2) ⟨207, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨207, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨207, complement (parent_total 0 207) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨207, complement (parent_total 0 207) c⟩ v : ℕ))) /
      (size 0 1 207 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 207 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1704122683 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
