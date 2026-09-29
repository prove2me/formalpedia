-- Prove2me | solution 1 for mme_released_joint_owner0_cell19_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:18:08.684622+00:00
-- url     : https://prove2.me/submissions/6ca9cc3a-4b77-4227-b349-207698c08602

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 320475753000000000000000000000000, 0, 0, 0, 0, 0, 18244998282000000000000000000000000, 0, 18244998282000000000000000000000000, 0, 0, 0, 805848560563172120326874339809861, 0, 14625584122917371698497251320380278, 0, 805848560563172120326874339809861, 0, 0, 0, 0, 0, 0, 0, 18244998282000000000000000000000000, 0, 18244998282000000000000000000000000, 0, 0, 0, 14625584122921692528613251320380278, 0, 791673332859069183064471497359239444, 0, 14625584122921692528613251320380278, 0, 0, 0, 18245000204750000000000000000000000, 0, 18245000204750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 805848560563172120326874339809861, 0, 14625584122917371698497251320380278, 0, 805848560563172120326874339809861, 0, 0, 0, 18245000204750000000000000000000000, 0, 18245000204750000000000000000000000, 0, 0, 0, 0, 0, 320466707000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 7, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 7, 0, 1, 0, 7, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 7, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8045703938132, 0, 0, 0, 0, 0, 4003864303257, 0, 4003864303257, 0, 0, 0, 7123614723232, 0, 4224982946634, 0, 7123614723232, 0, 0, 0, 0, 0, 0, 0, 4003864303257, 0, 4003864303257, 0, 0, 0, 4224982946633, 0, 233606430764, 0, 4224982946633, 0, 0, 0, 4003864197872, 0, 4003864197872, 0, 0, 0, 0, 0, 0, 0, 7123614723232, 0, 4224982946634, 0, 7123614723232, 0, 0, 0, 4003864197872, 0, 4003864197872, 0, 0, 0, 0, 0, 8045732165315, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8045703938131, 0, 0, 0, 0, 0, 4003864303256, 0, 4003864303256, 0, 0, 0, 7123614723231, 0, 4224982946633, 0, 7123614723231, 0, 0, 0, 0, 0, 0, 0, 4003864303256, 0, 4003864303256, 0, 0, 0, 4224982946632, 0, 233606430763, 0, 4224982946632, 0, 0, 0, 4003864197871, 0, 4003864197871, 0, 0, 0, 0, 0, 0, 0, 7123614723231, 0, 4224982946633, 0, 7123614723231, 0, 0, 0, 4003864197871, 0, 4003864197871, 0, 0, 0, 0, 0, 8045732165314, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1044634418 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 19) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 19 c : ℚ) *
        (((integerProfile 0 1 2) ⟨19, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨19, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨19, complement (parent_total 0 19) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨19, complement (parent_total 0 19) c⟩ v : ℕ))) /
      (size 0 1 19 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 19 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1044634418 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
