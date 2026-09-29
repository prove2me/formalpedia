-- Prove2me | solution 1 for mme_released_interior_owner1_cell31_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:39.256541+00:00
-- url     : https://prove2.me/submissions/347a872c-6ae7-4e73-8968-e6ce432cba16

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53413723349000000000000000000000000 / 17446801603957896284021304416056929931), (2065781178385000000000000000000000000 / 17446801603957896284021304416056929931), (12766135732141000000000000000000000000 / 17446801603957896284021304416056929931), (2065778924608000000000000000000000000 / 17446801603957896284021304416056929931), (53413723392000000000000000000000000 / 17446801603957896284021304416056929931)], ![(24672280481 / 62500000000), (78951245583 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(271997491011 / 1000000000000), (1451045284289 / 1000000000000), (1451044278237 / 1000000000000), (271997602827 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1447210979289 / 250000000000), (-2133647893183 / 1000000000000), (-62472064717 / 200000000000), (-533412246047 / 250000000000), (-5788843916351 / 1000000000000)], ![(-929486191033 / 1000000000000), (-929486849113 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301962436953 / 1000000000000), (74456836487 / 200000000000), (186141744553 / 500000000000), (-650981012931 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1157768783431 / 200000000000), (-1066823946591 / 500000000000), (-610078757 / 1953125000), (-2133648984187 / 1000000000000), (-115776878327 / 20000000000)], ![(-116185773879 / 125000000000), (-116185856139 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-162745304619 / 125000000000), (93071045609 / 250000000000), (372283489107 / 1000000000000), (-1301962025861 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8020292792107 / 1000000000000), (-269085125319 / 100000000000), (-1091274027529 / 250000000000), (-54347686891 / 62500000000), (-108695378189 / 125000000000), (-2182549135137 / 500000000000), (-336356374099 / 125000000000), (-8020292545699 / 1000000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4010146396053 / 500000000000), (-2690851253189 / 1000000000000), (-873019222023 / 200000000000), (-173912598051 / 200000000000), (-869563025511 / 1000000000000), (-4365098270273 / 1000000000000), (-2690850992791 / 1000000000000), (-4010146272849 / 500000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 1 31 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
