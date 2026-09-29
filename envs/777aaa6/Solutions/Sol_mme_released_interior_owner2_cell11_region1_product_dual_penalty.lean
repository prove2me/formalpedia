-- Prove2me | solution 1 for mme_released_interior_owner2_cell11_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:53.924987+00:00
-- url     : https://prove2.me/submissions/26288b71-01af-4374-b095-0056228cf3ff

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 2 11 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(118532663697 / 200000000000), (592664079941 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(286687949205000000000000000000000000 / 3869671435280435650953358386965696711), (534234218012000000000000000000000000 / 3869671435280435650953358386965696711), (286688618411500000000000000000000000 / 3869671435280435650953358386965696711), (1 / 1), (1 / 1)], ![(1 / 1), (151008260183 / 1000000000000), (3924060781777 / 1000000000000), (392406313769 / 100000000000), (151011614349 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-523128800943 / 1000000000000), (-26156375807 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2602530542739 / 1000000000000), (-495022632167 / 250000000000), (-1301264104237 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-378084148093 / 200000000000), (341781757833 / 250000000000), (341781907927 / 250000000000), (-1890398528907 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-261564400471 / 500000000000), (-523127516139 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301265271369 / 500000000000), (-1980090528667 / 1000000000000), (-2602528208473 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-118151296279 / 62500000000), (1367127031333 / 1000000000000), (1367127631709 / 1000000000000), (-945199264453 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5016057872587 / 1000000000000), (-1758530427173 / 1000000000000), (-11360916979 / 10000000000), (-1136091013473 / 1000000000000), (-439632494521 / 250000000000), (-1254019116289 / 250000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2508028936293 / 500000000000), (-439632606793 / 250000000000), (-1136091697899 / 1000000000000), (-35502844171 / 31250000000), (-1758529978083 / 1000000000000), (-1003215293031 / 200000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 2 11 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
