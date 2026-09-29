-- Prove2me | solution 1 for mme_released_interior_owner0_cell14_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:16.084712+00:00
-- url     : https://prove2.me/submissions/19213fb3-7455-45f5-909e-58269951b017

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(59682564854600000000000000000000000 / 763121247751861277291436657075317967), (19894206518600000000000000000000000 / 254373749250620425763812219025105989), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (19359925441 / 125000000000), (963362921099 / 250000000000), (3853455289579 / 1000000000000), (6195172533 / 40000000000)], ![(72652678097 / 125000000000), (1054491139909 / 1000000000000), (36326429923 / 62500000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-159273562259 / 62500000000), (-2548376079609 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-37302170133 / 20000000000), (84310580503 / 62500000000), (67448511181 / 50000000000), (-932554544529 / 500000000000)], ![(-108524696993 / 200000000000), (6632289841 / 125000000000), (-271310491677 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2548376996143 / 1000000000000), (-318547009951 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1865108506649 / 1000000000000), (1348969288049 / 1000000000000), (1348970223621 / 1000000000000), (-1865109089057 / 1000000000000)], ![(-135655871241 / 250000000000), (53058318729 / 1000000000000), (-542620983353 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1742028691449 / 1000000000000), (-1146348453797 / 1000000000000), (-4956109570171 / 1000000000000), (-4956105569619 / 1000000000000), (-1146348472831 / 1000000000000), (-217753667619 / 125000000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-217753586431 / 125000000000), (-286587113449 / 250000000000), (-495610957017 / 100000000000), (-2478052784809 / 500000000000), (-114634847283 / 100000000000), (-1742029340951 / 1000000000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 0 14 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
