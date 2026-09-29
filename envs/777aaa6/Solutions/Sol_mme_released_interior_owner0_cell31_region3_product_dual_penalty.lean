-- Prove2me | solution 1 for mme_released_interior_owner0_cell31_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:02.088964+00:00
-- url     : https://prove2.me/submissions/d4081144-43ed-4864-8371-cf13c003afc1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53413629947000000000000000000000000 / 17446210433106814151735360632924068621), (2065784760698000000000000000000000000 / 17446210433106814151735360632924068621), (12765804744331000000000000000000000000 / 17446210433106814151735360632924068621), (2065787240576000000000000000000000000 / 17446210433106814151735360632924068621), (17804542861000000000000000000000000 / 5815403477702271383911786877641356207)], ![(394761909469 / 1000000000000), (15790488657 / 40000000000), (1 / 1), (1 / 1), (1 / 1)], ![(272003002787 / 1000000000000), (36275076697 / 25000000000), (725502162077 / 500000000000), (136001367729 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5788811781039 / 1000000000000), (-1066806137147 / 500000000000), (-312352366167 / 1000000000000), (-2133611073841 / 1000000000000), (-361800737911 / 62500000000)], ![(-929472456653 / 1000000000000), (-929471679081 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301942173089 / 1000000000000), (18612754411 / 50000000000), (372255954017 / 1000000000000), (-650971577953 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2894405890519 / 500000000000), (-2133612274293 / 1000000000000), (-156176183083 / 500000000000), (-26670138423 / 12500000000), (-231552472263 / 40000000000)], ![(-232368114163 / 250000000000), (-23236791977 / 25000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-40685692909 / 31250000000), (372255088221 / 1000000000000), (186127977009 / 500000000000), (-260388631181 / 200000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8020226617151 / 1000000000000), (-4365027886891 / 1000000000000), (-4204418749 / 1562500000), (-869568868799 / 1000000000000), (-869568957027 / 1000000000000), (-2690828442267 / 1000000000000), (-4365024925977 / 1000000000000), (-8020226437681 / 1000000000000)] : List ℚ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-160404532343 / 20000000000), (-436502788689 / 100000000000), (-2690827999359 / 1000000000000), (-434784434399 / 500000000000), (-434784478513 / 500000000000), (-1345414221133 / 500000000000), (-545628115747 / 125000000000), (-100252830471 / 12500000000)] : List ℚ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 31 3 c : ℝ) / 1000000000000) ≤
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
