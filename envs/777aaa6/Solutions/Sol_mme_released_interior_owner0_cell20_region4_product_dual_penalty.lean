-- Prove2me | solution 1 for mme_released_interior_owner0_cell20_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:28.197363+00:00
-- url     : https://prove2.me/submissions/c1401e1c-3a5d-49fb-9169-3b2ec53e52c2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(444545608857000000000000000000000000 / 15917118195456447650066694089809649003), (863834865453000000000000000000000000 / 15917118195456447650066694089809649003), (444449295550000000000000000000000000 / 15917118195456447650066694089809649003), (1 / 1), (1 / 1)], ![(21951931957 / 125000000000), (588328318999 / 250000000000), (2353057307951 / 1000000000000), (21945048381 / 125000000000), (1 / 1)], ![(3368942537 / 20000000000), (2457322892267 / 1000000000000), (1228528841041 / 500000000000), (16444337 / 97656250), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3578097768347 / 1000000000000), (-2913768802551 / 1000000000000), (-1789157223723 / 500000000000), (0 / 1), (0 / 1)], ![(-1739458585391 / 1000000000000), (213956059963 / 250000000000), (427857732359 / 500000000000), (-1739772209517 / 1000000000000), (0 / 1)], ![(-222641670709 / 125000000000), (224768125547 / 250000000000), (449482284947 / 500000000000), (-1781472496749 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1789048884173 / 500000000000), (-58275376051 / 20000000000), (-715662889489 / 200000000000), (0 / 1), (0 / 1)], ![(-173945858539 / 100000000000), (855824239853 / 1000000000000), (855715464719 / 1000000000000), (-434943052379 / 250000000000), (0 / 1)], ![(-1781133365671 / 1000000000000), (899072502189 / 1000000000000), (179792913979 / 200000000000), (-445368124187 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1126439294101 / 250000000000), (-1823142353553 / 1000000000000), (-1105161184803 / 250000000000), (-6420939857567 / 1000000000000), (-579525428137 / 500000000000), (-1131886423 / 976562500), (-3210457154277 / 500000000000), (-276290980871 / 62500000000), (-911571162617 / 500000000000), (-563217941189 / 125000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4505757176403 / 1000000000000), (-113946397097 / 62500000000), (-4420644739211 / 1000000000000), (-3210469928783 / 500000000000), (-1159050856273 / 1000000000000), (-1159051697151 / 1000000000000), (-6420914308553 / 1000000000000), (-884131138787 / 200000000000), (-1823142325233 / 1000000000000), (-4505743529511 / 1000000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 0 20 4 c : ℝ) / 1000000000000) ≤
          (407 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (407 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((407 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
