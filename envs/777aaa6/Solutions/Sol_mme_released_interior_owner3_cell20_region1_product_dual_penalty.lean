-- Prove2me | solution 1 for mme_released_interior_owner3_cell20_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:20.403126+00:00
-- url     : https://prove2.me/submissions/2018337c-01bb-4188-8e43-fb379506c9c3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(141938859 / 320000000), (849305770771 / 1000000000000), (110874203801 / 250000000000), (1 / 1), (1 / 1)], ![(85131451973 / 500000000000), (600533849479 / 250000000000), (1200983562599 / 500000000000), (170227240279 / 1000000000000), (1 / 1)], ![(82120524423500000000000000000000000 / 8123156872681057069978887722207245927), (1245650080119500000000000000000000000 / 8123156872681057069978887722207245927), (1245562929989500000000000000000000000 / 8123156872681057069978887722207245927), (82103115667000000000000000000000000 / 8123156872681057069978887722207245927), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-406462300669 / 500000000000), (-81668001741 / 500000000000), (-81306465831 / 100000000000), (0 / 1), (0 / 1)], ![(-885205771361 / 500000000000), (876358090893 / 1000000000000), (175257607427 / 200000000000), (-1770621027007 / 1000000000000), (0 / 1)], ![(-143571442401 / 31250000000), (-375012261939 / 200000000000), (-375026255143 / 200000000000), (-1148624542407 / 250000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-812924601337 / 1000000000000), (-163336003481 / 1000000000000), (-813064658309 / 1000000000000), (0 / 1), (0 / 1)], ![(-1770411542721 / 1000000000000), (438179045447 / 500000000000), (54768002321 / 62500000000), (-885310513503 / 500000000000), (0 / 1)], ![(-4594286156831 / 1000000000000), (-937530654847 / 500000000000), (-937565637857 / 500000000000), (-4594498169627 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1299929726429 / 200000000000), (-4535007343851 / 1000000000000), (-2231137649641 / 500000000000), (-581122405829 / 500000000000), (-1811248975553 / 1000000000000), (-1811248938379 / 1000000000000), (-2270009227 / 1953125000), (-557784478919 / 125000000000), (-1133752311057 / 250000000000), (-3249825577737 / 500000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-406228039509 / 62500000000), (-90700146877 / 20000000000), (-4462275299281 / 1000000000000), (-1162244811657 / 1000000000000), (-28300765243 / 15625000000), (-905624469189 / 500000000000), (-1162244724223 / 1000000000000), (-4462275831351 / 1000000000000), (-4535009244227 / 1000000000000), (-6499651155473 / 1000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 20 1 c : ℝ) / 1000000000000) ≤
          (1591 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1591 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1591 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
