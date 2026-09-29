-- Prove2me | solution 1 for mme_released_interior_owner1_cell19_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:47.10297+00:00
-- url     : https://prove2.me/submissions/b1209ce7-f066-4700-a73c-b4df870bbf5e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(41032132316700000000000000000000000 / 2025026488018456525416102312528207481), (79737571922800000000000000000000000 / 2025026488018456525416102312528207481), (41027728882600000000000000000000000 / 2025026488018456525416102312528207481), (1 / 1), (1 / 1)], ![(408866817239 / 1000000000000), (160570632917 / 200000000000), (16352917597 / 40000000000), (1 / 1), (1 / 1)], ![(38591619221 / 1000000000000), (225499152871 / 100000000000), (17712464039451 / 1000000000000), (2254747344951 / 1000000000000), (2411952963 / 62500000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3898982585157 / 1000000000000), (-808649292099 / 250000000000), (-1949544953821 / 500000000000), (0 / 1), (0 / 1)], ![(-894365806191 / 1000000000000), (-109791720153 / 500000000000), (-894473126391 / 1000000000000), (0 / 1), (0 / 1)], ![(-406840018089 / 125000000000), (813146216277 / 1000000000000), (2874268574779 / 1000000000000), (813037924527 / 1000000000000), (-203420611207 / 62500000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-974745646289 / 250000000000), (-646919433679 / 200000000000), (-3899089907641 / 1000000000000), (0 / 1), (0 / 1)], ![(-89436580619 / 100000000000), (-43916688061 / 200000000000), (-89447312639 / 100000000000), (0 / 1), (0 / 1)], ![(-3254720144711 / 1000000000000), (406573108139 / 500000000000), (143713428739 / 50000000000), (50814870283 / 62500000000), (-3254729779311 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-76767485469 / 40000000000), (-26444224809 / 8000000000), (-8048078172493 / 1000000000000), (-828981019671 / 250000000000), (-579912033921 / 1000000000000), (-3315925049883 / 1000000000000), (-4024141589351 / 500000000000), (-3305527131491 / 1000000000000), (-239898392387 / 125000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-479796784181 / 250000000000), (-826382025281 / 250000000000), (-2012019543123 / 250000000000), (-3315924078683 / 1000000000000), (-906112553 / 1562500000), (-1657962524941 / 500000000000), (-8048283178701 / 1000000000000), (-330552713149 / 100000000000), (-383837427819 / 200000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 1 19 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
