-- Prove2me | solution 1 for mme_released_interior_owner2_cell27_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:31.329241+00:00
-- url     : https://prove2.me/submissions/43789c16-a556-4605-affa-a302586fe6b8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 2 27 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(16560676489 / 100000000000), (2476871465329 / 1000000000000), (123842742459 / 50000000000), (20700388633 / 125000000000), (1 / 1)], ![(170267615747000000000000000000000000 / 16190450551371534656739932073882206727), (2405666871977000000000000000000000000 / 16190450551371534656739932073882206727), (2405650451596000000000000000000000000 / 16190450551371534656739932073882206727), (170264444812000000000000000000000000 / 16190450551371534656739932073882206727), (1 / 1)], ![(110968421277 / 250000000000), (849619330587 / 1000000000000), (88773535463 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1798139187081 / 1000000000000), (226749064473 / 250000000000), (906989549347 / 1000000000000), (-1798161262667 / 1000000000000), (0 / 1)], ![(-113870136643 / 25000000000), (-238324305691 / 125000000000), (-95330063563 / 50000000000), (-910964817827 / 200000000000), (0 / 1)], ![(-406107625013 / 500000000000), (-8148343809 / 50000000000), (-406114392517 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-44953479677 / 25000000000), (906996257893 / 1000000000000), (226747387337 / 250000000000), (-899080631333 / 500000000000), (0 / 1)], ![(-4554805465719 / 1000000000000), (-1906594445527 / 1000000000000), (-1906601271259 / 1000000000000), (-2277412044567 / 500000000000), (0 / 1)], ![(-32488610001 / 40000000000), (-162966876179 / 1000000000000), (-812228785033 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4463805625101 / 1000000000000), (-1621755927969 / 250000000000), (-36225914743 / 20000000000), (-232542117407 / 200000000000), (-4520952627453 / 1000000000000), (-4520950918971 / 1000000000000), (-1162710703777 / 1000000000000), (-56602991763 / 31250000000), (-1621755066063 / 250000000000), (-557975501407 / 125000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-44638056251 / 10000000000), (-10379237939 / 1600000000), (-1811295737149 / 1000000000000), (-581355293517 / 500000000000), (-1130238156863 / 250000000000), (-452095091897 / 100000000000), (-36334709493 / 31250000000), (-362259147283 / 200000000000), (-6487020264251 / 1000000000000), (-892760802251 / 200000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 2 27 2 c : ℝ) / 1000000000000) ≤
          (1649 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1649 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1649 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
