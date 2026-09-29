-- Prove2me | solution 1 for mme_released_interior_owner0_cell33_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:08.416731+00:00
-- url     : https://prove2.me/submissions/3640af56-a743-434b-b2ae-e66835584d79

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53324723733000000000000000000000 / 17588314491488243780210531057698309), (2034436647643000000000000000000000 / 17588314491488243780210531057698309), (13146775703026000000000000000000000 / 17588314491488243780210531057698309), (2034430615603000000000000000000000 / 17588314491488243780210531057698309), (53324721754000000000000000000000 / 17588314491488243780210531057698309)], ![(136932368063 / 500000000000), (1435852525987 / 1000000000000), (143585021077 / 100000000000), (273863937923 / 1000000000000), (1 / 1)], ![(393127991621 / 1000000000000), (196563685847 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5798589927639 / 1000000000000), (-2157015783241 / 1000000000000), (-291058197313 / 1000000000000), (-2157018748213 / 1000000000000), (-362411872797 / 62500000000)], ![(-64756047913 / 50000000000), (361758767571 / 1000000000000), (5652455549 / 15625000000), (-1295123872853 / 1000000000000), (0 / 1)], ![(-93362004171 / 100000000000), (-46681080931 / 50000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2899294963819 / 500000000000), (-53925394581 / 25000000000), (-4547784333 / 15625000000), (-539254687053 / 250000000000), (-5798589964751 / 1000000000000)], ![(-1295120958259 / 1000000000000), (90439691893 / 250000000000), (361757155137 / 1000000000000), (-323780968213 / 250000000000), (0 / 1)], ![(-933620041709 / 1000000000000), (-933621618619 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4013667709829 / 500000000000), (-2728880246727 / 1000000000000), (-1096439924453 / 250000000000), (-21573026209 / 25000000000), (-172584216777 / 200000000000), (-4385761325077 / 1000000000000), (-170555001397 / 62500000000), (-200683274131 / 25000000000)] : List ℚ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8027335419657 / 1000000000000), (-1364440123363 / 500000000000), (-4385759697811 / 1000000000000), (-862921048359 / 1000000000000), (-215730270971 / 250000000000), (-1096440331269 / 250000000000), (-2728880022351 / 1000000000000), (-8027330965239 / 1000000000000)] : List ℚ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 0 33 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
