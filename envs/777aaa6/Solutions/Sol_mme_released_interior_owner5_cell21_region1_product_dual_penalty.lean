-- Prove2me | solution 1 for mme_released_interior_owner5_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:21:21.881147+00:00
-- url     : https://prove2.me/submissions/85f2404d-a748-4828-a9be-d74bd236e687

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(25783792409 / 62500000000), (402655716979 / 500000000000), (82500443917 / 200000000000), (1 / 1), (1 / 1)], ![(3899113067 / 100000000000), (462261004117 / 200000000000), (16884040572059 / 1000000000000), (577771821159 / 250000000000), (38991040557 / 1000000000000)], ![(205714299167500000000000000000000000 / 9915511044115203829672833244806562041), (404914084853500000000000000000000000 / 9915511044115203829672833244806562041), (68565079242500000000000000000000000 / 3305170348038401276557611081602187347), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-442710231709 / 500000000000), (-216526201899 / 1000000000000), (-88551369241 / 100000000000), (0 / 1), (0 / 1)], ![(-1622210538717 / 500000000000), (837812308989 / 1000000000000), (565273766181 / 200000000000), (167543619957 / 200000000000), (-3244423388553 / 1000000000000)], ![(-3875367273237 / 1000000000000), (-3198180673711 / 1000000000000), (-1937729968651 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-885420463417 / 1000000000000), (-108263100949 / 500000000000), (-885513692409 / 1000000000000), (0 / 1), (0 / 1)], ![(-3244421077433 / 1000000000000), (83781230899 / 100000000000), (1413184415453 / 500000000000), (418859049893 / 500000000000), (-405552923569 / 125000000000)], ![(-968841818309 / 250000000000), (-319818067371 / 100000000000), (-3875459937301 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-241814016623 / 125000000000), (-3254175381937 / 1000000000000), (-2001302781397 / 250000000000), (-405735257957 / 125000000000), (-588338044701 / 1000000000000), (-1622941515413 / 500000000000), (-8005394707033 / 1000000000000), (-81354345591 / 25000000000), (-1934511571573 / 1000000000000)] : List ℚ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1934512132983 / 1000000000000), (-203385961371 / 62500000000), (-8005211125587 / 1000000000000), (-649176412731 / 200000000000), (-5883380447 / 10000000000), (-129835321233 / 40000000000), (-1000674338379 / 125000000000), (-3254173823639 / 1000000000000), (-483627892893 / 250000000000)] : List ℚ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 5 21 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
