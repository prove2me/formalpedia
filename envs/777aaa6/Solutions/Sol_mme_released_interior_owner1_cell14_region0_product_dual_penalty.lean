-- Prove2me | solution 1 for mme_released_interior_owner1_cell14_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:34.570696+00:00
-- url     : https://prove2.me/submissions/9b1bd36d-219a-4fbe-a0aa-897f34033f08

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(59715648211000000000000000000000000 / 762284866859632829082925958620679413), (8530802489700000000000000000000000 / 108897838122804689868989422660097059), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (19379323667 / 125000000000), (962892702991 / 250000000000), (770313715559 / 200000000000), (30280219 / 195312500)], ![(72800805263 / 125000000000), (1051299428307 / 1000000000000), (145601465063 / 250000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2546726226709 / 1000000000000), (-636681685551 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1864107029953 / 1000000000000), (337120267049 / 250000000000), (1348480488129 / 1000000000000), (-1864106178891 / 1000000000000)], ![(-67573340107 / 125000000000), (50026949803 / 1000000000000), (-108117543981 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-636681556677 / 250000000000), (-2546726742203 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-29126672343 / 15625000000), (1348481068197 / 1000000000000), (134848048813 / 100000000000), (-186410617889 / 100000000000)], ![(-108117344171 / 200000000000), (12506737451 / 250000000000), (-16893366247 / 31250000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-495141912651 / 100000000000), (-143527348597 / 125000000000), (-1738832878417 / 1000000000000), (-1738832974931 / 1000000000000), (-229643744841 / 200000000000), (-4951421492007 / 1000000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4951419126509 / 1000000000000), (-45928751551 / 40000000000), (-108677054901 / 62500000000), (-173883297493 / 100000000000), (-287054681051 / 250000000000), (-2475710746003 / 500000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 14 0 c : ℝ) / 1000000000000) ≤
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
