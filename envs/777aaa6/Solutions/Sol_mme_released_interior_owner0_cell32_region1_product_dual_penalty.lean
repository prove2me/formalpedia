-- Prove2me | solution 1 for mme_released_interior_owner0_cell32_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:05.701115+00:00
-- url     : https://prove2.me/submissions/deca1c3d-5344-4416-8435-1866413dd388

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19468947545000000000000000000000000 / 9850419927666871194953874132813987859), (1174710099732500000000000000000000000 / 9850419927666871194953874132813987859), (8282956173270000000000000000000000000 / 9850419927666871194953874132813987859), (1174811746159500000000000000000000000 / 9850419927666871194953874132813987859), (19469034385500000000000000000000000 / 9850419927666871194953874132813987859)], ![(208630369423 / 500000000000), (792799768599 / 1000000000000), (417296632727 / 1000000000000), (1 / 1), (1 / 1)], ![(407554680829 / 1000000000000), (16608237389 / 20000000000), (407589967317 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3113224301399 / 500000000000), (-2126492693003 / 1000000000000), (-17331415609 / 100000000000), (-2126406167801 / 1000000000000), (-3113222071173 / 500000000000)], ![(-437021989787 / 500000000000), (-46436917569 / 200000000000), (-27311186269 / 31250000000), (0 / 1), (0 / 1)], ![(-44879008461 / 50000000000), (-9291673651 / 50000000000), (-448746795989 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6226448602797 / 1000000000000), (-1063246346501 / 500000000000), (-173314156089 / 1000000000000), (-10632030839 / 5000000000), (-1245288828469 / 200000000000)], ![(-874043979573 / 1000000000000), (-58046146961 / 250000000000), (-873957960607 / 1000000000000), (0 / 1), (0 / 1)], ![(-897580169219 / 1000000000000), (-185833473019 / 1000000000000), (-897493591977 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1999475039143 / 250000000000), (-3256170871363 / 1000000000000), (-1593142063993 / 500000000000), (-60776616501 / 31250000000), (-591332216953 / 1000000000000), (-486213071381 / 250000000000), (-1593141809523 / 500000000000), (-130246837053 / 40000000000), (-7998068292109 / 1000000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7997900156571 / 1000000000000), (-1628085435681 / 500000000000), (-637256825597 / 200000000000), (-1944851728031 / 1000000000000), (-73916527119 / 125000000000), (-1944852285523 / 1000000000000), (-637256723809 / 200000000000), (-814042731581 / 250000000000), (-1999517073027 / 250000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 0 32 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
