-- Prove2me | solution 1 for mme_released_interior_owner0_cell27_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:57.307212+00:00
-- url     : https://prove2.me/submissions/adc43c42-26d9-411a-b921-95c1a2033b00

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(28300616708000000000000000000000000 / 2643347741938714381975793014116385169), (406941211137000000000000000000000000 / 2643347741938714381975793014116385169), (1220883058286000000000000000000000000 / 7930043225816143145927379042349155507), (28304546454000000000000000000000000 / 2643347741938714381975793014116385169), (1 / 1)], ![(175661856319 / 1000000000000), (471261313467 / 200000000000), (1178210116779 / 500000000000), (35137706829 / 200000000000), (1 / 1)], ![(444979575161 / 1000000000000), (172935491001 / 200000000000), (6953484111 / 15625000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-907383576131 / 200000000000), (-730911229 / 390625000), (-1871084071373 / 1000000000000), (-2268389516519 / 500000000000), (0 / 1)], ![(-434798600717 / 250000000000), (857095379283 / 1000000000000), (214285904317 / 250000000000), (-869521272029 / 500000000000), (0 / 1)], ![(-3162995689 / 3906250000), (-145398725977 / 1000000000000), (-32385174029 / 40000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2268458940327 / 500000000000), (-1871132746239 / 1000000000000), (-467771017843 / 250000000000), (-4536779033037 / 1000000000000), (0 / 1)], ![(-1739194402867 / 1000000000000), (214273844821 / 250000000000), (857143617269 / 1000000000000), (-1739042544057 / 1000000000000), (0 / 1)], ![(-809726896383 / 1000000000000), (-18174840747 / 125000000000), (-202407337681 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1122864236359 / 250000000000), (-1281459772987 / 200000000000), (-455845360653 / 250000000000), (-231892255059 / 200000000000), (-4421817522801 / 1000000000000), (-4421823148513 / 1000000000000), (-579730419637 / 500000000000), (-45584551881 / 25000000000), (-3203655932461 / 500000000000), (-4491463870743 / 1000000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-898291389087 / 200000000000), (-3203649432467 / 500000000000), (-1823381442611 / 1000000000000), (-579730637647 / 500000000000), (-11054543807 / 2500000000), (-138181973391 / 31250000000), (-1159460839273 / 1000000000000), (-1823382075239 / 1000000000000), (-6407311864921 / 1000000000000), (-2245731935371 / 500000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 27 1 c : ℝ) / 1000000000000) ≤
          (431 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (431 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((431 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
