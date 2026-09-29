-- Prove2me | solution 1 for mme_released_interior_owner3_cell28_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:14:54.683175+00:00
-- url     : https://prove2.me/submissions/73161717-2658-4c0a-8249-7023870a3fbf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 3 28 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(138093318859 / 500000000000), (1425426809083 / 1000000000000), (1425426333453 / 1000000000000), (55237454457 / 200000000000), (1 / 1)], ![(53305689811 / 1000000000000), (2035487125961 / 1000000000000), (6592375557551 / 500000000000), (203548674213 / 100000000000), (26652848191 / 500000000000)], ![(49211387820250000000000000000000000 / 2192094306290158053345308258906329493), (49211374676875000000000000000000000 / 2192094306290158053345308258906329493), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-643339209093 / 500000000000), (17723564201 / 50000000000), (70894190069 / 200000000000), (-643338060293 / 500000000000), (0 / 1)], ![(-2931712202833 / 1000000000000), (142147032837 / 200000000000), (128953047163 / 50000000000), (5552616997 / 7812500000), (-2931712079563 / 1000000000000)], ![(-3796487613609 / 1000000000000), (-3796487880689 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-257335683637 / 200000000000), (354471284021 / 1000000000000), (177235475173 / 500000000000), (-257335224117 / 200000000000), (0 / 1)], ![(-183232012677 / 62500000000), (355367582093 / 500000000000), (2579060943261 / 1000000000000), (710734975617 / 1000000000000), (-1465856039781 / 500000000000)], ![(-474560951701 / 125000000000), (-237280492543 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4007439055403 / 500000000000), (-109251254159 / 40000000000), (-215738930001 / 250000000000), (-2186214284989 / 500000000000), (-4372431323269 / 1000000000000), (-862955653407 / 1000000000000), (-34141022077 / 12500000000), (-4007438102327 / 500000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-1602975622161 / 200000000000), (-1365640676987 / 500000000000), (-862955720003 / 1000000000000), (-4372428569977 / 1000000000000), (-1093107830817 / 250000000000), (-431477826703 / 500000000000), (-2731281766159 / 1000000000000), (-8014876204653 / 1000000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 3 28 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
