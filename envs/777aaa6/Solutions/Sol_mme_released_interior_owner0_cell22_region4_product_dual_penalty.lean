-- Prove2me | solution 1 for mme_released_interior_owner0_cell22_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:22.163193+00:00
-- url     : https://prove2.me/submissions/e4c23150-2fd6-4ee3-858b-d2f49499ac39

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11644488328580000000000000000000000 / 152510540737902242641780315674427449), (7010607244740000000000000000000000 / 50836846912634080880593438558142483), (11644479612280000000000000000000000 / 152510540737902242641780315674427449), (1 / 1), (1 / 1)], ![(1 / 1), (38777149211 / 250000000000), (1924527348387 / 500000000000), (1924526523091 / 500000000000), (155108436653 / 1000000000000)], ![(59771022027 / 100000000000), (5977100079 / 10000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2572400750033 / 1000000000000), (-1981197101791 / 1000000000000), (-2572401498567 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-931814891293 / 500000000000), (673913792423 / 500000000000), (269565431203 / 200000000000), (-931815407677 / 500000000000)], ![(-16082788249 / 31250000000), (-257324789637 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-160775046877 / 62500000000), (-198119710179 / 100000000000), (-1286200749283 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-372725956517 / 200000000000), (1347827584847 / 1000000000000), (84239197251 / 62500000000), (-1863630815353 / 1000000000000)], ![(-514649223967 / 1000000000000), (-514649579273 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1739223173289 / 1000000000000), (-4950680789323 / 1000000000000), (-57400954811 / 50000000000), (-574009584873 / 500000000000), (-4950680860383 / 1000000000000), (-869611568843 / 500000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-217402896661 / 125000000000), (-2475340394661 / 500000000000), (-1148019096219 / 1000000000000), (-229603833949 / 200000000000), (-2475340430191 / 500000000000), (-347844627537 / 200000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 0 22 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
