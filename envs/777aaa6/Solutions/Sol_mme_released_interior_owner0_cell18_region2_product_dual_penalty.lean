-- Prove2me | solution 1 for mme_released_interior_owner0_cell18_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:22.815968+00:00
-- url     : https://prove2.me/submissions/59dfe7c0-76ab-4c9e-8e31-658feea3b62b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(573988690753000000000000000000000000 / 7752400533437519876806852078142030367), (1064294715482000000000000000000000000 / 7752400533437519876806852078142030367), (573990097541000000000000000000000000 / 7752400533437519876806852078142030367), (1 / 1), (1 / 1)], ![(148039055593 / 250000000000), (118431396379 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (150135135317 / 1000000000000), (1971490879927 / 500000000000), (985746236957 / 250000000000), (75069388381 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-325393515879 / 125000000000), (-992845100427 / 500000000000), (-325393209517 / 125000000000), (0 / 1), (0 / 1)], ![(-523984789769 / 1000000000000), (-523983507131 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-948109744171 / 500000000000), (10718259601 / 7812500000), (685969018723 / 500000000000), (-1896195234187 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2603148127031 / 1000000000000), (-1985690200853 / 1000000000000), (-520629135227 / 200000000000), (0 / 1), (0 / 1)], ![(-65498098721 / 125000000000), (-52398350713 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1896219488341 / 1000000000000), (1371937228929 / 1000000000000), (1371938037447 / 1000000000000), (-948097617093 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5023328151063 / 1000000000000), (-877596798357 / 500000000000), (-45509478127 / 40000000000), (-71108529941 / 62500000000), (-1755193236977 / 1000000000000), (-125583716791 / 25000000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-2511664075531 / 500000000000), (-1755193596713 / 1000000000000), (-568868476587 / 500000000000), (-227547295811 / 200000000000), (-109699577311 / 62500000000), (-5023348671639 / 1000000000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 0 18 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
