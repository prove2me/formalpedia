-- Prove2me | solution 1 for mme_released_interior_owner2_cell19_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:04.374797+00:00
-- url     : https://prove2.me/submissions/b0ce0075-9065-41c5-be4b-0c61e19d5e2e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 2 19 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(10031934431 / 25000000000), (415051223373 / 500000000000), (200639219027 / 500000000000), (1 / 1), (1 / 1)], ![(207616071395000000000000000000000000 / 10174802682095933014435214171249350319), (386985099749500000000000000000000000 / 10174802682095933014435214171249350319), (207616620491000000000000000000000000 / 10174802682095933014435214171249350319), (1 / 1), (1 / 1)], ![(7789701719 / 200000000000), (278596392709 / 125000000000), (17849101175603 / 1000000000000), (2228777310811 / 1000000000000), (1217140933 / 31250000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-114137797123 / 125000000000), (-93103077997 / 500000000000), (-182619946679 / 200000000000), (0 / 1), (0 / 1)], ![(-3891979054207 / 1000000000000), (-3269283427351 / 1000000000000), (-778395281889 / 200000000000), (0 / 1), (0 / 1)], ![(-3245514797643 / 1000000000000), (801450376037 / 1000000000000), (2881953152649 / 1000000000000), (801453143989 / 1000000000000), (-3245514765267 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-913102376983 / 1000000000000), (-186206155993 / 1000000000000), (-456549866697 / 500000000000), (0 / 1), (0 / 1)], ![(-1945989527103 / 500000000000), (-65385668547 / 20000000000), (-972994102361 / 250000000000), (0 / 1), (0 / 1)], ![(-1622757398821 / 500000000000), (400725188019 / 500000000000), (57639063053 / 20000000000), (80145314399 / 100000000000), (-1622757382633 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8050596195663 / 1000000000000), (-819183029953 / 250000000000), (-120195351319 / 62500000000), (-845233150213 / 250000000000), (-114707286139 / 200000000000), (-338093284421 / 100000000000), (-240390705953 / 125000000000), (-819183033953 / 250000000000), (-1610118188061 / 200000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4025298097831 / 500000000000), (-3276732119811 / 1000000000000), (-1923125621103 / 1000000000000), (-3380932600851 / 1000000000000), (-286768215347 / 500000000000), (-3380932844209 / 1000000000000), (-1923125647623 / 1000000000000), (-3276732135811 / 1000000000000), (-503161933769 / 62500000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 19 3 c : ℝ) / 1000000000000) ≤
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
