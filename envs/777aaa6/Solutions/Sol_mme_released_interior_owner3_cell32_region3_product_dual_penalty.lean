-- Prove2me | solution 1 for mme_released_interior_owner3_cell32_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:17:03.177994+00:00
-- url     : https://prove2.me/submissions/200c29e7-fc8a-43df-9a94-a23474f9b99c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(711698250071 / 250000000000000), (171893751320927 / 1000000000000000), (242408497957833 / 200000000000000), (171893858115931 / 1000000000000000), (711598637151 / 250000000000000)], ![(90092070185927 / 250000000000000), (183779250103767 / 250000000000000), (90092075061133 / 250000000000000), (1 / 1), (1 / 1)], ![(327415678836977 / 1000000000000000), (310658437225647 / 500000000000000), (163707863992239 / 500000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![8, 3, 0, 3, 8], ![1, 0, 1, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2930781090671823 / 500000000000000), (-1760878717917637 / 1000000000000000), (192306944614439 / 1000000000000000), (-1760878096632861 / 1000000000000000), (-2930851078122127 / 500000000000000)], ![(-204125753675229 / 200000000000000), (-15386280409979 / 50000000000000), (-1020628714262549 / 1000000000000000), (0 / 1), (0 / 1)], ![(-1116524726257787 / 1000000000000000), (-475914062372583 / 1000000000000000), (-223304915230089 / 200000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2930781090671819 / 500000000000000), (-880439358958817 / 500000000000000), (4807673615361 / 25000000000000), (-880439048316429 / 500000000000000), (-5861702156244247 / 1000000000000000)], ![(-1020628768376143 / 1000000000000000), (-307725608199579 / 1000000000000000), (-255157178565637 / 250000000000000), (0 / 1), (0 / 1)], ![(-139565590782223 / 125000000000000), (-237957031186291 / 500000000000000), (-558262288075221 / 500000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-972423248057859 / 500000000000000), (-1592564215182481 / 500000000000000), (-1599771130175623 / 200000000000000), (-325742149377313 / 100000000000000), (-295666362978861 / 500000000000000), (-203588808010077 / 62500000000000), (-3999357735878323 / 500000000000000), (-3185128902992927 / 1000000000000000), (-243105799962791 / 125000000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-388969299223143 / 200000000000000), (-3185128430364957 / 1000000000000000), (-999856956359763 / 125000000000000), (-5211874390037 / 1600000000000), (-14783318148943 / 25000000000000), (-3257420928161227 / 1000000000000000), (-1599743094351327 / 200000000000000), (-1592564451496461 / 500000000000000), (-486211599925581 / 250000000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 3 32 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
