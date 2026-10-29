-- Prove2me | solution 1 for mme_released_interior_owner3_cell32_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:16:41.753559+00:00
-- url     : https://prove2.me/submissions/cc35e8a0-e9d1-41b5-b278-ec13d5576eeb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2847002998857 / 1000000000000000), (171880560431159 / 1000000000000000), (605959573911541 / 500000000000000), (17188068108377 / 100000000000000), (569309419353 / 200000000000000)], ![(376733885468617 / 1000000000000000), (178953377239219 / 250000000000000), (47091738975219 / 125000000000000), (1 / 1), (1 / 1)], ![(313226229942043 / 1000000000000000), (31906895903951 / 50000000000000), (313226278174677 / 1000000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![8, 3, 0, 3, 8], ![1, 0, 1, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-586148841734749 / 100000000000000), (-880477729742567 / 500000000000000), (192205175705001 / 1000000000000000), (-880477378764631 / 500000000000000), (-146541214105257 / 25000000000000)], ![(-976216214869089 / 1000000000000000), (-334335608298433 / 1000000000000000), (-976216144970587 / 1000000000000000), (0 / 1), (0 / 1)], ![(-72551848134603 / 62500000000000), (-89840169292323 / 200000000000000), (-580414708083543 / 500000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5861488417347483 / 1000000000000000), (-1760955459485131 / 1000000000000000), (96102587852501 / 500000000000000), (-1760954757529259 / 1000000000000000), (-183176517631571 / 31250000000000)], ![(-976216214869087 / 1000000000000000), (-5223993879663 / 15625000000000), (-195243228994117 / 200000000000000), (0 / 1), (0 / 1)], ![(-580414785076823 / 500000000000000), (-224600423230807 / 500000000000000), (-290207354041771 / 250000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944840539725379 / 1000000000000000), (-203507495927829 / 62500000000000), (-7998694349233009 / 1000000000000000), (-3186372449857793 / 1000000000000000), (-295665639527523 / 500000000000000), (-796592954979877 / 250000000000000), (-3999266989242597 / 500000000000000), (-3256120485086731 / 1000000000000000), (-1944840455025027 / 1000000000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-30388133433209 / 15625000000000), (-3256119934845259 / 1000000000000000), (-3999347174616499 / 500000000000000), (-796593112464447 / 250000000000000), (-147832819763761 / 250000000000000), (-3186371819919503 / 1000000000000000), (-7998533978485183 / 1000000000000000), (-1628060242543363 / 500000000000000), (-15194066054883 / 7812500000000)] : List ℚ).getD
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
        (splitWeight 3 32 2 c : ℝ) / 1000000000000) ≤
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
