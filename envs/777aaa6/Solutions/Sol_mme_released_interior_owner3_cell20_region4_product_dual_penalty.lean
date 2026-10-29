-- Prove2me | solution 1 for mme_released_interior_owner3_cell20_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:28:38.255545+00:00
-- url     : https://prove2.me/submissions/8b739035-d5a5-46ac-9d30-0d6057def1e4

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(4331302618147656686973818523 / 12500000000000000000000000000), (66333193420649436668065793499 / 100000000000000000000000000000), (693008414840693069915851593 / 2000000000000000000000000000), (1 / 1), (1 / 1)], ![(210830858757097891691412429 / 4000000000000000000000000000), (1988278305055080117216949449 / 2500000000000000000000000000), (79531131129180904688688708183 / 100000000000000000000000000000), (5270772865613247292271343867 / 100000000000000000000000000000), (1 / 1)], ![(4172490409841858275095901581 / 100000000000000000000000000000), (59294391698917107056083010823 / 100000000000000000000000000000), (59294393807068707056061929307 / 100000000000000000000000000000), (834497236285291655027637147 / 20000000000000000000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![4, 0, 0, 4, 0], ![5, 1, 1, 5, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1059860311935893 / 1000000000000000), (-3283838073363 / 8000000000000), (-1059860317798639 / 1000000000000000), (0 / 1), (0 / 1)], ![(-2942993445357829 / 1000000000000000), (-57255410238843 / 250000000000000), (-28627706805903 / 125000000000000), (-2942993180370887 / 1000000000000000), (0 / 1)], ![(-397082138482131 / 125000000000000), (-104531091903467 / 200000000000000), (-130663855990839 / 250000000000000), (-127066324850433 / 40000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1059860311935891 / 1000000000000000), (-410479759170373 / 1000000000000000), (-264965079449659 / 250000000000000), (0 / 1), (0 / 1)], ![(-117719737814313 / 40000000000000), (-229021640955371 / 1000000000000000), (-229021654447223 / 1000000000000000), (-1471496590185441 / 500000000000000), (0 / 1)], ![(-3176657107857043 / 1000000000000000), (-522655459517333 / 1000000000000000), (-261327711981677 / 500000000000000), (-158832906063041 / 50000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([9, 6, 7, 2, 3, 3, 2, 7, 6, 9] : List ℤ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1625264032320819 / 250000000000000), (-2234644429736143 / 500000000000000), (-4529490946657157 / 1000000000000000), (-1162294461076143 / 1000000000000000), (-452752702159383 / 250000000000000), (-1811010780727363 / 1000000000000000), (-1162294412199617 / 1000000000000000), (-452949117778659 / 100000000000000), (-4469289852449107 / 1000000000000000), (-3250528703852747 / 500000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6501056129283267 / 1000000000000000), (-111732221486807 / 25000000000000), (-4529490946657151 / 1000000000000000), (-58114723053807 / 50000000000000), (-226376351079691 / 125000000000000), (-1811010780727359 / 1000000000000000), (-232458882439923 / 200000000000000), (-4529491177786583 / 1000000000000000), (-4469289852449101 / 1000000000000000), (-3250528703852743 / 500000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 3 20 4 c : ℝ) / 1000000000000) ≤
          (1642 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1642 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1642 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
