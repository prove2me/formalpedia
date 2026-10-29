-- Prove2me | solution 1 for mme_released_interior_owner3_cell32_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:17:12.691508+00:00
-- url     : https://prove2.me/submissions/62e308ca-d2db-40c4-8da9-d9cb025d7e85

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2848912129047 / 1000000000000000), (8515543920371 / 50000000000000), (121422172475247 / 100000000000000), (42577706297231 / 250000000000000), (2849025133289 / 1000000000000000)], ![(354648045018427 / 1000000000000000), (742625285872189 / 1000000000000000), (88662004770081 / 250000000000000), (1 / 1), (1 / 1)], ![(166130924074293 / 500000000000000), (615272073689571 / 1000000000000000), (33226184668581 / 100000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![8, 3, 0, 3, 8], ![1, 0, 1, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2930409033338681 / 500000000000000), (-1770129815447437 / 1000000000000000), (24262914473717 / 125000000000000), (-885065063963017 / 500000000000000), (-293038920085601 / 50000000000000)], ![(-1036629403774367 / 1000000000000000), (-297563687358063 / 1000000000000000), (-1036629476911959 / 1000000000000000), (0 / 1), (0 / 1)], ![(-1101831921682729 / 1000000000000000), (-242845356380391 / 500000000000000), (-1101831926085209 / 1000000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1172163613335471 / 200000000000000), (-885064907723717 / 500000000000000), (194103315789737 / 1000000000000000), (-1770130127926031 / 1000000000000000), (-5860778401712013 / 1000000000000000)], ![(-518314701887183 / 500000000000000), (-148781843679031 / 500000000000000), (-1036629476911957 / 1000000000000000), (0 / 1), (0 / 1)], ![(-1101831921682727 / 1000000000000000), (-24284535638039 / 50000000000000), (-550915963042603 / 500000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944358094170857 / 1000000000000000), (-633905139653781 / 200000000000000), (-7999239727169227 / 1000000000000000), (-3292449961360617 / 1000000000000000), (-147287771082277 / 250000000000000), (-13169801152883 / 4000000000000), (-3999639734837189 / 500000000000000), (-396190683448577 / 125000000000000), (-1944358002703933 / 1000000000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944358094170853 / 1000000000000000), (-31695256982689 / 10000000000000), (-7999239727169217 / 1000000000000000), (-823112490340153 / 250000000000000), (-294575542164553 / 500000000000000), (-658490057644149 / 200000000000000), (-62494370856831 / 7812500000000), (-3169525467588611 / 1000000000000000), (-1944358002703929 / 1000000000000000)] : List ℚ).getD
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
        (splitWeight 3 32 5 c : ℝ) / 1000000000000) ≤
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
