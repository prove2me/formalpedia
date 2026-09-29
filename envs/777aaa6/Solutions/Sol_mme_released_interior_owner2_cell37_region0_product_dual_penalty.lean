-- Prove2me | solution 1 for mme_released_interior_owner2_cell37_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:42.660242+00:00
-- url     : https://prove2.me/submissions/b2e7d35c-f159-43e3-b636-a7edcf03665a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 2 37 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1571073433 / 10000000000), (238272152757 / 62500000000), (1906154828937 / 500000000000), (39276851877 / 250000000000)], ![(58429354156700000000000000000000000 / 757743493734411931854289980833543283), (35030792658100000000000000000000000 / 252581164578137310618096660277847761), (19476016628000000000000000000000000 / 252581164578137310618096660277847761), (1 / 1), (1 / 1)], ![(37433614641 / 62500000000), (598931217233 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-74033039679 / 40000000000), (1338246962611 / 1000000000000), (1338235214883 / 1000000000000), (-925412791643 / 500000000000)], ![(-2562526526383 / 1000000000000), (-395101035201 / 200000000000), (-2562548848849 / 1000000000000), (0 / 1), (0 / 1)], ![(-512597468797 / 1000000000000), (-128152129197 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-925412995987 / 500000000000), (334561740653 / 250000000000), (334558803721 / 250000000000), (-370165116657 / 200000000000)], ![(-1281263263191 / 500000000000), (-493876294001 / 250000000000), (-160159303053 / 62500000000), (0 / 1), (0 / 1)], ![(-128149367199 / 250000000000), (-512608516787 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1736899828289 / 1000000000000), (-197037983137 / 40000000000), (-1149866730181 / 1000000000000), (-1149867429919 / 1000000000000), (-1231495839403 / 250000000000), (-1736899355033 / 1000000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-27139059817 / 15625000000), (-615743697303 / 125000000000), (-57493336509 / 50000000000), (-574933714959 / 500000000000), (-4925983357611 / 1000000000000), (-217112419379 / 125000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 2 37 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
