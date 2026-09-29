-- Prove2me | solution 1 for mme_released_interior_owner0_cell10_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:59:59.108024+00:00
-- url     : https://prove2.me/submissions/085039da-5371-4c95-9937-fcbfb7a120fd

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(56595614501000000000000000000000000 / 251379035185198319407138180844233591), (56595724712200000000000000000000000 / 251379035185198319407138180844233591), (1 / 1), (1 / 1), (1 / 1)], ![(850819666261 / 1000000000000), (425409796247 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (299271669909 / 500000000000), (2011685506153 / 1000000000000), (149635146641 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-372757600131 / 250000000000), (-1491028453181 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161555080901 / 1000000000000), (-80777583801 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-513256342541 / 1000000000000), (13979458619 / 20000000000), (-128315235619 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1491030400523 / 1000000000000), (-74551422659 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1615550809 / 10000000000), (-161555167601 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-25662817127 / 50000000000), (698972930951 / 1000000000000), (-20530437699 / 40000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2165846423899 / 1000000000000), (-38144505487 / 40000000000), (-238402650783 / 250000000000), (-1082919981661 / 500000000000)] : List ℚ).getD
    ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-1082923211949 / 500000000000), (-476806318587 / 500000000000), (-953610603131 / 1000000000000), (-2165839963321 / 1000000000000)] : List ℚ).getD
    ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 0 10 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
