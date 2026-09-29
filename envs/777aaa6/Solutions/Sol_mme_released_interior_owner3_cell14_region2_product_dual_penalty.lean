-- Prove2me | solution 1 for mme_released_interior_owner3_cell14_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:47.695859+00:00
-- url     : https://prove2.me/submissions/29f23500-7768-4cda-b410-4f5b6f311110

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2334403339 / 3906250000), (597608441101 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (154939742243 / 1000000000000), (1926257048117 / 500000000000), (3852519698817 / 1000000000000), (19367929083 / 125000000000)], ![(64696885151000000000000000000000000 / 847600852342853219366982773268467211), (350335266436000000000000000000000000 / 2542802557028559658100948319805401633), (582274156384000000000000000000000000 / 7628407671085678974302844959416204899), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-128705376343 / 250000000000), (-257409760131 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1864718997373 / 1000000000000), (337181486797 / 250000000000), (674363700727 / 500000000000), (-1864695179229 / 1000000000000)], ![(-1286348387297 / 500000000000), (-1982131520569 / 1000000000000), (-2572693013429 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-514821505371 / 1000000000000), (-514819520261 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-466179749343 / 250000000000), (1348725947189 / 1000000000000), (269745480291 / 200000000000), (-466173794807 / 250000000000)], ![(-2572696774593 / 1000000000000), (-247766440071 / 125000000000), (-643173253357 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-619026682397 / 125000000000), (-1738788893397 / 1000000000000), (-287056406121 / 250000000000), (-71764068353 / 62500000000), (-217348571451 / 125000000000), (-495223153101 / 100000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-198088538367 / 40000000000), (-434697223349 / 250000000000), (-1148225624483 / 1000000000000), (-1148225093647 / 1000000000000), (-1738788571607 / 1000000000000), (-4952231531009 / 1000000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 3 14 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
