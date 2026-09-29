-- Prove2me | solution 1 for mme_released_interior_owner2_cell27_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:32.058352+00:00
-- url     : https://prove2.me/submissions/958b41b3-efa8-4fd3-8bcf-56236d93f634

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 2 27 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(169774331859 / 1000000000000), (305191375529 / 125000000000), (2441542500293 / 1000000000000), (169776604199 / 1000000000000), (1 / 1)], ![(175639207222000000000000000000000000 / 15856388849862416647957287955557182847), (785333521387000000000000000000000000 / 5285462949954138882652429318519060949), (2356011564796000000000000000000000000 / 15856388849862416647957287955557182847), (175641769630000000000000000000000000 / 15856388849862416647957287955557182847), (1 / 1)], ![(445005150979 / 1000000000000), (432330961071 / 500000000000), (111252330621 / 250000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-22166064793 / 12500000000), (223156325821 / 250000000000), (892630011819 / 1000000000000), (-1773271799057 / 1000000000000), (0 / 1)], ![(-450289584807 / 100000000000), (-59581468621 / 31250000000), (-476650581671 / 250000000000), (-4502881259133 / 1000000000000), (0 / 1)], ![(-16193388433 / 20000000000), (-9088543119 / 62500000000), (-404830023817 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1773285183439 / 1000000000000), (178525060657 / 200000000000), (44631500591 / 50000000000), (-110829487441 / 62500000000), (0 / 1)], ![(-4502895848069 / 1000000000000), (-1906606995871 / 1000000000000), (-1906602326683 / 1000000000000), (-1125720314783 / 250000000000), (0 / 1)], ![(-809669421649 / 1000000000000), (-145416689903 / 1000000000000), (-809660047633 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-2210920513873 / 500000000000), (-6407522638883 / 1000000000000), (-1823356505711 / 1000000000000), (-289866771653 / 250000000000), (-2245800795133 / 500000000000), (-1122900233231 / 250000000000), (-1159467125869 / 1000000000000), (-227919562751 / 125000000000), (-800940179021 / 125000000000), (-1105460130751 / 250000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-884368205549 / 200000000000), (-3203761319441 / 500000000000), (-182335650571 / 100000000000), (-1159467086611 / 1000000000000), (-898320318053 / 200000000000), (-4491600932923 / 1000000000000), (-289866781467 / 250000000000), (-1823356502007 / 1000000000000), (-6407521432167 / 1000000000000), (-4421840523003 / 1000000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 2 27 3 c : ℝ) / 1000000000000) ≤
          (431 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (431 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((431 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
