-- Prove2me | solution 1 for mme_released_interior_owner1_cell36_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:43.877632+00:00
-- url     : https://prove2.me/submissions/890036ab-23ef-4cf8-8ceb-ee3e0e627e25

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (39359452031500000000000000000000000 / 1890127117103052922261312603235929961), (952069629538500000000000000000000000 / 1890127117103052922261312603235929961), (952244247768250000000000000000000000 / 1890127117103052922261312603235929961), (39360559029500000000000000000000000 / 1890127117103052922261312603235929961)], ![(149796792801 / 250000000000), (7491416443 / 12500000000), (1 / 1), (1 / 1), (1 / 1)], ![(117246786551 / 200000000000), (209148090063 / 200000000000), (36653079699 / 62500000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-967915803349 / 250000000000), (-685761191131 / 1000000000000), (-171394449713 / 250000000000), (-3871635088451 / 1000000000000)], ![(-256090628441 / 500000000000), (-127992688361 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-133509091603 / 250000000000), (44725199397 / 1000000000000), (-266834550977 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-774332642679 / 200000000000), (-68576119113 / 100000000000), (-685577798851 / 1000000000000), (-77432701769 / 20000000000)], ![(-512181256881 / 1000000000000), (-511970753443 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-534036366411 / 1000000000000), (22362599699 / 500000000000), (-533669101953 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4917303068837 / 1000000000000), (-144125843147 / 125000000000), (-432902887491 / 250000000000), (-865792459353 / 500000000000), (-72064616021 / 62500000000), (-1229463177949 / 250000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1229325767209 / 250000000000), (-46120269807 / 40000000000), (-1731611549963 / 1000000000000), (-346316983741 / 200000000000), (-230606771267 / 200000000000), (-983570542359 / 200000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 1 36 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
