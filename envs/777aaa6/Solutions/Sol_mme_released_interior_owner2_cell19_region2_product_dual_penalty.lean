-- Prove2me | solution 1 for mme_released_interior_owner2_cell19_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:03.724779+00:00
-- url     : https://prove2.me/submissions/38ae5cf9-7516-4f54-892b-515d1891faf5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 2 19 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(51093773807 / 125000000000), (803241013707 / 1000000000000), (25546948007 / 62500000000), (1 / 1), (1 / 1)], ![(410220652981000000000000000000000000 / 20261401521755717775011973866627941643), (796646080334000000000000000000000000 / 20261401521755717775011973866627941643), (410221634687000000000000000000000000 / 20261401521755717775011973866627941643), (1 / 1), (1 / 1)], ![(19361997169 / 500000000000), (564228897833 / 250000000000), (1772996330469 / 100000000000), (2256921034837 / 1000000000000), (3872399867 / 100000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-111831386353 / 125000000000), (-219100468467 / 1000000000000), (-894648699009 / 1000000000000), (0 / 1), (0 / 1)], ![(-779955551853 / 200000000000), (-3236062436861 / 1000000000000), (-3899775366151 / 1000000000000), (0 / 1), (0 / 1)], ![(-3251295862339 / 1000000000000), (813999098523 / 1000000000000), (287525605041 / 100000000000), (814001510443 / 1000000000000), (-325129575047 / 100000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-894651090823 / 1000000000000), (-109550234233 / 500000000000), (-6989442961 / 7812500000), (0 / 1), (0 / 1)], ![(-121868054977 / 31250000000), (-161803121843 / 50000000000), (-77995507323 / 20000000000), (0 / 1), (0 / 1)], ![(-1625647931169 / 500000000000), (203499774631 / 250000000000), (2875256050411 / 1000000000000), (203500377611 / 250000000000), (-3251295750469 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-64365796811 / 8000000000), (-206554794881 / 62500000000), (-959585203831 / 500000000000), (-3316712016441 / 1000000000000), (-289953427457 / 500000000000), (-1658356019083 / 500000000000), (-1919170406769 / 1000000000000), (-413109591911 / 125000000000), (-8045719926989 / 1000000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4022862300687 / 500000000000), (-660975343619 / 200000000000), (-1919170407661 / 1000000000000), (-82917800411 / 25000000000), (-579906854913 / 1000000000000), (-663342407633 / 200000000000), (-119948150423 / 62500000000), (-3304876735287 / 1000000000000), (-2011429981747 / 250000000000)] : List ℚ).getD
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
        (splitWeight 2 19 2 c : ℝ) / 1000000000000) ≤
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
