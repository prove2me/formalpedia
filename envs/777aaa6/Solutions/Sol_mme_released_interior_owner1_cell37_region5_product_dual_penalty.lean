-- Prove2me | solution 1 for mme_released_interior_owner1_cell37_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:25:34.438822+00:00
-- url     : https://prove2.me/submissions/61762f0a-272e-4db2-aa12-cd451004b11f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (39474021353500000000000000000000000 / 1888549874040033347190902175635728963), (949746833350750000000000000000000000 / 1888549874040033347190902175635728963), (949749879144000000000000000000000000 / 1888549874040033347190902175635728963), (39474014808750000000000000000000000 / 1888549874040033347190902175635728963)], ![(586324276773 / 1000000000000), (1046751515203 / 1000000000000), (3664549033 / 6250000000), (1 / 1), (1 / 1)], ![(149964915429 / 250000000000), (18745670731 / 31250000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1933960891431 / 500000000000), (-27494763731 / 40000000000), (-85920735791 / 125000000000), (-3867921948661 / 1000000000000)], ![(-533882269127 / 1000000000000), (22845786723 / 500000000000), (-4170907679 / 7812500000), (0 / 1), (0 / 1)], ![(-102211909653 / 200000000000), (-511056544773 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3867921782861 / 1000000000000), (-343684546637 / 500000000000), (-687365886327 / 1000000000000), (-193396097433 / 50000000000)], ![(-266941134563 / 500000000000), (45691573447 / 1000000000000), (-533876182911 / 1000000000000), (0 / 1), (0 / 1)], ![(-63882443533 / 125000000000), (-127764136193 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1228213627653 / 250000000000), (-1732304824451 / 1000000000000), (-1152734064601 / 1000000000000), (-1152733861141 / 1000000000000), (-1732304700229 / 1000000000000), (-4912863766079 / 1000000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4912854510611 / 1000000000000), (-34646096489 / 20000000000), (-5763670323 / 5000000000), (-57636693057 / 50000000000), (-433076175057 / 250000000000), (-2456431883039 / 500000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 37 5 c : ℝ) / 1000000000000) ≤
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
