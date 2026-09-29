-- Prove2me | solution 1 for mme_released_interior_owner2_cell10_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:14:33.184303+00:00
-- url     : https://prove2.me/submissions/75903d30-117d-46f3-97ee-69510ea931e6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 2 10 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(850624546719 / 1000000000000), (170124895089 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(84857986964500000000000000000000000 / 377439644836524605288776167358851921), (84857928839000000000000000000000000 / 377439644836524605288776167358851921), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (597511486699 / 1000000000000), (2016979528739 / 1000000000000), (597510237509 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![3, 3, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161784438457 / 1000000000000), (-161784522247 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1492431557029 / 1000000000000), (-1492432242003 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-514981770761 / 1000000000000), (701601109559 / 1000000000000), (-514983861417 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-20223054807 / 125000000000), (-80892261123 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-373107889257 / 250000000000), (-746216121001 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-12874544269 / 25000000000), (17540027739 / 25000000000), (-64372982677 / 125000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2169199856899 / 1000000000000), (-238153742429 / 250000000000), (-952615570899 / 1000000000000), (-2169198535011 / 1000000000000)] : List ℚ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-1084599928449 / 500000000000), (-190522993943 / 200000000000), (-476307785449 / 500000000000), (-216919853501 / 100000000000)] : List ℚ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 10 1 c : ℝ) / 1000000000000) ≤
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
