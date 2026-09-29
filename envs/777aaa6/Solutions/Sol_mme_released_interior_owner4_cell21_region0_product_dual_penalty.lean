-- Prove2me | solution 1 for mme_released_interior_owner4_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:17:55.089992+00:00
-- url     : https://prove2.me/submissions/ffdb7095-8a55-4aac-9b87-e86c20b81372

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 4 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(415586342643 / 1000000000000), (98569184383 / 125000000000), (83127356433 / 200000000000), (1 / 1), (1 / 1)], ![(38849003263000000000000000000000000 / 19952570013630854038711843991805529079), (177600117525000000000000000000000000 / 1534813077971604156823987999369656083), (17059800621293000000000000000000000000 / 19952570013630854038711843991805529079), (2309084368910000000000000000000000000 / 19952570013630854038711843991805529079), (38849205128000000000000000000000000 / 19952570013630854038711843991805529079)], ![(81218301631 / 200000000000), (51643528437 / 62500000000), (40614078961 / 100000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5487905513 / 6250000000), (-47511011231 / 200000000000), (-219485879977 / 250000000000), (0 / 1), (0 / 1)], ![(-6241430816311 / 1000000000000), (-2156629387001 / 1000000000000), (-78316551347 / 500000000000), (-1078253444459 / 500000000000), (-6241425620181 / 1000000000000)], ![(-901176755233 / 1000000000000), (-5962552047 / 31250000000), (-450527703527 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-878064882079 / 1000000000000), (-118777528077 / 500000000000), (-877943519907 / 1000000000000), (0 / 1), (0 / 1)], ![(-624143081631 / 100000000000), (-2156629387 / 1000000000), (-156633102693 / 1000000000000), (-2156506888917 / 1000000000000), (-312071281009 / 50000000000)], ![(-28161773601 / 31250000000), (-190801665503 / 1000000000000), (-901055407053 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020429743213 / 1000000000000), (-3225374569691 / 1000000000000), (-3295239853123 / 1000000000000), (-967876689293 / 500000000000), (-584989824351 / 1000000000000), (-1935753391079 / 1000000000000), (-3295238697377 / 1000000000000), (-3225373439219 / 1000000000000), (-8020667258633 / 1000000000000)] : List ℚ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-2005107435803 / 250000000000), (-322537456969 / 100000000000), (-1647619926561 / 500000000000), (-387150675717 / 200000000000), (-11699796487 / 20000000000), (-967876695539 / 500000000000), (-102976209293 / 31250000000), (-1612686719609 / 500000000000), (-1002583407329 / 125000000000)] : List ℚ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 4 21 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
