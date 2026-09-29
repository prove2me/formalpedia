-- Prove2me | solution 1 for mme_released_interior_owner0_cell37_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:15.032047+00:00
-- url     : https://prove2.me/submissions/cb9a4005-3f0c-4532-ba29-1f3fccfce70c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (31488163114000000000000000000000000 / 1511966607153408400740633105142565223), (761755196887400000000000000000000000 / 1511966607153408400740633105142565223), (253918369351400000000000000000000000 / 503988869051136133580211035047521741), (2862558935600000000000000000000000 / 137451509741218945521875736831142293)], ![(293143282331 / 500000000000), (1046024203759 / 1000000000000), (187611637 / 320000000), (1 / 1), (1 / 1)], ![(37443243777 / 62500000000), (599091794277 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-967888692557 / 250000000000), (-685541231137 / 1000000000000), (-342770673877 / 500000000000), (-3871555240957 / 1000000000000)], ![(-266973295371 / 500000000000), (44996504723 / 1000000000000), (-533946930229 / 1000000000000), (0 / 1), (0 / 1)], ![(-512340269543 / 1000000000000), (-512340446737 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3871554770227 / 1000000000000), (-21423163473 / 31250000000), (-685541347753 / 1000000000000), (-967888810239 / 250000000000)], ![(-533946590741 / 1000000000000), (11249126181 / 250000000000), (-133486732557 / 250000000000), (0 / 1), (0 / 1)], ![(-256170134771 / 500000000000), (-32021277921 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-76841283549 / 15625000000), (-23057703463 / 20000000000), (-1731828430907 / 1000000000000), (-173182838523 / 100000000000), (-46115404503 / 40000000000), (-4917842101203 / 1000000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-983568429427 / 200000000000), (-1152885173149 / 1000000000000), (-865914215453 / 500000000000), (-1731828385229 / 1000000000000), (-576442556287 / 500000000000), (-2458921050601 / 500000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 37 1 c : ℝ) / 1000000000000) ≤
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
