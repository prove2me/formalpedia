-- Prove2me | solution 1 for mme_released_interior_owner1_cell18_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:44.050747+00:00
-- url     : https://prove2.me/submissions/35daf10a-6f28-4f0d-9fbe-cb089433bd98

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 1 18 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(574010768745000000000000000000000000 / 7751142576591444477439074971952925081), (1064387655392000000000000000000000000 / 7751142576591444477439074971952925081), (574014403058000000000000000000000000 / 7751142576591444477439074971952925081), (1 / 1), (1 / 1)], ![(592325077137 / 1000000000000), (592326941731 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (150227514483 / 1000000000000), (3940872602909 / 1000000000000), (49261071933 / 12500000000), (150227800197 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-162684211481 / 62500000000), (-992720299699 / 500000000000), (-2602941052279 / 1000000000000), (0 / 1), (0 / 1)], ![(-523699678023 / 1000000000000), (-65462066263 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-189560437079 / 100000000000), (1371402171607 / 1000000000000), (685702754433 / 500000000000), (-473900617229 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-520589476739 / 200000000000), (-1985440599397 / 1000000000000), (-1301470526139 / 500000000000), (0 / 1), (0 / 1)], ![(-261849839011 / 500000000000), (-523696530103 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1895604370789 / 1000000000000), (171425271451 / 125000000000), (1371405508867 / 1000000000000), (-379120493783 / 200000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1755238404931 / 1000000000000), (-5022249530691 / 1000000000000), (-227546991579 / 200000000000), (-568867384277 / 500000000000), (-31389012207 / 6250000000), (-438809639673 / 250000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-175523840493 / 100000000000), (-502224953069 / 100000000000), (-568867478947 / 500000000000), (-1137734768553 / 1000000000000), (-5022241953119 / 1000000000000), (-1755238558691 / 1000000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 1 18 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
