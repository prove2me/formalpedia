-- Prove2me | solution 1 for mme_released_interior_owner1_cell19_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:46.283985+00:00
-- url     : https://prove2.me/submissions/22d38ff3-2797-4de8-86f1-a2c33c0a1c00

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(408825951821000000000000000000000000 / 20249926062500107542971916783775569797), (803268172236000000000000000000000000 / 20249926062500107542971916783775569797), (408787256209000000000000000000000000 / 20249926062500107542971916783775569797), (1 / 1), (1 / 1)], ![(410386517219 / 1000000000000), (797027420811 / 1000000000000), (205173836973 / 500000000000), (1 / 1), (1 / 1)], ![(38593627073 / 1000000000000), (1127431400939 / 500000000000), (17710664894329 / 1000000000000), (563661860907 / 250000000000), (9648320823 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3902616901491 / 1000000000000), (-1613608900083 / 500000000000), (-3902711556547 / 1000000000000), (0 / 1), (0 / 1)], ![(-445327919223 / 500000000000), (-28358274469 / 125000000000), (-445375246693 / 500000000000), (0 / 1), (0 / 1)], ![(-1627334058939 / 500000000000), (203272282341 / 250000000000), (287416699453 / 100000000000), (406496808221 / 500000000000), (-101708657051 / 31250000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-390261690149 / 100000000000), (-645443560033 / 200000000000), (-1951355778273 / 500000000000), (0 / 1), (0 / 1)], ![(-178131167689 / 200000000000), (-226866195751 / 1000000000000), (-178150098677 / 200000000000), (0 / 1), (0 / 1)], ![(-3254668117877 / 1000000000000), (162617825873 / 200000000000), (2874166994531 / 1000000000000), (812993616443 / 1000000000000), (-3254677025631 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-959600200147 / 500000000000), (-829122370249 / 250000000000), (-4023974883339 / 500000000000), (-330487916439 / 100000000000), (-579917001389 / 1000000000000), (-1652440010981 / 500000000000), (-8048130166901 / 1000000000000), (-3316488622727 / 1000000000000), (-14993753129 / 7812500000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1919200400293 / 1000000000000), (-663297896199 / 200000000000), (-8047949766677 / 1000000000000), (-3304879164389 / 1000000000000), (-144979250347 / 250000000000), (-3304880021961 / 1000000000000), (-80481301669 / 10000000000), (-1658244311363 / 500000000000), (-1919200400511 / 1000000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 19 1 c : ℝ) / 1000000000000) ≤
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
