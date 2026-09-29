-- Prove2me | solution 1 for mme_released_interior_owner0_cell36_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:14.174833+00:00
-- url     : https://prove2.me/submissions/8ce790e0-1dde-4826-acf1-582ffd32433f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (7895014380200000000000000000000000 / 377685757434256766985674265026680661), (189951010470100000000000000000000000 / 377685757434256766985674265026680661), (189950850550550000000000000000000000 / 377685757434256766985674265026680661), (7895004770500000000000000000000000 / 377685757434256766985674265026680661)], ![(119976007351 / 200000000000), (149969884071 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(586419350481 / 1000000000000), (8175654937 / 7812500000), (586418724963 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1933915525599 / 500000000000), (-171824080263 / 250000000000), (-687297162951 / 1000000000000), (-120869758387 / 31250000000)], ![(-511025582499 / 1000000000000), (-31939151049 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533720130181 / 1000000000000), (45435813129 / 1000000000000), (-106744239371 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3867831051197 / 1000000000000), (-687296321051 / 1000000000000), (-13745943259 / 20000000000), (-3867832268383 / 1000000000000)], ![(-255512791249 / 500000000000), (-511026416783 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-26686006509 / 50000000000), (4543581313 / 100000000000), (-266860598427 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-982515732957 / 200000000000), (-433010775101 / 250000000000), (-115288692471 / 100000000000), (-576443466159 / 500000000000), (-866021854957 / 500000000000), (-491257798103 / 100000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-307036166549 / 62500000000), (-1732043100403 / 1000000000000), (-1152886924709 / 1000000000000), (-1152886932317 / 1000000000000), (-1732043709913 / 1000000000000), (-4912577981029 / 1000000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 36 5 c : ℝ) / 1000000000000) ≤
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
