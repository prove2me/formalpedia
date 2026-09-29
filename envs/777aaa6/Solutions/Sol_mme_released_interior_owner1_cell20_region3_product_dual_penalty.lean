-- Prove2me | solution 1 for mme_released_interior_owner1_cell20_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:48.991709+00:00
-- url     : https://prove2.me/submissions/494103cf-df5f-430d-9b99-b8148234ebca

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 1 20 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(44334603895300000000000000000000000 / 1624972964431762720414220560765569129), (84893218843400000000000000000000000 / 1624972964431762720414220560765569129), (44329774939300000000000000000000000 / 1624972964431762720414220560765569129), (1 / 1), (1 / 1)], ![(85156479873 / 500000000000), (2402490730381 / 1000000000000), (480472870001 / 200000000000), (170275882953 / 1000000000000), (1 / 1)], ![(82164800079 / 500000000000), (155782579287 / 62500000000), (1246190417551 / 500000000000), (82156366629 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1800740479459 / 500000000000), (-1475926119753 / 500000000000), (-900397471387 / 250000000000), (0 / 1), (0 / 1)], ![(-1770117594703 / 1000000000000), (219126500883 / 250000000000), (876453398251 / 1000000000000), (-27661489319 / 15625000000), (0 / 1)], ![(-1805881110957 / 1000000000000), (913294755853 / 1000000000000), (913238412323 / 1000000000000), (-902991878447 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3601480958917 / 1000000000000), (-590370447901 / 200000000000), (-3601589885547 / 1000000000000), (0 / 1), (0 / 1)], ![(-885058797351 / 500000000000), (876506003533 / 1000000000000), (219113349563 / 250000000000), (-354067063283 / 200000000000), (0 / 1)], ![(-451470277739 / 250000000000), (456647377927 / 500000000000), (228309603081 / 250000000000), (-1805983756893 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4462190332647 / 1000000000000), (-181127009843 / 100000000000), (-4534904126123 / 1000000000000), (-6499473157053 / 1000000000000), (-1162239663829 / 1000000000000), (-232448677527 / 200000000000), (-6499358217919 / 1000000000000), (-36279702473 / 8000000000), (-905635038129 / 500000000000), (-2231069046759 / 500000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2231095166323 / 500000000000), (-1811270098429 / 1000000000000), (-2267452063061 / 500000000000), (-1624868289263 / 250000000000), (-290559915957 / 250000000000), (-581121693817 / 500000000000), (-3249679108959 / 500000000000), (-1133740702281 / 250000000000), (-1811270076257 / 1000000000000), (-4462138093517 / 1000000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 1 20 3 c : ℝ) / 1000000000000) ≤
          (1591 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1591 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1591 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
