-- Prove2me | solution 1 for mme_released_interior_owner3_cell22_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:37.611988+00:00
-- url     : https://prove2.me/submissions/93c58ddf-13c5-4cf1-9738-c90906124a76

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 3 22 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(582262511673 / 1000000000000), (1051686375889 / 1000000000000), (582262956987 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (155017965791 / 1000000000000), (3851744889301 / 1000000000000), (1925873126357 / 500000000000), (77508917927 / 500000000000)], ![(298559538091000000000000000000000000 / 3811899963393579464643021777256121301), (298559666192000000000000000000000000 / 3811899963393579464643021777256121301), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-13520847049 / 25000000000), (50394948089 / 1000000000000), (-540833117161 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1864214260451 / 1000000000000), (1348526263627 / 1000000000000), (52676821 / 39062500), (-932107549329 / 500000000000)], ![(-159182103209 / 62500000000), (-63672830557 / 25000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-540833881959 / 1000000000000), (5039494809 / 100000000000), (-13520827929 / 25000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-37284285209 / 20000000000), (337131565907 / 250000000000), (1348526617601 / 1000000000000), (-1864215098657 / 1000000000000)], ![(-2546913651343 / 1000000000000), (-2546913222279 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-2475981315963 / 500000000000), (-1147992085653 / 1000000000000), (-869610252437 / 500000000000), (-1739220486639 / 1000000000000), (-1147992010563 / 1000000000000), (-2475980299983 / 500000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-198078505277 / 40000000000), (-286998021413 / 250000000000), (-1739220504873 / 1000000000000), (-869610243319 / 500000000000), (-573996005281 / 500000000000), (-990392119993 / 200000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 3 22 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
