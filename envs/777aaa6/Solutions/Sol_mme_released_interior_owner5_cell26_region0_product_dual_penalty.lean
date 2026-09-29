-- Prove2me | solution 1 for mme_released_interior_owner5_cell26_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:23:10.05726+00:00
-- url     : https://prove2.me/submissions/a37447f5-0d2d-4fe9-8337-1aa7a77f5c3e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 5 26 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(176432083063 / 1000000000000), (292953025947 / 125000000000), (585873939777 / 250000000000), (176403155087 / 1000000000000), (1 / 1)], ![(445038937959 / 1000000000000), (108102761883 / 125000000000), (222495086273 / 500000000000), (1 / 1), (1 / 1)], ![(24060461482000000000000000000000000 / 2268354515301117859337443658970513439), (351137067593000000000000000000000000 / 2268354515301117859337443658970513439), (2457824938789000000000000000000000000 / 15878481607107825015362105612793594073), (168395161362000000000000000000000000 / 15878481607107825015362105612793594073), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1734819275173 / 1000000000000), (851698537861 / 1000000000000), (425821864369 / 500000000000), (-1734983249589 / 1000000000000), (0 / 1)], ![(-809593499613 / 1000000000000), (-2904629273 / 20000000000), (-809703081227 / 1000000000000), (0 / 1), (0 / 1)], ![(-2273120036833 / 500000000000), (-1865633311293 / 1000000000000), (-1865688046957 / 1000000000000), (-4546406745159 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-433704818793 / 250000000000), (425849268931 / 500000000000), (851643728739 / 1000000000000), (-433745812397 / 250000000000), (0 / 1)], ![(-202398374903 / 250000000000), (-145231463649 / 1000000000000), (-404851540613 / 500000000000), (0 / 1), (0 / 1)], ![(-909248014733 / 200000000000), (-466408327823 / 250000000000), (-466422011739 / 250000000000), (-2273203372579 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-51299243343 / 8000000000), (-1126592844383 / 250000000000), (-2206047889019 / 500000000000), (-1159294024683 / 1000000000000), (-1823354258223 / 1000000000000), (-56979819419 / 31250000000), (-1159293951497 / 1000000000000), (-4412096114237 / 1000000000000), (-450637365503 / 100000000000), (-6412408130739 / 1000000000000)] : List ℚ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-3206202708937 / 500000000000), (-4506371377531 / 1000000000000), (-4412095778037 / 1000000000000), (-579647012341 / 500000000000), (-911677129111 / 500000000000), (-1823354221407 / 1000000000000), (-144911743937 / 125000000000), (-1103024028559 / 250000000000), (-4506373655029 / 1000000000000), (-3206204065369 / 500000000000)] : List ℚ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 5 26 0 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (428 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((428 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
