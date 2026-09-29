-- Prove2me | solution 1 for mme_released_interior_owner1_cell14_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:36.714551+00:00
-- url     : https://prove2.me/submissions/f4d8bec1-af6c-47c8-88a0-f6eb95630312

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(198933927130000000000000000000000000 / 2543959830879556018257191938469826991), (596800845899000000000000000000000000 / 7631879492638668054771575815409480973), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (77424330899 / 500000000000), (1927019269069 / 500000000000), (3854032374237 / 1000000000000), (77424111541 / 500000000000)], ![(581194338309 / 1000000000000), (13181150901 / 12500000000), (581192533533 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2548504389467 / 1000000000000), (-159281622311 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-74612280581 / 40000000000), (1349121569459 / 1000000000000), (674559985061 / 500000000000), (-1865309847721 / 1000000000000)], ![(-135667522179 / 250000000000), (53059202729 / 1000000000000), (-542673194009 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1274252194733 / 500000000000), (-101940238279 / 40000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-466326753631 / 250000000000), (67456078473 / 50000000000), (1349119970123 / 1000000000000), (-46632746193 / 25000000000)], ![(-108534017743 / 200000000000), (5305920273 / 100000000000), (-67834149251 / 125000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4956484325891 / 1000000000000), (-143290652077 / 125000000000), (-1742056014019 / 1000000000000), (-1742056075569 / 1000000000000), (-229265036957 / 200000000000), (-619560770697 / 125000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-495648432589 / 100000000000), (-229265043323 / 200000000000), (-871028007009 / 500000000000), (-108878504723 / 62500000000), (-71645324049 / 62500000000), (-198259446623 / 40000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 1 14 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
