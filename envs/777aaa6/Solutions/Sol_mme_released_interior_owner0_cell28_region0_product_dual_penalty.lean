-- Prove2me | solution 1 for mme_released_interior_owner0_cell28_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:59.35255+00:00
-- url     : https://prove2.me/submissions/d3c011de-a0a3-472d-92f8-d62ecb3bc141

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(34873998072875000000000000000000000 / 2210625143059156824228104601689910367), (175702628596250000000000000000000000 / 2210625143059156824228104601689910367), (175701102520875000000000000000000000 / 2210625143059156824228104601689910367), (34873149188625000000000000000000000 / 2210625143059156824228104601689910367), (1 / 1)], ![(1326694759 / 25000000000), (1002539826019 / 500000000000), (681594072463 / 50000000000), (501261270573 / 250000000000), (53067734319 / 1000000000000)], ![(98016427129 / 250000000000), (196031158913 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4149289114039 / 1000000000000), (-1266118834443 / 500000000000), (-1266123177241 / 500000000000), (-2074656727901 / 500000000000), (0 / 1)], ![(-2936185119339 / 1000000000000), (695683786671 / 1000000000000), (522482254709 / 200000000000), (695666545439 / 1000000000000), (-1468093087683 / 500000000000)], ![(-468162914737 / 500000000000), (-936334477781 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2074644557019 / 500000000000), (-506447533777 / 200000000000), (-2532246354481 / 1000000000000), (-4149313455801 / 1000000000000), (0 / 1)], ![(-1468092559669 / 500000000000), (43480236667 / 62500000000), (1306205636773 / 500000000000), (4347915909 / 6250000000), (-587237235073 / 200000000000)], ![(-936325829473 / 1000000000000), (-46816723889 / 50000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-1097489261597 / 250000000000), (-2005450279639 / 250000000000), (-5351005457 / 6250000000), (-1386448476461 / 500000000000), (-2772897045591 / 1000000000000), (-856160910409 / 1000000000000), (-4010916527077 / 500000000000), (-1097488874661 / 250000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4389957046387 / 1000000000000), (-1604360223711 / 200000000000), (-856160873119 / 1000000000000), (-2772896952921 / 1000000000000), (-277289704559 / 100000000000), (-107020113801 / 125000000000), (-8021833054153 / 1000000000000), (-4389955498643 / 1000000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 0 28 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
