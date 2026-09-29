-- Prove2me | solution 1 for mme_released_interior_owner2_cell20_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:13.865081+00:00
-- url     : https://prove2.me/submissions/75ce5708-9421-47cd-8def-8c4255b684e9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 2 20 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(17784346647 / 40000000000), (864121879227 / 1000000000000), (222339533029 / 500000000000), (1 / 1), (1 / 1)], ![(175512797467000000000000000000000000 / 15913031617409424612584423788441949849), (2352358920805000000000000000000000000 / 15913031617409424612584423788441949849), (2352545246141000000000000000000000000 / 15913031617409424612584423788441949849), (175554296629000000000000000000000000 / 15913031617409424612584423788441949849), (1 / 1)], ![(33670613621 / 200000000000), (2456413734877 / 1000000000000), (2456608178893 / 1000000000000), (168393097733 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-810560785571 / 1000000000000), (-146041456207 / 1000000000000), (-202600614219 / 250000000000), (0 / 1), (0 / 1)], ![(-4507181690813 / 1000000000000), (-1911719751341 / 1000000000000), (-191164054661 / 100000000000), (-2253472636771 / 500000000000), (0 / 1)], ![(-89084595449 / 50000000000), (898702454923 / 1000000000000), (1755432831 / 1953125000), (-445363541337 / 250000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-81056078557 / 100000000000), (-73020728103 / 500000000000), (-1296643931 / 1600000000), (0 / 1), (0 / 1)], ![(-1126795422703 / 250000000000), (-95585987567 / 50000000000), (-1911640546609 / 1000000000000), (-4506945273541 / 1000000000000), (0 / 1)], ![(-1781691908979 / 1000000000000), (224675613731 / 250000000000), (898781609473 / 1000000000000), (-1781454165347 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6420920817431 / 1000000000000), (-1105162330507 / 250000000000), (-1126436338927 / 250000000000), (-289762610667 / 250000000000), (-911572220829 / 500000000000), (-911572205543 / 500000000000), (-231810078519 / 200000000000), (-2252872781563 / 500000000000), (-4420650387183 / 1000000000000), (-802615268343 / 125000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-642092081743 / 100000000000), (-4420649322027 / 1000000000000), (-4505745355707 / 1000000000000), (-1159050442667 / 1000000000000), (-1823144441657 / 1000000000000), (-364628882217 / 200000000000), (-579525196297 / 500000000000), (-7209192901 / 1600000000), (-2210325193591 / 500000000000), (-6420922146743 / 1000000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 20 5 c : ℝ) / 1000000000000) ≤
          (407 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (407 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((407 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
