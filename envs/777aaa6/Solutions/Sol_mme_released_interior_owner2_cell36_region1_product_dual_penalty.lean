-- Prove2me | solution 1 for mme_released_interior_owner2_cell36_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:39.704651+00:00
-- url     : https://prove2.me/submissions/79abc403-f685-456a-abac-37ebedadf671

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 2 36 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157959455237 / 1000000000000), (379872079887 / 100000000000), (474840499307 / 125000000000), (78979753419 / 500000000000)], ![(9375912322890625000000000000000000 / 117957987760709955869856832477016201), (9375919908656250000000000000000000 / 117957987760709955869856832477016201), (1 / 1), (1 / 1), (1 / 1)], ![(14679342989 / 25000000000), (522177730747 / 500000000000), (587174672053 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-184541689131 / 100000000000), (667332189091 / 500000000000), (1334665219409 / 1000000000000), (-922708282319 / 500000000000)], ![(-2532184643581 / 1000000000000), (-2532183834511 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266217279101 / 500000000000), (10849977967 / 250000000000), (-532432936037 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845416891309 / 1000000000000), (1334664378183 / 1000000000000), (133466521941 / 100000000000), (-1845416564637 / 1000000000000)], ![(-126609232179 / 50000000000), (-253218383451 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-532434558201 / 1000000000000), (43399911869 / 1000000000000), (-133108234009 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-432488300359 / 250000000000), (-1154119512303 / 1000000000000), (-2455017883249 / 500000000000), (-1227508415461 / 250000000000), (-1154119544459 / 1000000000000), (-1729953173301 / 1000000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-864976600717 / 500000000000), (-577059756151 / 500000000000), (-4910035766497 / 1000000000000), (-4910033661843 / 1000000000000), (-577059772229 / 500000000000), (-17299531733 / 10000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 36 1 c : ℝ) / 1000000000000) ≤
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
