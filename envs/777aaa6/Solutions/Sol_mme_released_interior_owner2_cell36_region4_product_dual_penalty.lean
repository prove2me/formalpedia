-- Prove2me | solution 1 for mme_released_interior_owner2_cell36_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:41.169996+00:00
-- url     : https://prove2.me/submissions/225d8a34-e0da-47ff-a695-18cdf6135c3f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 2 36 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157940519459 / 1000000000000), (3798255663279 / 1000000000000), (75965194759 / 20000000000), (157940558311 / 1000000000000)], ![(19996947336700000000000000000000000 / 251765251693877520248679479974263409), (19996967954700000000000000000000000 / 251765251693877520248679479974263409), (1 / 1), (1 / 1), (1 / 1)], ![(586435204999 / 1000000000000), (1046541038007 / 1000000000000), (293218210323 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-922768387977 / 500000000000), (1334541925363 / 1000000000000), (1334542998137 / 1000000000000), (-1845536529963 / 1000000000000)], ![(-2532917483721 / 1000000000000), (-506583290533 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266846547201 / 500000000000), (22745238333 / 500000000000), (-533691021461 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845536775953 / 1000000000000), (333635481341 / 250000000000), (667271499069 / 500000000000), (-922768264981 / 500000000000)], ![(-63322937093 / 25000000000), (-316614556583 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533693094401 / 1000000000000), (45490476667 / 1000000000000), (-26684551073 / 50000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1732066579821 / 1000000000000), (-576442004459 / 500000000000), (-4912147108053 / 1000000000000), (-4912144250109 / 1000000000000), (-576442025317 / 500000000000), (-69282661957 / 40000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-86603328991 / 50000000000), (-1152884008917 / 1000000000000), (-1228036777013 / 250000000000), (-1228036062527 / 250000000000), (-1152884050633 / 1000000000000), (-433016637231 / 250000000000)] : List ℚ).getD
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
        (splitWeight 2 36 4 c : ℝ) / 1000000000000) ≤
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
