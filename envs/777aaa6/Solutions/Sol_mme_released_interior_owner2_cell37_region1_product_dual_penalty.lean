-- Prove2me | solution 1 for mme_released_interior_owner2_cell37_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:43.345597+00:00
-- url     : https://prove2.me/submissions/dfa5bfd1-7c9b-416e-9314-0194388ff24f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 2 37 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157926800427 / 1000000000000), (1899676125459 / 500000000000), (237448629597 / 62500000000), (9870326179 / 62500000000)], ![(9774402860650000000000000000000000 / 125839586081356224712015664492026541), (17448887365900000000000000000000000 / 125839586081356224712015664492026541), (29320630282900000000000000000000000 / 377518758244068674136046993476079623), (1 / 1), (1 / 1)], ![(599418129991 / 1000000000000), (149847931403 / 250000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-115351477609 / 62500000000), (1334830591917 / 1000000000000), (1334784746903 / 1000000000000), (-922816828163 / 500000000000)], ![(-2555240953919 / 1000000000000), (-1975732084151 / 1000000000000), (-638832221173 / 250000000000), (0 / 1), (0 / 1)], ![(-511795877659 / 1000000000000), (-255919964323 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845623641743 / 1000000000000), (667415295959 / 500000000000), (166848093363 / 125000000000), (-73825346253 / 40000000000)], ![(-1277620476959 / 500000000000), (-39514641683 / 20000000000), (-2555328884691 / 1000000000000), (0 / 1), (0 / 1)], ![(-255897938829 / 500000000000), (-102367985729 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-108268508479 / 62500000000), (-2456335243921 / 500000000000), (-14409267761 / 12500000000), (-576371607453 / 500000000000), (-4912792455047 / 1000000000000), (-1732294170433 / 1000000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1732296135663 / 1000000000000), (-4912670487841 / 1000000000000), (-1152741420879 / 1000000000000), (-230548642981 / 200000000000), (-2456396227523 / 500000000000), (-27067096413 / 15625000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 2 37 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
