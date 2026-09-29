-- Prove2me | solution 1 for mme_released_interior_owner3_cell37_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:13:05.393438+00:00
-- url     : https://prove2.me/submissions/f54b0a0b-713e-4d27-9d64-f1fe508981ad

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 3 37 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78978673029 / 500000000000), (949667203421 / 250000000000), (3798671970301 / 1000000000000), (39489349143 / 250000000000)], ![(587083435623 / 1000000000000), (208924028149 / 200000000000), (58708437579 / 100000000000), (1 / 1), (1 / 1)], ![(23078541597000000000000000000000000 / 290376176285176059800919072195080869), (23078560024000000000000000000000000 / 290376176285176059800919072195080869), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-92271512203 / 50000000000), (133465069317 / 100000000000), (1334651524149 / 1000000000000), (-369085984853 / 200000000000)], ![(-133147082551 / 250000000000), (21826658827 / 500000000000), (-266293364393 / 500000000000), (0 / 1), (0 / 1)], ![(-506454798279 / 200000000000), (-633068298237 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845430244059 / 1000000000000), (1334650693171 / 1000000000000), (26693030483 / 20000000000), (-230678740533 / 125000000000)], ![(-532588330203 / 1000000000000), (8730663531 / 200000000000), (-106517345757 / 200000000000), (0 / 1), (0 / 1)], ![(-1266136995697 / 500000000000), (-2532273192947 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-432552506753 / 250000000000), (-144246143699 / 125000000000), (-2455146122929 / 500000000000), (-1227572541441 / 250000000000), (-288492295531 / 250000000000), (-1730209999 / 1000000000)] : List ℚ).getD
    ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1730210027011 / 1000000000000), (-1153969149591 / 1000000000000), (-4910292245857 / 1000000000000), (-4910290165763 / 1000000000000), (-1153969182123 / 1000000000000), (-1730209998999 / 1000000000000)] : List ℚ).getD
    ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 37 1 c : ℝ) / 1000000000000) ≤
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
