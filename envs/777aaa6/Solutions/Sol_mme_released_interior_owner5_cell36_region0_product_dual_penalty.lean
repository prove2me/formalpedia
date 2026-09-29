-- Prove2me | solution 1 for mme_released_interior_owner5_cell36_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:23:55.814276+00:00
-- url     : https://prove2.me/submissions/8eba0149-77d9-4e2b-95e7-83360a2a37c5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 5 36 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (31572554209 / 200000000000), (3800698348141 / 1000000000000), (380070175869 / 100000000000), (39466717453 / 250000000000)], ![(599306517929 / 1000000000000), (119861466027 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(293256169421000000000000000000000000 / 3775379088843229878982120770014760621), (523301551627000000000000000000000000 / 3775379088843229878982120770014760621), (293257097894500000000000000000000000 / 3775379088843229878982120770014760621), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1846029161043 / 1000000000000), (667592412837 / 500000000000), (1335185723021 / 1000000000000), (-923001598633 / 500000000000)], ![(-255991047837 / 500000000000), (-31998796277 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2555209552121 / 1000000000000), (-61753068721 / 31250000000), (-2555206386043 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-923014580521 / 500000000000), (53407393027 / 40000000000), (667592861511 / 500000000000), (-369200639453 / 200000000000)], ![(-511982095673 / 1000000000000), (-511980740431 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-63880238803 / 25000000000), (-1976098199071 / 1000000000000), (-1277603193021 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-614149355633 / 125000000000), (-216500571191 / 125000000000), (-1152894571723 / 1000000000000), (-144111764229 / 125000000000), (-346400731209 / 200000000000), (-4913216287477 / 1000000000000)] : List ℚ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4913194845063 / 1000000000000), (-1732004569527 / 1000000000000), (-576447285861 / 500000000000), (-1152894113831 / 1000000000000), (-433000914011 / 250000000000), (-1228304071869 / 250000000000)] : List ℚ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 36 0 c : ℝ) / 1000000000000) ≤
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
