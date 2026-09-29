-- Prove2me | solution 1 for mme_released_interior_owner3_cell36_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:13:04.631928+00:00
-- url     : https://prove2.me/submissions/9d91bbe9-5fed-43cb-ad9e-c5188b46ca4e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 3 36 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (9870684029 / 62500000000), (949903612413 / 250000000000), (94967544489 / 25000000000), (157921821857 / 1000000000000)], ![(119920872337 / 200000000000), (74933375089 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(39109339839400000000000000000000000 / 503384118199788750215046612291158689), (9967931264400000000000000000000000 / 71912016885684107173578087470165527), (39091377642600000000000000000000000 / 503384118199788750215046612291158689), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845597401849 / 1000000000000), (667449800483 / 500000000000), (1334659371403 / 1000000000000), (-922827583391 / 500000000000)], ![(-63935654807 / 125000000000), (-255857175357 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1277496112049 / 500000000000), (-1976070317687 / 1000000000000), (-1277725805557 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-230699675231 / 125000000000), (1334899600967 / 1000000000000), (333664842851 / 250000000000), (-1845655166781 / 1000000000000)], ![(-102297047691 / 200000000000), (-511714350713 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2554992224097 / 1000000000000), (-988035158843 / 500000000000), (-2555451611113 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-346409440681 / 200000000000), (-614016578667 / 125000000000), (-576442533719 / 500000000000), (-1152896184737 / 1000000000000), (-1228190840913 / 250000000000), (-1732037248601 / 1000000000000)] : List ℚ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-433011800851 / 250000000000), (-982426525867 / 200000000000), (-1152885067437 / 1000000000000), (-36028005773 / 31250000000), (-4912763363651 / 1000000000000), (-8660186243 / 5000000000)] : List ℚ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 36 1 c : ℝ) / 1000000000000) ≤
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
