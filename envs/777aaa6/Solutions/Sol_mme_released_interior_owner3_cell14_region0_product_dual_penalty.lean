-- Prove2me | solution 1 for mme_released_interior_owner3_cell14_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:35.308302+00:00
-- url     : https://prove2.me/submissions/a5e736d1-df02-4ae9-9206-2f5b22a8bbed

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(298797384731 / 500000000000), (119531573177 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (77563669587 / 500000000000), (153908716571 / 40000000000), (3848142436313 / 1000000000000), (155135526029 / 1000000000000)], ![(581563845192000000000000000000000000 / 7628046624027275541752961533274538733), (1053467868297000000000000000000000000 / 7628046624027275541752961533274538733), (581687117725000000000000000000000000 / 7628046624027275541752961533274538733), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-32177649861 / 62500000000), (-128684204847 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1863508956287 / 1000000000000), (269496044603 / 200000000000), (84224409237 / 62500000000), (-1863456182617 / 1000000000000)], ![(-102954652761 / 40000000000), (-19797443461 / 10000000000), (-2573654374161 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-20593695911 / 40000000000), (-514736819387 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-931754478143 / 500000000000), (168435027877 / 125000000000), (1347590547793 / 1000000000000), (-232932022827 / 125000000000)], ![(-160866644939 / 62500000000), (-1979744346099 / 1000000000000), (-32170679677 / 12500000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-123804122487 / 25000000000), (-1741012590623 / 1000000000000), (-1146996196079 / 1000000000000), (-143375117809 / 125000000000), (-1741016548923 / 1000000000000), (-2475950074933 / 500000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4952164899479 / 1000000000000), (-870506295311 / 500000000000), (-573498098039 / 500000000000), (-1147000942471 / 1000000000000), (-870508274461 / 500000000000), (-990380029973 / 200000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 14 0 c : ℝ) / 1000000000000) ≤
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
