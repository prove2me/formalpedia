-- Prove2me | solution 1 for mme_released_interior_owner1_cell13_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:33.876403+00:00
-- url     : https://prove2.me/submissions/bfc193b7-f702-4389-a9c0-8c508f5ea764

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(9786839976800000000000000000000000 / 443465515831772085566615934363883887), (9786857539100000000000000000000000 / 443465515831772085566615934363883887), (1 / 1), (1 / 1), (1 / 1)], ![(53070718247 / 1000000000000), (1002381334371 / 500000000000), (2719726323703 / 200000000000), (2004770526587 / 1000000000000), (53070745231 / 1000000000000)], ![(11065030869 / 40000000000), (1415520050059 / 1000000000000), (22117539247 / 15625000000), (27662804751 / 100000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1906790710199 / 500000000000), (-1906789812959 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2936129948279 / 1000000000000), (695525684047 / 1000000000000), (1304984585697 / 500000000000), (173882400907 / 250000000000), (-1468064719913 / 500000000000)], ![(-321272422707 / 250000000000), (347496990117 / 1000000000000), (86874682307 / 250000000000), (-1285081463917 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3813581420397 / 1000000000000), (-3813579625917 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1468064974139 / 500000000000), (43470355253 / 62500000000), (521993834279 / 200000000000), (695529603629 / 1000000000000), (-117445177593 / 40000000000)], ![(-1285089690827 / 1000000000000), (173748495059 / 500000000000), (347498729229 / 1000000000000), (-321270365979 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8034800551993 / 1000000000000), (-2770554826649 / 1000000000000), (-26753547493 / 31250000000), (-34399509377 / 7812500000), (-34399529009 / 7812500000), (-856113464403 / 1000000000000), (-2770555212647 / 1000000000000), (-4017395519687 / 500000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-1004350068999 / 125000000000), (-346319353331 / 125000000000), (-34244540791 / 40000000000), (-880627440051 / 200000000000), (-4403139713151 / 1000000000000), (-428056732201 / 500000000000), (-1385277606323 / 500000000000), (-8034791039373 / 1000000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 1 13 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
