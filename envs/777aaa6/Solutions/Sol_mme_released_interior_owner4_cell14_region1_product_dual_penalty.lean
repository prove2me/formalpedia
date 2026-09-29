-- Prove2me | solution 1 for mme_released_interior_owner4_cell14_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:15:45.575378+00:00
-- url     : https://prove2.me/submissions/5d323284-d4ab-4828-b42d-e2871cd4af5b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 4 14 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(598454535403 / 1000000000000), (598454131921 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (3119899717740000000000000000000000 / 152101641224739521815910668306262239), (76651462970240000000000000000000000 / 152101641224739521815910668306262239), (76651421746400000000000000000000000 / 152101641224739521815910668306262239), (3119898482300000000000000000000000 / 152101641224739521815910668306262239)], ![(583154165683 / 1000000000000), (1050988478357 / 1000000000000), (583153256117 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-513404721109 / 1000000000000), (-128351348829 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-777349626017 / 200000000000), (-342640149067 / 500000000000), (-685280835943 / 1000000000000), (-485843565759 / 125000000000)], ![(-107860738491 / 200000000000), (49731129281 / 1000000000000), (-539305252191 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-128351180277 / 250000000000), (-102681079063 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-971687032521 / 250000000000), (-685280298133 / 1000000000000), (-342640417971 / 500000000000), (-3886748526071 / 1000000000000)], ![(-269651846227 / 500000000000), (24865564641 / 500000000000), (-53930525219 / 100000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4939458777639 / 1000000000000), (-1148954564167 / 1000000000000), (-868995135717 / 500000000000), (-13578046279 / 7812500000), (-1148954427769 / 1000000000000), (-2469728469839 / 500000000000)] : List ℚ).getD
    ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2469729388819 / 500000000000), (-574477282083 / 500000000000), (-1737990271433 / 1000000000000), (-1737989923711 / 1000000000000), (-143619303471 / 125000000000), (-4939456939677 / 1000000000000)] : List ℚ).getD
    ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 14 1 c : ℝ) / 1000000000000) ≤
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
