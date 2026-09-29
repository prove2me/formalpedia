-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:17.172235+00:00
-- url     : https://prove2.me/submissions/817cd3b1-9139-468e-9265-6b05ae2f548f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(207674615951000000000000000000000000 / 9975497941234512510727742893895463211), (394245987819000000000000000000000000 / 9975497941234512510727742893895463211), (207689839011500000000000000000000000 / 9975497941234512510727742893895463211), (1 / 1), (1 / 1)], ![(19434628379 / 500000000000), (2309704454021 / 1000000000000), (8532960453791 / 500000000000), (461974966457 / 200000000000), (7773873261 / 200000000000)], ![(81232547263 / 200000000000), (103250478389 / 125000000000), (406192733199 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3871914650989 / 1000000000000), (-646182422077 / 200000000000), (-1935920675607 / 500000000000), (0 / 1), (0 / 1)], ![(-1623775827763 / 500000000000), (418559787183 / 500000000000), (2837083545601 / 1000000000000), (837193337907 / 1000000000000), (-50742950581 / 15625000000)], ![(-901001371329 / 1000000000000), (-38231174433 / 200000000000), (-225231879927 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-967978662747 / 250000000000), (-201932006899 / 62500000000), (-3871841351213 / 1000000000000), (0 / 1), (0 / 1)], ![(-129902066221 / 40000000000), (837119574367 / 1000000000000), (1418541772801 / 500000000000), (209298334477 / 250000000000), (-3247548837183 / 1000000000000)], ![(-14078146427 / 15625000000), (-47788968041 / 250000000000), (-900927519707 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1935758628957 / 1000000000000), (-3225877171219 / 1000000000000), (-4010232430093 / 500000000000), (-1647360020349 / 500000000000), (-584984436947 / 1000000000000), (-1647360079413 / 500000000000), (-501270032939 / 62500000000), (-1612938831513 / 500000000000), (-60492474159 / 31250000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-483939657239 / 250000000000), (-1612938585609 / 500000000000), (-1604092972037 / 200000000000), (-3294720040697 / 1000000000000), (-292492218473 / 500000000000), (-131788806353 / 40000000000), (-8020320527023 / 1000000000000), (-129035106521 / 40000000000), (-1935759173087 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 0 21 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
