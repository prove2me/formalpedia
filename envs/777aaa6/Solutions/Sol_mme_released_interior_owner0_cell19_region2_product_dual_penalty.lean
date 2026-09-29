-- Prove2me | solution 1 for mme_released_interior_owner0_cell19_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:25.241723+00:00
-- url     : https://prove2.me/submissions/56574f75-4ec1-44b5-a313-bf48a32ec88e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2050612069810000000000000000000000 / 101302518008444118413963378846718837), (1328409040000000000000000000000000 / 33767506002814706137987792948906279), (2050617215230000000000000000000000 / 101302518008444118413963378846718837), (1 / 1), (1 / 1)], ![(102212666461 / 250000000000), (802870406771 / 1000000000000), (25553230733 / 62500000000), (1 / 1), (1 / 1)], ![(4840395481 / 125000000000), (1128417051121 / 500000000000), (4432148555407 / 250000000000), (1128419877961 / 500000000000), (7744633197 / 200000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-487496618583 / 125000000000), (-1617758481773 / 500000000000), (-121874076233 / 31250000000), (0 / 1), (0 / 1)], ![(-447202654899 / 500000000000), (-109780982199 / 500000000000), (-894402800611 / 1000000000000), (0 / 1), (0 / 1)], ![(-1625658654481 / 500000000000), (32558519659 / 40000000000), (1437589414411 / 500000000000), (813965496609 / 1000000000000), (-130052690151 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3899972948663 / 1000000000000), (-647103392709 / 200000000000), (-779994087891 / 200000000000), (0 / 1), (0 / 1)], ![(-894405309797 / 1000000000000), (-219561964397 / 1000000000000), (-89440280061 / 100000000000), (0 / 1), (0 / 1)], ![(-3251317308961 / 1000000000000), (203490747869 / 250000000000), (2875178828823 / 1000000000000), (81396549661 / 100000000000), (-1625658626887 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8045695513193 / 1000000000000), (-3305569416503 / 1000000000000), (-1919196920439 / 1000000000000), (-663191355337 / 200000000000), (-7248751239 / 12500000000), (-1657978386359 / 500000000000), (-959598460223 / 500000000000), (-826392353083 / 250000000000), (-8045690548753 / 1000000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1005711939149 / 125000000000), (-1652784708251 / 500000000000), (-959598460219 / 500000000000), (-828989194171 / 250000000000), (-579900099119 / 1000000000000), (-3315956772717 / 1000000000000), (-383839384089 / 200000000000), (-330556941233 / 100000000000), (-502855659297 / 62500000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 0 19 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
