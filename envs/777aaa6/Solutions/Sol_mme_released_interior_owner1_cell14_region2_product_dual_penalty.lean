-- Prove2me | solution 1 for mme_released_interior_owner1_cell14_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:36.095687+00:00
-- url     : https://prove2.me/submissions/8ddb609c-c5a5-4b8d-958e-d2c83d5be62d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(33175844659000000000000000000000000 / 423477602108480341310094411162821167), (99527344202500000000000000000000000 / 1270432806325441023930283233488463501), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (77607559451 / 500000000000), (153886734969 / 40000000000), (480895074467 / 125000000000), (38803788867 / 250000000000)], ![(581751154797 / 1000000000000), (526873743761 / 500000000000), (581748918459 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-636669646127 / 250000000000), (-9947970669 / 3906250000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-465735815093 / 250000000000), (1347337390481 / 1000000000000), (673667684303 / 500000000000), (-186294302479 / 100000000000)], ![(-270856245881 / 500000000000), (5235284601 / 100000000000), (-270858167959 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2546678584507 / 1000000000000), (-2546680491263 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1862943260371 / 1000000000000), (673668695241 / 500000000000), (1347335368607 / 1000000000000), (-1862943024789 / 1000000000000)], ![(-541712491761 / 1000000000000), (52352846011 / 1000000000000), (-541716335917 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1237833525283 / 250000000000), (-1146990369893 / 1000000000000), (-870528764973 / 500000000000), (-1741057614419 / 1000000000000), (-1146990254767 / 1000000000000), (-618917510951 / 125000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4951334101131 / 1000000000000), (-286747592473 / 250000000000), (-348211505989 / 200000000000), (-870528807209 / 500000000000), (-573495127383 / 500000000000), (-4951340087607 / 1000000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 14 2 c : ℝ) / 1000000000000) ≤
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
