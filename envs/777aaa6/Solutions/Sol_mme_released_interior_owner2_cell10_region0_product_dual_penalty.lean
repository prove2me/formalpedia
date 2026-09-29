-- Prove2me | solution 1 for mme_released_interior_owner2_cell10_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:14:32.44688+00:00
-- url     : https://prove2.me/submissions/3a6a33ba-3573-4bdc-83aa-74fc753f6e88

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 2 10 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(425409894781 / 500000000000), (850819516721 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(141489069976500000000000000000000000 / 628444670604141916190639996746097809), (424466224142000000000000000000000000 / 1885334011812425748571919990238293427), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (59854389031 / 100000000000), (502919431919 / 250000000000), (598541113699 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![3, 3, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161554935981 / 1000000000000), (-161555256661 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-298205103999 / 200000000000), (-1491027842409 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-256627711411 / 500000000000), (87371133037 / 125000000000), (-32078753861 / 62500000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-8077746799 / 50000000000), (-8077762833 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-745512759997 / 500000000000), (-186378480301 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-513255422821 / 1000000000000), (698969064297 / 1000000000000), (-20530402471 / 40000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2165840517749 / 1000000000000), (-476805856179 / 500000000000), (-190722742819 / 200000000000), (-1082919260947 / 500000000000)] : List ℚ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-541460129437 / 250000000000), (-953611712357 / 1000000000000), (-476806857047 / 500000000000), (-2165838521893 / 1000000000000)] : List ℚ).getD
    ((seed 2 10).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 2 10 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
