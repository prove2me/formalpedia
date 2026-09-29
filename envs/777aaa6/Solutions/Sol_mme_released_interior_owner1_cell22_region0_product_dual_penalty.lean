-- Prove2me | solution 1 for mme_released_interior_owner1_cell22_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:56.427137+00:00
-- url     : https://prove2.me/submissions/319c8d14-e93f-4faf-ba30-704c82457b2d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(290741110340500000000000000000000000 / 3814536739453053742776260104225927091), (526921380893000000000000000000000000 / 3814536739453053742776260104225927091), (290741542553500000000000000000000000 / 3814536739453053742776260104225927091), (1 / 1), (1 / 1)], ![(1 / 1), (155150725513 / 1000000000000), (3847149368201 / 1000000000000), (3847150595013 / 1000000000000), (155154391099 / 1000000000000)], ![(597743312893 / 1000000000000), (597743792083 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2574141289003 / 1000000000000), (-1979523149963 / 1000000000000), (-1287069901207 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-232919776487 / 125000000000), (673666225103 / 500000000000), (269466553819 / 200000000000), (-1863334586207 / 1000000000000)], ![(-514593859837 / 1000000000000), (-128648264543 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1287070644501 / 500000000000), (-989761574981 / 500000000000), (-2574139802413 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-372671642379 / 200000000000), (1347332450207 / 1000000000000), (168416596137 / 125000000000), (-931667293103 / 500000000000)], ![(-128648464959 / 250000000000), (-514593058171 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-198082789401 / 40000000000), (-1741401578077 / 1000000000000), (-1146784240703 / 1000000000000), (-114678375793 / 100000000000), (-870700606023 / 500000000000), (-4952091072507 / 1000000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-309504358439 / 62500000000), (-435350394519 / 250000000000), (-573392120351 / 500000000000), (-1146783757929 / 1000000000000), (-348280242409 / 200000000000), (-2476045536253 / 500000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 1 22 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
