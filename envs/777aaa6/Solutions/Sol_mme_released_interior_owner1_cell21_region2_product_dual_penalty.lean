-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:53.452175+00:00
-- url     : https://prove2.me/submissions/20ac30b2-a1ca-45fb-880a-9429a6d70e51

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(51552091493125000000000000000000000 / 2479773261744927763529717598607615503), (100617061636625000000000000000000000 / 2479773261744927763529717598607615503), (17184045693750000000000000000000000 / 826591087248309254509905866202538501), (1 / 1), (1 / 1)], ![(4873968413 / 125000000000), (578201038751 / 250000000000), (8448247902419 / 500000000000), (2312806209707 / 1000000000000), (7798349701 / 200000000000)], ![(102841542987 / 250000000000), (12654701891 / 15625000000), (4113665273 / 10000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1936664813249 / 500000000000), (-640920113241 / 200000000000), (-1936664371093 / 500000000000), (0 / 1), (0 / 1)], ![(-648881052567 / 200000000000), (838460708243 / 1000000000000), (2827106251603 / 1000000000000), (419230798323 / 500000000000), (-3244405232033 / 1000000000000)], ![(-444135765907 / 500000000000), (-210843358521 / 1000000000000), (-888270667981 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3873329626497 / 1000000000000), (-801150141551 / 250000000000), (-774665748437 / 200000000000), (0 / 1), (0 / 1)], ![(-1622202631417 / 500000000000), (209615177061 / 250000000000), (706776562901 / 250000000000), (838461596647 / 1000000000000), (-101387663501 / 31250000000)], ![(-888271531813 / 1000000000000), (-5271083963 / 25000000000), (-44413533399 / 50000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8006006391883 / 1000000000000), (-3245711398513 / 1000000000000), (-120905877509 / 62500000000), (-3254410491143 / 1000000000000), (-294168836561 / 500000000000), (-650882107233 / 200000000000), (-967247012563 / 500000000000), (-1622855691167 / 500000000000), (-1601200934701 / 200000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4003003195941 / 500000000000), (-202856962407 / 62500000000), (-1934494040143 / 1000000000000), (-1627205245571 / 500000000000), (-588337673121 / 1000000000000), (-813602634041 / 250000000000), (-15475952201 / 8000000000), (-3245711382333 / 1000000000000), (-250187646047 / 31250000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 21 2 c : ℝ) / 1000000000000) ≤
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
