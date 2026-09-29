-- Prove2me | solution 1 for mme_released_interior_owner2_cell25_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:33.162174+00:00
-- url     : https://prove2.me/submissions/f66d6d03-826e-4c4c-8743-734c438fa8ef

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 2 25 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(138712709661 / 500000000000), (1409645717709 / 1000000000000), (176205300689 / 125000000000), (277420269009 / 1000000000000), (1 / 1)], ![(391000952476000000000000000000000000 / 17780886878694244069489632383041453011), (390999956221000000000000000000000000 / 17780886878694244069489632383041453011), (1 / 1), (1 / 1), (1 / 1)], ![(53258213441 / 1000000000000), (1985098243929 / 1000000000000), (3435960056793 / 250000000000), (1985085475717 / 1000000000000), (53258198087 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-641101570559 / 500000000000), (343338408781 / 1000000000000), (42917007389 / 125000000000), (-1282221705967 / 1000000000000), (0 / 1)], ![(-3817169392533 / 1000000000000), (-3817171940497 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-11455481419 / 3906250000), (685668406077 / 1000000000000), (2620590740259 / 1000000000000), (342830987013 / 500000000000), (-2932603531557 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1282203141117 / 1000000000000), (171669204391 / 500000000000), (343336059113 / 1000000000000), (-641110852983 / 500000000000), (0 / 1)], ![(-954292348133 / 250000000000), (-238573246281 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2932603243263 / 1000000000000), (342834203039 / 500000000000), (131029537013 / 50000000000), (685661974027 / 1000000000000), (-733150882889 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1606395212807 / 200000000000), (-2788169009731 / 1000000000000), (-853242593161 / 1000000000000), (-2206861346217 / 500000000000), (-4413713107601 / 1000000000000), (-26663837233 / 31250000000), (-1394083737653 / 500000000000), (-4015998444383 / 500000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4015988032017 / 500000000000), (-278816900973 / 100000000000), (-21331064829 / 25000000000), (-4413722692433 / 1000000000000), (-11034282769 / 2500000000), (-170648558291 / 200000000000), (-557633495061 / 200000000000), (-1606399377753 / 200000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 2 25 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
