-- Prove2me | solution 1 for mme_released_interior_owner1_cell11_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:28.404224+00:00
-- url     : https://prove2.me/submissions/31e56bc4-97ef-4554-bd55-30a67ca3bb4a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(592233373095000000000000000000000000 / 7750374403467004427346579731595559657), (592232150438000000000000000000000000 / 7750374403467004427346579731595559657), (1 / 1), (1 / 1), (1 / 1)], ![(143515826953 / 250000000000), (532155623707 / 500000000000), (574060952163 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (150224020817 / 1000000000000), (3941177726503 / 1000000000000), (1970584635879 / 500000000000), (150223891853 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1285797831397 / 500000000000), (-2571597727281 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-555015596389 / 1000000000000), (62327873907 / 1000000000000), (-555019699863 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1895627626893 / 1000000000000), (1371479593999 / 1000000000000), (342869362191 / 250000000000), (-473907121343 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2571595662793 / 1000000000000), (-32144971591 / 12500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-138753899097 / 250000000000), (15581968477 / 250000000000), (-277509849931 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-473906906723 / 250000000000), (685739797 / 500000000), (274295489753 / 200000000000), (-1895628485371 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1755135768659 / 1000000000000), (-1137790340123 / 1000000000000), (-5022239744537 / 1000000000000), (-627780631751 / 125000000000), (-568895129687 / 500000000000), (-1755135874903 / 1000000000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-877567884329 / 500000000000), (-568895170061 / 500000000000), (-627779968067 / 125000000000), (-5022245054007 / 1000000000000), (-1137790259373 / 1000000000000), (-877567937451 / 500000000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 1 11 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
