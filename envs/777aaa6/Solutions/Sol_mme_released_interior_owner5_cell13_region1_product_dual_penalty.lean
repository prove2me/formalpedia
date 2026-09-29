-- Prove2me | solution 1 for mme_released_interior_owner5_cell13_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:20:35.460656+00:00
-- url     : https://prove2.me/submissions/25af2d50-7744-4f24-b0e1-c255644801d7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 5 13 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(98254168389 / 250000000000), (98253794399 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(13329724997 / 250000000000), (406750588191 / 200000000000), (13154731098433 / 1000000000000), (1016868431167 / 500000000000), (1332972207 / 25000000000)], ![(2011259851875000000000000000000000 / 129422367403033019138624160423007597), (179593004707625000000000000000000000 / 2200180245851561325356610727191129149), (179592326400875000000000000000000000 / 2200180245851561325356610727191129149), (34190957987875000000000000000000000 / 2200180245851561325356610727191129149), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-466951620831 / 500000000000), (-466953524011 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-732866103567 / 250000000000), (1135812521 / 1600000000), (2576781473267 / 1000000000000), (354937459853 / 500000000000), (-732866158463 / 250000000000)], ![(-4164319904171 / 1000000000000), (-2505601360103 / 1000000000000), (-2505605137021 / 1000000000000), (-416433334313 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-933903241661 / 1000000000000), (-933907048021 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2931464414267 / 1000000000000), (354941412813 / 500000000000), (644195368317 / 250000000000), (709874919707 / 1000000000000), (-2931464633851 / 1000000000000)], ![(-416431990417 / 100000000000), (-1252800680051 / 500000000000), (-125280256851 / 50000000000), (-4164333343129 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-4388352032449 / 1000000000000), (-2007421944579 / 250000000000), (-862726934859 / 1000000000000), (-545925936411 / 200000000000), (-2729629359417 / 1000000000000), (-107840863177 / 125000000000), (-8029704805951 / 1000000000000), (-2194176879589 / 500000000000)] : List ℚ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-68568000507 / 15625000000), (-1605937555663 / 200000000000), (-431363467429 / 500000000000), (-1364814841027 / 500000000000), (-341203669927 / 125000000000), (-172545381083 / 200000000000), (-160594096119 / 20000000000), (-4388353759177 / 1000000000000)] : List ℚ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 13 1 c : ℝ) / 1000000000000) ≤
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
