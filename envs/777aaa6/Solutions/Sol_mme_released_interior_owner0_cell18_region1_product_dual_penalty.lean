-- Prove2me | solution 1 for mme_released_interior_owner0_cell18_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:21.832328+00:00
-- url     : https://prove2.me/submissions/598af53d-0c4b-4a10-bca5-c990287f29e4

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(143332386425000000000000000000000000 / 1934822206483901601105349003028849683), (267162397202250000000000000000000000 / 1934822206483901601105349003028849683), (143332571583500000000000000000000000 / 1934822206483901601105349003028849683), (1 / 1), (1 / 1)], ![(592665563397 / 1000000000000), (592665966437 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (151022883503 / 1000000000000), (980924421157 / 250000000000), (392369842613 / 100000000000), (151026382009 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-650651101157 / 250000000000), (-1979914015563 / 1000000000000), (-2602603112817 / 1000000000000), (0 / 1), (0 / 1)], ![(-261562506557 / 500000000000), (-523124333067 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-236290488409 / 125000000000), (1367034496081 / 1000000000000), (683517342531 / 500000000000), (-1890300742137 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2602604404627 / 1000000000000), (-989957007781 / 500000000000), (-162662694551 / 62500000000), (0 / 1), (0 / 1)], ![(-65390626639 / 125000000000), (-261562166533 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1890323907271 / 1000000000000), (683517248041 / 500000000000), (1367034685063 / 1000000000000), (-236287592767 / 125000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5016030159851 / 1000000000000), (-1758694052633 / 1000000000000), (-1136004343613 / 1000000000000), (-22720077051 / 20000000000), (-1758693629849 / 1000000000000), (-78375802393 / 15625000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-100320603197 / 20000000000), (-219836756579 / 125000000000), (-284001085903 / 250000000000), (-1136003852549 / 1000000000000), (-219836703731 / 125000000000), (-5016051353151 / 1000000000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 0 18 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
