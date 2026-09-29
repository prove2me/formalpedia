-- Prove2me | solution 1 for mme_released_interior_owner2_cell13_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:17:02.812404+00:00
-- url     : https://prove2.me/submissions/c6dd8fa0-5e24-4cc7-bf14-4d237459f6fc

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 2 13 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(78294671049 / 200000000000), (391474197829 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(53073017459000000000000000000000000 / 17738773595887969431130241617743462719), (2004755282212000000000000000000000000 / 17738773595887969431130241617743462719), (13598355169402000000000000000000000000 / 17738773595887969431130241617743462719), (2004763359809000000000000000000000000 / 17738773595887969431130241617743462719), (53073009028000000000000000000000000 / 17738773595887969431130241617743462719)], ![(69154193229 / 250000000000), (17694499739 / 12500000000), (707781555599 / 500000000000), (276617782749 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-93783782399 / 100000000000), (-234458917913 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5811839468021 / 1000000000000), (-436046168561 / 200000000000), (-132902000177 / 500000000000), (-436045362719 / 200000000000), (-5811839626877 / 1000000000000)], ![(-1285122221981 / 1000000000000), (347525197769 / 1000000000000), (173763705187 / 500000000000), (-128511857133 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-937837823989 / 1000000000000), (-937835671651 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-290591973401 / 50000000000), (-545057710701 / 250000000000), (-265804000353 / 1000000000000), (-1090113406797 / 500000000000), (-1452959906719 / 250000000000)], ![(-64256111099 / 50000000000), (34752519777 / 100000000000), (2780219283 / 8000000000), (-1285118571329 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8034793712281 / 1000000000000), (-4403187238097 / 1000000000000), (-2770539104079 / 1000000000000), (-856114413967 / 1000000000000), (-214028618559 / 250000000000), (-2770539439823 / 1000000000000), (-4403184707269 / 1000000000000), (-4017399836167 / 500000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-200869842807 / 25000000000), (-275199202381 / 62500000000), (-1385269552039 / 500000000000), (-428057206983 / 500000000000), (-171222894847 / 200000000000), (-1385269719911 / 500000000000), (-1100796176817 / 250000000000), (-8034799672333 / 1000000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 13 4 c : ℝ) / 1000000000000) ≤
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
