-- Prove2me | solution 1 for mme_released_interior_owner4_cell27_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:18:18.537121+00:00
-- url     : https://prove2.me/submissions/4fcf3dcf-1597-493f-a4de-4bdbc9ade5f8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 4 27 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(44117393537 / 250000000000), (146547177743 / 62500000000), (46892536323 / 20000000000), (44110193171 / 250000000000), (1 / 1)], ![(351971085043750000000000000000000 / 33034349329671027734637548045200921), (15325571792143750000000000000000000 / 99103047989013083203912644135602763), (5108245285506250000000000000000000 / 33034349329671027734637548045200921), (351912956225000000000000000000000 / 33034349329671027734637548045200921), (1 / 1)], ![(445288370777 / 1000000000000), (86507219859 / 100000000000), (445239761431 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-17346068019 / 10000000000), (106522606531 / 125000000000), (852126248999 / 1000000000000), (-867385012227 / 500000000000), (0 / 1)], ![(-141929817513 / 31250000000), (-233329675671 / 125000000000), (-933345976003 / 500000000000), (-4541919326311 / 1000000000000), (0 / 1)], ![(-32361327299 / 40000000000), (-36235577239 / 250000000000), (-809142352179 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1734606801899 / 1000000000000), (852180852249 / 1000000000000), (852126249 / 1000000000), (-1734770024453 / 1000000000000), (0 / 1)], ![(-908350832083 / 200000000000), (-1866637405367 / 1000000000000), (-373338390401 / 200000000000), (-454191932631 / 100000000000), (0 / 1)], ![(-404516591237 / 500000000000), (-28988461791 / 200000000000), (-404571176089 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-6407268746089 / 1000000000000), (-281303946413 / 62500000000), (-4412356387693 / 1000000000000), (-1159527606247 / 1000000000000), (-1823310870783 / 1000000000000), (-911655425487 / 500000000000), (-1159527549799 / 1000000000000), (-551544609763 / 125000000000), (-2250432266837 / 500000000000), (-1601817673633 / 250000000000)] : List ℚ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-800908593261 / 125000000000), (-4500863142607 / 1000000000000), (-1103089096923 / 250000000000), (-579763803123 / 500000000000), (-911655435391 / 500000000000), (-1823310850973 / 1000000000000), (-579763774899 / 500000000000), (-4412356878103 / 1000000000000), (-4500864533673 / 1000000000000), (-6407270694531 / 1000000000000)] : List ℚ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 4 27 0 c : ℝ) / 1000000000000) ≤
          (440 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (440 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((440 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
