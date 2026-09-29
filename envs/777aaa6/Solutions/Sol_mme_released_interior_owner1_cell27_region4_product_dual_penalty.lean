-- Prove2me | solution 1 for mme_released_interior_owner1_cell27_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:33.473538+00:00
-- url     : https://prove2.me/submissions/2f961ff1-500b-4531-9acf-1ed817b9e7b8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(85571940743000000000000000000000000 / 8091443692732911404785765937018737289), (1196577919399000000000000000000000000 / 8091443692732911404785765937018737289), (1196676553220500000000000000000000000 / 8091443692732911404785765937018737289), (85593023101500000000000000000000000 / 8091443692732911404785765937018737289), (1 / 1)], ![(41225339957 / 250000000000), (310823595379 / 125000000000), (621698399393 / 250000000000), (164942215559 / 1000000000000), (1 / 1)], ![(222017136473 / 500000000000), (170059486041 / 200000000000), (27756715073 / 62500000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1137301253441 / 250000000000), (-955670710057 / 500000000000), (-238907374199 / 125000000000), (-2274479337057 / 500000000000), (0 / 1)], ![(-1802407803071 / 1000000000000), (910911796517 / 1000000000000), (227748542211 / 250000000000), (-1802160075153 / 1000000000000), (0 / 1)], ![(-81185352821 / 100000000000), (-162169072817 / 1000000000000), (-811688761211 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4549205013763 / 1000000000000), (-1911341420113 / 1000000000000), (-1911258993591 / 1000000000000), (-4548958674113 / 1000000000000), (0 / 1)], ![(-180240780307 / 100000000000), (455455898259 / 500000000000), (182198833769 / 200000000000), (-112635004697 / 62500000000), (0 / 1)], ![(-811853528209 / 1000000000000), (-10135567051 / 62500000000), (-81168876121 / 100000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1621290858577 / 250000000000), (-1113390184389 / 250000000000), (-2264651831949 / 500000000000), (-72665801987 / 62500000000), (-1811595792591 / 1000000000000), (-905797880377 / 500000000000), (-1162652777787 / 1000000000000), (-4529304194849 / 1000000000000), (-4453561535009 / 1000000000000), (-6485164822987 / 1000000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-6485163434307 / 1000000000000), (-890712147511 / 200000000000), (-4529303663897 / 1000000000000), (-1162652831791 / 1000000000000), (-181159579259 / 100000000000), (-1811595760753 / 1000000000000), (-581326388893 / 500000000000), (-141540756089 / 31250000000), (-139173797969 / 31250000000), (-3242582411493 / 500000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 27 4 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1592 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1592 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
