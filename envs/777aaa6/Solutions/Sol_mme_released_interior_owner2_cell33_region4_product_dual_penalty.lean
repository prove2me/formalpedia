-- Prove2me | solution 1 for mme_released_interior_owner2_cell33_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:54:07.562419+00:00
-- url     : https://prove2.me/submissions/924d7ad3-5ca8-49fe-8c9a-c69557973c58

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 2 33 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2670701209 / 50000000000), (1033404399359 / 500000000000), (6389317775269 / 500000000000), (206681344889 / 100000000000), (2670701481 / 50000000000)], ![(136346501239000000000000000000000000 / 8716489893916312902883149247943604633), (723916576850000000000000000000000000 / 8716489893916312902883149247943604633), (723917314968500000000000000000000000 / 8716489893916312902883149247943604633), (136347110770000000000000000000000000 / 8716489893916312902883149247943604633), (1 / 1)], ![(98728250619 / 250000000000), (78982683561 / 200000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![6, 4, 4, 6, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929681942403 / 1000000000000), (726005774591 / 1000000000000), (79617958713 / 31250000000), (726008024517 / 1000000000000), (-2929681840557 / 1000000000000)], ![(-4157772451947 / 1000000000000), (-1244147870181 / 500000000000), (-311036840093 / 125000000000), (-2078883990751 / 500000000000), (0 / 1)], ![(-232272446309 / 250000000000), (-929088733539 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1464840971201 / 500000000000), (2835960057 / 3906250000), (2547774678817 / 1000000000000), (363004012259 / 500000000000), (-732420460139 / 250000000000)], ![(-2078886225973 / 500000000000), (-2488295740361 / 1000000000000), (-2488294720743 / 1000000000000), (-4157767981501 / 1000000000000), (0 / 1)], ![(-185817957047 / 200000000000), (-464544366769 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-2180426580493 / 500000000000), (-8016544078131 / 1000000000000), (-217402448771 / 250000000000), (-672844375271 / 250000000000), (-2691377679687 / 1000000000000), (-869609827163 / 1000000000000), (-8016538656249 / 1000000000000), (-4360851992159 / 1000000000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-872170632197 / 200000000000), (-801654407813 / 100000000000), (-869609795083 / 1000000000000), (-2691377501083 / 1000000000000), (-1345688839843 / 500000000000), (-434804913581 / 500000000000), (-1002067332031 / 125000000000), (-2180425996079 / 500000000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 2 33 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
