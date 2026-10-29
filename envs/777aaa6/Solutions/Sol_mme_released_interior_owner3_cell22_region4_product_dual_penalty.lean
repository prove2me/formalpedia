-- Prove2me | solution 1 for mme_released_interior_owner3_cell22_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:14:10.053191+00:00
-- url     : https://prove2.me/submissions/385ff6b3-16a1-44b1-97d2-a35490b55368

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 3 22 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11929692593492580703074065073 / 25000000000000000000000000000), (43025993695247669740063047519 / 50000000000000000000000000000), (11929688778611180703112213887 / 25000000000000000000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (1362345658699286376543413007 / 50000000000000000000000000000), (66947270248785230527297512141 / 100000000000000000000000000000), (33473616840458565263831595411 / 50000000000000000000000000000), (2724689256967872753107430321 / 100000000000000000000000000000)], ![(55032113568757349678864312421 / 100000000000000000000000000000), (55032128061060749678719389387 / 100000000000000000000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 5, 1, 1, 5], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-739845356609847 / 1000000000000000), (-15021856783321 / 100000000000000), (-739845676390259 / 1000000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1801407521154099 / 500000000000000), (-80252977533039 / 200000000000000), (-401265433884301 / 1000000000000000), (-225175987407219 / 62500000000000)], ![(-597253288080701 / 1000000000000000), (-74656628092259 / 125000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-147969071321969 / 200000000000000), (-150218567833209 / 1000000000000000), (-739845676390257 / 1000000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3602815042308193 / 1000000000000000), (-401264887665193 / 1000000000000000), (-401265433884299 / 1000000000000000), (-1801407899257749 / 500000000000000)], ![(-597253288080699 / 1000000000000000), (-59725302473807 / 100000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([7, 2, 3, 3, 2, 7] : List ℤ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4939914443206021 / 1000000000000000), (-1148737289798181 / 1000000000000000), (-434590963034031 / 250000000000000), (-1738363815232191 / 1000000000000000), (-574368240118223 / 500000000000000), (-4939913743436499 / 1000000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-2469957221603007 / 500000000000000), (-1148737289798179 / 1000000000000000), (-1738363852136121 / 1000000000000000), (-1738363815232187 / 1000000000000000), (-287184120059111 / 250000000000000), (-1234978435859123 / 250000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 3 22 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
