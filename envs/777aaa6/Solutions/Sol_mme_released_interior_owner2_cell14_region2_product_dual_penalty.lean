-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:21.199848+00:00
-- url     : https://prove2.me/submissions/c551fb61-9643-47c4-9edb-471967c449fe

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 2 14 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11960093243 / 20000000000), (598005411001 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (10398806530600000000000000000000000 / 506776778081105410714564960293161953), (255578440149800000000000000000000000 / 506776778081105410714564960293161953), (255578693620400000000000000000000000 / 506776778081105410714564960293161953), (10398801093400000000000000000000000 / 506776778081105410714564960293161953)], ![(291660147841 / 500000000000), (525420927137 / 500000000000), (23332866169 / 40000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-20566269153 / 40000000000), (-16067358643 / 31250000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-485797447979 / 125000000000), (-684541257737 / 1000000000000), (-136908053197 / 200000000000), (-38863801067 / 10000000000)], ![(-269509425621 / 500000000000), (24795804451 / 500000000000), (-269508261131 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-64269591103 / 125000000000), (-20566219063 / 40000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3886379583831 / 1000000000000), (-85567657217 / 125000000000), (-1336992707 / 1953125000), (-3886380106699 / 1000000000000)], ![(-539018851241 / 1000000000000), (49591608903 / 1000000000000), (-539016522261 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-123488789569 / 25000000000), (-69508580353 / 40000000000), (-574552562703 / 500000000000), (-1149105385907 / 1000000000000), (-347542918761 / 200000000000), (-2469777843409 / 500000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4939551582759 / 1000000000000), (-217214313603 / 125000000000), (-229821025081 / 200000000000), (-574552692953 / 500000000000), (-434428648451 / 250000000000), (-4939555686817 / 1000000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 2 14 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
