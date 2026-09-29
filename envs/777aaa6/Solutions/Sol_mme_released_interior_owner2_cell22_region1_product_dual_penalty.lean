-- Prove2me | solution 1 for mme_released_interior_owner2_cell22_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:18.884921+00:00
-- url     : https://prove2.me/submissions/1ab20b09-47b4-4713-867d-5279d550ed1a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 2 22 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(36439283161 / 62500000000), (262803252343 / 250000000000), (58302779771 / 100000000000), (1 / 1), (1 / 1)], ![(1 / 1), (38985303614500000000000000000000000 / 1901682239408266720936365141734241173), (958368461911000000000000000000000000 / 1901682239408266720936365141734241173), (958367947667750000000000000000000000 / 1901682239408266720936365141734241173), (38985257802250000000000000000000000 / 1901682239408266720936365141734241173)], ![(119682904581 / 200000000000), (299207110949 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-269759578153 / 500000000000), (24972372203 / 500000000000), (-269760206653 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1943654708939 / 500000000000), (-685261842793 / 1000000000000), (-1096419807 / 1600000000), (-1943655296497 / 500000000000)], ![(-32091973941 / 62500000000), (-32092005379 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-107903831261 / 200000000000), (49944744407 / 1000000000000), (-107904082661 / 200000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3887309417877 / 1000000000000), (-85657730349 / 125000000000), (-342631189687 / 500000000000), (-3887310592993 / 1000000000000)], ![(-102694316611 / 200000000000), (-513472086063 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4940301917209 / 1000000000000), (-287197296113 / 250000000000), (-1738253839153 / 1000000000000), (-869126810873 / 500000000000), (-143598652253 / 125000000000), (-4940301332373 / 1000000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-617537739651 / 125000000000), (-1148789184451 / 1000000000000), (-108640864947 / 62500000000), (-347650724349 / 200000000000), (-1148789218023 / 1000000000000), (-1235075333093 / 250000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 2 22 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
