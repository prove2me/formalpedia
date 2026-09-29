-- Prove2me | solution 1 for mme_released_interior_owner2_cell40_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:46.433201+00:00
-- url     : https://prove2.me/submissions/34070636-f6d3-4db1-9878-9a22a81087de

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 2 40 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1 / 1), (121851032701 / 200000000000), (979567900471 / 500000000000), (304672350393 / 500000000000)], ![(426454140824000000000000000000000000 / 1868403090723501056156962872722101313), (426459210851000000000000000000000000 / 1868403090723501056156962872722101313), (1 / 1), (1 / 1), (1 / 1)], ![(852894233861 / 1000000000000), (852901234869 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 0, 1, 0, 1], ![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-495518111331 / 1000000000000), (336251729061 / 500000000000), (-247685580127 / 500000000000)], ![(-1477334546131 / 1000000000000), (-369330664351 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-39779933077 / 250000000000), (-159111523811 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-49551811133 / 100000000000), (672503458123 / 1000000000000), (-495371160253 / 1000000000000)], ![(-147733454613 / 100000000000), (-1477322657403 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-159119732307 / 1000000000000), (-15911152381 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 40) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-963942611819 / 1000000000000), (-1065912719347 / 500000000000), (-2131952292547 / 1000000000000), (-481969465793 / 500000000000)] : List ℚ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-481971305909 / 500000000000), (-2131825438693 / 1000000000000), (-1065976146273 / 500000000000), (-192787786317 / 200000000000)] : List ℚ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 40) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 40 =>
        (splitWeight 2 40 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 40, ∏ i, weights i (c.val i) ≤ 1 := by
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
