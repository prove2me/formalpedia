-- Prove2me | solution 1 for mme_released_interior_owner2_cell11_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:54.606882+00:00
-- url     : https://prove2.me/submissions/e9406f2a-464c-4d08-8e9a-38aa9d884dfb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 2 11 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(592162536463 / 1000000000000), (118432724799 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(574040268220000000000000000000000000 / 7752231910029512039103544204123381953), (118236189165000000000000000000000000 / 861359101114390226567060467124820217), (574042285328000000000000000000000000 / 7752231910029512039103544204123381953), (1 / 1), (1 / 1)], ![(1 / 1), (150131018089 / 1000000000000), (1971564392291 / 500000000000), (157725358257 / 40000000000), (18766811333 / 125000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-261987063473 / 500000000000), (-130993072601 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301518260863 / 500000000000), (-1985827264921 / 1000000000000), (-2603033007853 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1896246912199 / 1000000000000), (274394903187 / 200000000000), (1371975827543 / 1000000000000), (-1896223782169 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-104794825389 / 200000000000), (-523972290403 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-104121460869 / 40000000000), (-49645681623 / 25000000000), (-650758251963 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-948123456099 / 500000000000), (42874203623 / 31250000000), (171496978443 / 125000000000), (-237027972771 / 125000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-125580860771 / 25000000000), (-877516492293 / 500000000000), (-284456391081 / 250000000000), (-284456259847 / 250000000000), (-109689538679 / 62500000000), (-5023252210499 / 1000000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5023234430839 / 1000000000000), (-351006596917 / 200000000000), (-1137825564323 / 1000000000000), (-1137825039387 / 1000000000000), (-1755032618863 / 1000000000000), (-2511626105249 / 500000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 2 11 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
