-- Prove2me | solution 1 for mme_released_interior_owner1_cell37_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:59.442503+00:00
-- url     : https://prove2.me/submissions/23d32aee-f71d-449d-ab5f-2e47519d73d8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (31507020935800000000000000000000000 / 1512073314150682585476645423503436923), (761257057762600000000000000000000000 / 1512073314150682585476645423503436923), (761257700801600000000000000000000000 / 1512073314150682585476645423503436923), (31507018509800000000000000000000000 / 1512073314150682585476645423503436923)], ![(58637430943 / 100000000000), (522809992157 / 500000000000), (117275061603 / 200000000000), (1 / 1), (1 / 1)], ![(599627642399 / 1000000000000), (74953522807 / 125000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3871026635913 / 1000000000000), (-686265953497 / 1000000000000), (-686265108791 / 1000000000000), (-3871026712911 / 1000000000000)], ![(-133449235007 / 250000000000), (11152498979 / 250000000000), (-533795237047 / 1000000000000), (0 / 1), (0 / 1)], ![(-255723206209 / 500000000000), (-127861377941 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-483878329489 / 125000000000), (-85783244187 / 125000000000), (-68626510879 / 100000000000), (-387102671291 / 100000000000)], ![(-533796940027 / 1000000000000), (44609995917 / 1000000000000), (-266897618523 / 500000000000), (0 / 1), (0 / 1)], ![(-511446412417 / 1000000000000), (-511445511763 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4916267384681 / 1000000000000), (-865753801481 / 500000000000), (-36034420917 / 31250000000), (-1153101525291 / 1000000000000), (-865753780291 / 500000000000), (-4916270065391 / 1000000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-122906684617 / 25000000000), (-1731507602961 / 1000000000000), (-1153101469343 / 1000000000000), (-115310152529 / 100000000000), (-1731507560581 / 1000000000000), (-491627006539 / 100000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 1 37 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
