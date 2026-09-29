-- Prove2me | solution 1 for mme_released_interior_owner2_cell15_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:24.853227+00:00
-- url     : https://prove2.me/submissions/fdc71f32-0df8-494a-a21b-0c7cb8ff6350

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 2 15 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(170385055587 / 200000000000), (851925283693 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (603854214071000000000000000000000000 / 3745345801034140891309787091274612487), (1976378742188000000000000000000000000 / 3745345801034140891309787091274612487), (603853989506000000000000000000000000 / 3745345801034140891309787091274612487)], ![(85192530637 / 100000000000), (851925312429 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-80128228977 / 500000000000), (-32051290239 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-364987285409 / 200000000000), (-25569907893 / 40000000000), (-1824936798931 / 1000000000000)], ![(-1252003317 / 7812500000), (-20032052183 / 125000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-160256457953 / 1000000000000), (-80128225597 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-456234106761 / 250000000000), (-159811924331 / 250000000000), (-182493679893 / 100000000000)], ![(-6410256983 / 40000000000), (-160256417463 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 15) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 2 15).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-2145449295699 / 1000000000000), (-119970071593 / 125000000000), (-479880286547 / 500000000000), (-107272484073 / 50000000000)] : List ℚ).getD
    ((seed 2 15).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-1072724647849 / 500000000000), (-959760572743 / 1000000000000), (-959760573093 / 1000000000000), (-2145449681459 / 1000000000000)] : List ℚ).getD
    ((seed 2 15).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 15) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 15 =>
        (splitWeight 2 15 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 15, ∏ i, weights i (c.val i) ≤ 1 := by
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
