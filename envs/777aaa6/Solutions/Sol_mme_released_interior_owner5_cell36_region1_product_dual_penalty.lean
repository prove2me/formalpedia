-- Prove2me | solution 1 for mme_released_interior_owner5_cell36_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:23:43.579465+00:00
-- url     : https://prove2.me/submissions/e8278ff7-d59b-4749-b0a1-9571c6a762bc

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 5 36 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (15704152209 / 100000000000), (190684655113 / 50000000000), (762738746201 / 200000000000), (15704639729 / 100000000000)], ![(598906287291 / 1000000000000), (74863343431 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(23373668277240000000000000000000000 / 303134082800380531060932488785197169), (42022823587720000000000000000000000 / 303134082800380531060932488785197169), (23373713550520000000000000000000000 / 303134082800380531060932488785197169), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-185124503669 / 100000000000), (1338598037831 / 1000000000000), (167324775337 / 125000000000), (-1851213993153 / 1000000000000)], ![(-512650141703 / 1000000000000), (-256324686687 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1281282561833 / 500000000000), (-1975962335681 / 1000000000000), (-2562563186733 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1851245036689 / 1000000000000), (167324754729 / 125000000000), (1338598202697 / 1000000000000), (-28925218643 / 15625000000)], ![(-256325070851 / 500000000000), (-512649373373 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-512513024733 / 200000000000), (-6174882299 / 3125000000), (-2562563186731 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4926429258513 / 1000000000000), (-217077036793 / 125000000000), (-575007137343 / 500000000000), (-1150013671223 / 1000000000000), (-434153822651 / 250000000000), (-19705830387 / 4000000000)] : List ℚ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-307901828657 / 62500000000), (-1736616294343 / 1000000000000), (-230002854937 / 200000000000), (-575006835611 / 500000000000), (-1736615290603 / 1000000000000), (-4926457596749 / 1000000000000)] : List ℚ).getD
    ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 5 36 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
