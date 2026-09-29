-- Prove2me | solution 1 for mme_released_interior_owner2_cell12_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:56.868427+00:00
-- url     : https://prove2.me/submissions/c58227c8-17d8-455f-a19a-36b1bb3d9d4e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 2 12 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(391198099347 / 1000000000000), (195598802769 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(278482514467000000000000000000000000 / 17765793542209823531471970521822931987), (1404379386446000000000000000000000000 / 17765793542209823531471970521822931987), (1404377598937000000000000000000000000 / 17765793542209823531471970521822931987), (278481762107000000000000000000000000 / 17765793542209823531471970521822931987), (1 / 1)], ![(53203463581 / 1000000000000), (1985779452939 / 1000000000000), (13778560304519 / 1000000000000), (496443663373 / 250000000000), (53203460763 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![6, 4, 4, 6, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-469270599677 / 500000000000), (-469271230827 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-831134980719 / 200000000000), (-2537679409963 / 1000000000000), (-101507227311 / 40000000000), (-4155677605241 / 1000000000000), (0 / 1)], ![(-366703972481 / 125000000000), (686011508569 / 1000000000000), (2623113782951 / 1000000000000), (343004545829 / 500000000000), (-586726366563 / 200000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-938541199353 / 1000000000000), (-938542461653 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2077837451797 / 500000000000), (-1268839704981 / 500000000000), (-1268840341387 / 500000000000), (-103891940131 / 25000000000), (0 / 1)], ![(-2933631779847 / 1000000000000), (68601150857 / 100000000000), (327889222869 / 125000000000), (686009091659 / 1000000000000), (-1466815916407 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8027847935727 / 1000000000000), (-2204104136811 / 500000000000), (-2790211517651 / 1000000000000), (-106638511083 / 125000000000), (-106638512397 / 125000000000), (-139510581793 / 50000000000), (-110205182401 / 25000000000), (-8027851846851 / 1000000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4013923967863 / 500000000000), (-4408208273621 / 1000000000000), (-55804230353 / 20000000000), (-853108088663 / 1000000000000), (-34124323967 / 40000000000), (-2790211635859 / 1000000000000), (-4408207296039 / 1000000000000), (-160557036937 / 20000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 2 12 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
