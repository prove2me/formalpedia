-- Prove2me | solution 1 for mme_released_interior_owner5_cell14_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:21:18.178982+00:00
-- url     : https://prove2.me/submissions/64f58150-dca1-4ce7-bee9-6cd1b2e6c8af

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 5 14 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(596795285363 / 1000000000000), (298394830877 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (19355067061 / 125000000000), (963553652189 / 250000000000), (1927087361859 / 500000000000), (154839798657 / 1000000000000)], ![(581202943963000000000000000000000000 / 7632126063286057686596809198059467259), (351499920105000000000000000000000000 / 2544042021095352562198936399353155753), (581191935734000000000000000000000000 / 7632126063286057686596809198059467259), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-103236225997 / 200000000000), (-516190553041 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-186535948849 / 100000000000), (1349167253121 / 1000000000000), (674578452323 / 500000000000), (-1865364253603 / 1000000000000)], ![(-2575021733717 / 1000000000000), (-1979299958097 / 1000000000000), (-1287520337159 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2016332539 / 3906250000), (-6452381913 / 12500000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1865359488489 / 1000000000000), (674583626561 / 500000000000), (1349156904647 / 1000000000000), (-932682126801 / 500000000000)], ![(-643755433429 / 250000000000), (-123706247381 / 62500000000), (-2575040674317 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1742055382111 / 1000000000000), (-1239141779329 / 250000000000), (-573161629009 / 500000000000), (-573162091717 / 500000000000), (-4956590715857 / 1000000000000), (-87102727559 / 50000000000)] : List ℚ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-174205538211 / 100000000000), (-991313423463 / 200000000000), (-1146323258017 / 1000000000000), (-1146324183433 / 1000000000000), (-309786919741 / 62500000000), (-1742054551179 / 1000000000000)] : List ℚ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 14 0 c : ℝ) / 1000000000000) ≤
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
