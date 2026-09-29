-- Prove2me | solution 1 for mme_released_interior_owner0_cell14_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:12.913295+00:00
-- url     : https://prove2.me/submissions/b064dba1-1ac3-414f-8929-f34dd5603d13

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(99667352647000000000000000000000000 / 1266888800072824983077877689461725137), (99666785782000000000000000000000000 / 1266888800072824983077877689461725137), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (155991060731 / 1000000000000), (239591014389 / 62500000000), (766686730441 / 200000000000), (155990752343 / 1000000000000)], ![(72916890441 / 125000000000), (1050866295973 / 1000000000000), (116665783701 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-508496248541 / 200000000000), (-2542486930291 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1857956576381 / 1000000000000), (268753361249 / 200000000000), (1343760916499 / 1000000000000), (-1857958553343 / 1000000000000)], ![(-538993431833 / 1000000000000), (49614867791 / 1000000000000), (-539004069039 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-158905077669 / 62500000000), (-254248693029 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-92897828819 / 50000000000), (671883403123 / 500000000000), (2687521833 / 2000000000), (-928979276671 / 500000000000)], ![(-67374178979 / 125000000000), (3100929237 / 62500000000), (-269502034519 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1737718505501 / 1000000000000), (-574552729207 / 500000000000), (-2469716613979 / 500000000000), (-4939447575729 / 1000000000000), (-1149105256249 / 1000000000000), (-1737719445627 / 1000000000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-3475437011 / 2000000000), (-1149105458413 / 1000000000000), (-4939433227957 / 1000000000000), (-308715473483 / 62500000000), (-143638157031 / 125000000000), (-868859722813 / 500000000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 14 0 c : ℝ) / 1000000000000) ≤
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
