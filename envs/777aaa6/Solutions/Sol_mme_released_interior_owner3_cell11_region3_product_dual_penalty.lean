-- Prove2me | solution 1 for mme_released_interior_owner3_cell11_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:38.593559+00:00
-- url     : https://prove2.me/submissions/b39569fb-e1ac-4996-a77f-252f2b987efb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 3 11 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(592270051887 / 1000000000000), (592271945331 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(574011003433 / 1000000000000), (1064139667183 / 1000000000000), (287007329867 / 500000000000), (1 / 1), (1 / 1)], ![(1 / 1), (37535204316500000000000000000000000 / 1938212386410911429123234580870283689), (109520820750000000000000000000000000 / 215356931823434603235914953430031521), (985690736371000000000000000000000000 / 1938212386410911429123234580870283689), (37535175494000000000000000000000000 / 1938212386410911429123234580870283689)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-65474072423 / 125000000000), (-261894691231 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-555106713103 / 1000000000000), (31083324227 / 500000000000), (-555100343383 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-986060525647 / 250000000000), (-135236424921 / 200000000000), (-676178726351 / 1000000000000), (-986060717617 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-523792579383 / 1000000000000), (-523789382461 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-277553356551 / 500000000000), (12433329691 / 200000000000), (-277550171691 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3944242102587 / 1000000000000), (-169045531151 / 250000000000), (-13523574527 / 20000000000), (-3944242870467 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1004626365679 / 200000000000), (-175507504737 / 100000000000), (-1137804858613 / 1000000000000), (-568902328641 / 500000000000), (-877537410957 / 500000000000), (-251157108147 / 50000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2511565914197 / 500000000000), (-1755075047369 / 1000000000000), (-284451214653 / 250000000000), (-1137804657281 / 1000000000000), (-1755074821913 / 1000000000000), (-5023142162939 / 1000000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 11 3 c : ℝ) / 1000000000000) ≤
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
