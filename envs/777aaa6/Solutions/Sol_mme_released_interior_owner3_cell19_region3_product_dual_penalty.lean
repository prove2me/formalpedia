-- Prove2me | solution 1 for mme_released_interior_owner3_cell19_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:32.641773+00:00
-- url     : https://prove2.me/submissions/0ef182ef-af5a-4238-b438-c6a545009332

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(102175421263 / 250000000000), (803068660767 / 1000000000000), (204327719523 / 500000000000), (1 / 1), (1 / 1)], ![(410501690303 / 1000000000000), (99650161567 / 125000000000), (410455240323 / 1000000000000), (1 / 1), (1 / 1)], ![(4303418711000000000000000000000000 / 2250103417371324715641060292272299577), (751599435413000000000000000000000000 / 6750310252113974146923180876816898731), (17712478218167000000000000000000000000 / 20250930756341922440769542630450696193), (751513647166000000000000000000000000 / 6750310252113974146923180876816898731), (12910171249000000000000000000000000 / 6750310252113974146923180876816898731)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-178953953093 / 200000000000), (-219315063377 / 1000000000000), (-447441462659 / 500000000000), (0 / 1), (0 / 1)], ![(-89037523243 / 100000000000), (-226648069301 / 1000000000000), (-890488393007 / 1000000000000), (0 / 1), (0 / 1)], ![(-3129660850767 / 500000000000), (-68598132179 / 31250000000), (-267862761 / 2000000000), (-2195254377157 / 1000000000000), (-6259328276483 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-111846220683 / 125000000000), (-13707191461 / 62500000000), (-894882925317 / 1000000000000), (0 / 1), (0 / 1)], ![(-890375232429 / 1000000000000), (-2266480693 / 10000000000), (-445244196503 / 500000000000), (0 / 1), (0 / 1)], ![(-6259321701533 / 1000000000000), (-2195140229727 / 1000000000000), (-133931380499 / 1000000000000), (-548813594289 / 250000000000), (-3129664138241 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8044693018631 / 1000000000000), (-1652471843191 / 500000000000), (-3316671224067 / 1000000000000), (-191918953891 / 100000000000), (-28994725659 / 50000000000), (-191918953831 / 100000000000), (-132666888487 / 40000000000), (-3304944672697 / 1000000000000), (-251389789793 / 31250000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-804469301863 / 100000000000), (-3304943686381 / 1000000000000), (-1658335612033 / 500000000000), (-1919189538909 / 1000000000000), (-579894513179 / 1000000000000), (-1919189538309 / 1000000000000), (-1658336106087 / 500000000000), (-413118084087 / 125000000000), (-64355786187 / 8000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 3 19 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
