-- Prove2me | solution 1 for mme_released_interior_owner1_cell15_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:38.079823+00:00
-- url     : https://prove2.me/submissions/2bd8e29a-59fb-4441-ae0d-a4df63d7e89d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 1 15 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(212723117890250000000000000000000000 / 935885376415582966810037953172543259), (212723403976250000000000000000000000 / 935885376415582966810037953172543259), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (605271211509 / 1000000000000), (19762266521 / 10000000000), (605270149929 / 1000000000000)], ![(852129796529 / 1000000000000), (852130783423 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![0, 0, 1, 0, 1], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1481501603807 / 1000000000000), (-1481500258933 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-100415727583 / 200000000000), (681189295227 / 1000000000000), (-3922503061 / 7812500000)], ![(-40004105103 / 250000000000), (-160015262263 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-740750801903 / 500000000000), (-370375064733 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-251039318957 / 500000000000), (170297323807 / 250000000000), (-502080391807 / 1000000000000)], ![(-160016420411 / 1000000000000), (-80007631131 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 15) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-1071799208013 / 500000000000), (-960327570841 / 1000000000000), (-24008184603 / 25000000000), (-535898539777 / 250000000000)] : List ℚ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-85743936641 / 40000000000), (-24008189271 / 25000000000), (-960327384119 / 1000000000000), (-2143594159107 / 1000000000000)] : List ℚ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 15 0 c : ℝ) / 1000000000000) ≤
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
