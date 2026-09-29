-- Prove2me | solution 1 for mme_released_interior_owner3_cell22_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:13:50.001871+00:00
-- url     : https://prove2.me/submissions/956d2f8d-bd64-4dec-8b72-382ec4afc5fb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 3 22 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(291768978989 / 500000000000), (526155732469 / 500000000000), (58353257861 / 100000000000), (1 / 1), (1 / 1)], ![(1 / 1), (156002532693 / 1000000000000), (1908701065101 / 500000000000), (1908692622309 / 500000000000), (78001126357 / 500000000000)], ![(2515254714500000000000000000000000 / 31871741609795564952547101266785987), (17606698421500000000000000000000000 / 223102191268568954667829708867501909), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-538645777139 / 1000000000000), (12747284957 / 250000000000), (-538654995721 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1857883036653 / 1000000000000), (1339570120637 / 1000000000000), (1339565697309 / 1000000000000), (-1857884831363 / 1000000000000)], ![(-2539345697693 / 1000000000000), (-507870100307 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-269322888569 / 500000000000), (50989139829 / 1000000000000), (-13466374893 / 25000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-464470759163 / 250000000000), (669785060319 / 500000000000), (133956569731 / 100000000000), (-928942415681 / 500000000000)], ![(-634836424423 / 250000000000), (-1269675250767 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4935876306257 / 1000000000000), (-1148790860553 / 1000000000000), (-869215286387 / 500000000000), (-1738430581363 / 1000000000000), (-1148791241069 / 1000000000000), (-2467944266961 / 500000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-308492269141 / 62500000000), (-143598857569 / 125000000000), (-1738430572773 / 1000000000000), (-869215290681 / 500000000000), (-287197810267 / 250000000000), (-4935888533921 / 1000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 3 22 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
