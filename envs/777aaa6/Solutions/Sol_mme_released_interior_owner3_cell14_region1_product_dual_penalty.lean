-- Prove2me | solution 1 for mme_released_interior_owner3_cell14_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:46.789552+00:00
-- url     : https://prove2.me/submissions/bb3c699f-dc62-423f-b4aa-a6cacfdcd904

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(596750803761 / 1000000000000), (596752247631 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (38696195759 / 250000000000), (240956437163 / 62500000000), (1927655145907 / 500000000000), (30957747473 / 200000000000)], ![(581172960385000000000000000000000000 / 7633216179254724390990929570829975717), (351470274871000000000000000000000000 / 2544405393084908130330309856943325239), (581175633494000000000000000000000000 / 7633216179254724390990929570829975717), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-516255666867 / 1000000000000), (-258126623659 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-93285981173 / 50000000000), (1349449601749 / 1000000000000), (1349451494519 / 1000000000000), (-932847038257 / 500000000000)], ![(-2575216146217 / 1000000000000), (-197952712323 / 100000000000), (-2575211546721 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-258127833433 / 500000000000), (-516253247317 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1865719623459 / 1000000000000), (5397798407 / 4000000000), (33736287363 / 25000000000), (-1865694076513 / 1000000000000)], ![(-321902018277 / 125000000000), (-1979527123229 / 1000000000000), (-16095072167 / 6250000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1239291472417 / 250000000000), (-871008949509 / 500000000000), (-1146331295577 / 1000000000000), (-573165384397 / 500000000000), (-5443805037 / 3125000000), (-619648052189 / 125000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4957165889667 / 1000000000000), (-1742017899017 / 1000000000000), (-143291411947 / 125000000000), (-1146330768793 / 1000000000000), (-1742017611839 / 1000000000000), (-4957184417511 / 1000000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 14 1 c : ℝ) / 1000000000000) ≤
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
