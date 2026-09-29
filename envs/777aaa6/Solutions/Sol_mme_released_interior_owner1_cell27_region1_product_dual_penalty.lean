-- Prove2me | solution 1 for mme_released_interior_owner1_cell27_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:32.852524+00:00
-- url     : https://prove2.me/submissions/e8a3ca89-d759-4c87-807d-767362a1a835

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(55187820164000000000000000000000000 / 5397207116684225041846926811714531357), (2475736303693000000000000000000000000 / 16191621350052675125540780435143594071), (2475567459520000000000000000000000000 / 16191621350052675125540780435143594071), (55176343940000000000000000000000000 / 5397207116684225041846926811714531357), (1 / 1)], ![(34055354107 / 200000000000), (481184655811 / 200000000000), (1202879399151 / 500000000000), (85121123387 / 500000000000), (1 / 1)], ![(88823767891 / 200000000000), (850029074279 / 1000000000000), (88811633373 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4582894618411 / 1000000000000), (-1877956059611 / 1000000000000), (-469506065379 / 250000000000), (-286443911783 / 62500000000), (0 / 1)], ![(-885165051909 / 500000000000), (438966864851 / 500000000000), (219466340611 / 250000000000), (-1770532875231 / 1000000000000), (0 / 1)], ![(-405831547967 / 500000000000), (-162484725049 / 1000000000000), (-405899859339 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-458289461841 / 100000000000), (-187795605961 / 100000000000), (-375604852303 / 200000000000), (-4583102588527 / 1000000000000), (0 / 1)], ![(-1770330103817 / 1000000000000), (877933729703 / 1000000000000), (175573072489 / 200000000000), (-177053287523 / 100000000000), (0 / 1)], ![(-811663095933 / 1000000000000), (-20310590631 / 125000000000), (-811799718677 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-6487006719427 / 1000000000000), (-4520809547671 / 1000000000000), (-4463912858433 / 1000000000000), (-581357108907 / 500000000000), (-226411361051 / 125000000000), (-362258166971 / 200000000000), (-372068497 / 320000000), (-446391490077 / 100000000000), (-282550782497 / 62500000000), (-6487011911479 / 1000000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-3243503359713 / 500000000000), (-452080954767 / 100000000000), (-69748638413 / 15625000000), (-1162714217813 / 1000000000000), (-1811290888407 / 1000000000000), (-905645417427 / 500000000000), (-290678513281 / 250000000000), (-4463914900769 / 1000000000000), (-4520812519951 / 1000000000000), (-3243505955739 / 500000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 1 27 1 c : ℝ) / 1000000000000) ≤
          (1649 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1649 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1649 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
