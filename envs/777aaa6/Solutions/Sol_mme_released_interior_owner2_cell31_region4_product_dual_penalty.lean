-- Prove2me | solution 1 for mme_released_interior_owner2_cell31_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:35.997898+00:00
-- url     : https://prove2.me/submissions/332b62fe-9719-4ef8-9bae-df48d1106889

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 2 31 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53397678663 / 1000000000000), (2065383430999 / 1000000000000), (798259912439 / 62500000000), (1032750740543 / 500000000000), (53397747269 / 1000000000000)], ![(1095838667825000000000000000000000 / 48515237048119977323981130762611507), (3287607653725000000000000000000000 / 145545711144359931971943392287834521), (1 / 1), (1 / 1), (1 / 1)], ![(54301988479 / 200000000000), (363269667349 / 250000000000), (1453118956427 / 1000000000000), (271535309207 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-732497001173 / 250000000000), (725315890047 / 1000000000000), (2547267692487 / 1000000000000), (725373044913 / 1000000000000), (-73249667997 / 25000000000)], ![(-236897371109 / 62500000000), (-758066011973 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-32593913001 / 25000000000), (186842262929 / 500000000000), (186856125383 / 500000000000), (-1303663095737 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929988004691 / 1000000000000), (5666530391 / 7812500000), (318408461561 / 125000000000), (362686522457 / 500000000000), (-2929986719879 / 1000000000000)], ![(-3790357937743 / 1000000000000), (-473791257483 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1303756520039 / 1000000000000), (373684525859 / 1000000000000), (373712250767 / 1000000000000), (-162957886967 / 125000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-546088142933 / 125000000000), (-108672249311 / 125000000000), (-1345650183487 / 500000000000), (-401205058887 / 50000000000), (-8023981160233 / 1000000000000), (-672825479761 / 250000000000), (-10867223019 / 12500000000), (-873742706993 / 200000000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4368705143463 / 1000000000000), (-869377994487 / 1000000000000), (-2691300366973 / 1000000000000), (-8024101177739 / 1000000000000), (-1002997645029 / 125000000000), (-2691301919043 / 1000000000000), (-869377841519 / 1000000000000), (-1092178383741 / 250000000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 2 31 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
