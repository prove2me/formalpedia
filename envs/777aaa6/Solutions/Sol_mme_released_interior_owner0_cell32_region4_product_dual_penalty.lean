-- Prove2me | solution 1 for mme_released_interior_owner0_cell32_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:07.80518+00:00
-- url     : https://prove2.me/submissions/99bb4ec1-6d6a-4235-9f67-240e5e645ac7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19512461887500000000000000000000000 / 9866469782162362368785257309586574023), (1166363051094000000000000000000000000 / 9866469782162362368785257309586574023), (8314439285293000000000000000000000000 / 9866469782162362368785257309586574023), (1166334241510500000000000000000000000 / 9866469782162362368785257309586574023), (19512451899000000000000000000000000 / 9866469782162362368785257309586574023)], ![(210197473629 / 500000000000), (779369677359 / 1000000000000), (420384721631 / 1000000000000), (1 / 1), (1 / 1)], ![(3155299553 / 7812500000), (168946493809 / 200000000000), (201934380817 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-622584406433 / 100000000000), (-1067625856957 / 500000000000), (-85574220851 / 500000000000), (-133454775911 / 62500000000), (-3112922288117 / 500000000000)], ![(-1692501287 / 1953125000), (-249269791943 / 1000000000000), (-866584983097 / 1000000000000), (0 / 1), (0 / 1)], ![(-453320789047 / 500000000000), (-42183826609 / 250000000000), (-226666325309 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6225844064329 / 1000000000000), (-2135251713913 / 1000000000000), (-171148441701 / 1000000000000), (-85411056583 / 40000000000), (-6225844576233 / 1000000000000)], ![(-866560658943 / 1000000000000), (-124634895971 / 500000000000), (-108323122887 / 125000000000), (0 / 1), (0 / 1)], ![(-906641578093 / 1000000000000), (-33747061287 / 200000000000), (-181333060247 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7999094347757 / 1000000000000), (-3291186856123 / 1000000000000), (-3170571959971 / 1000000000000), (-194437438913 / 100000000000), (-7364419251 / 12500000000), (-1944375015647 / 1000000000000), (-3170572423411 / 1000000000000), (-822796933893 / 250000000000), (-7999046812887 / 1000000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1999773586939 / 250000000000), (-1645593428061 / 500000000000), (-317057195997 / 100000000000), (-1944374389129 / 1000000000000), (-589153540079 / 1000000000000), (-972187507823 / 500000000000), (-317057242341 / 100000000000), (-3291187735571 / 1000000000000), (-3999523406443 / 500000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 0 32 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
