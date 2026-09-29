-- Prove2me | solution 1 for mme_released_interior_owner0_cell12_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:08.404235+00:00
-- url     : https://prove2.me/submissions/7cc88dd0-29ed-4d04-afae-f9c8eab63042

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(32564728792000000000000000000000000 / 1483442892523938735503908287050256991), (32564700613750000000000000000000000 / 1483442892523938735503908287050256991), (1 / 1), (1 / 1), (1 / 1)], ![(138296252007 / 500000000000), (35326384831 / 25000000000), (1413053728567 / 1000000000000), (276596410481 / 1000000000000), (1 / 1)], ![(26628981337 / 500000000000), (248055158829 / 125000000000), (13735565980857 / 1000000000000), (1984441675191 / 1000000000000), (53257973943 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-763778236027 / 200000000000), (-763778409087 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-51408398423 / 40000000000), (34575430551 / 100000000000), (345753127443 / 1000000000000), (-160649479641 / 125000000000), (0 / 1)], ![(-733151987947 / 250000000000), (137067479753 / 200000000000), (523997705179 / 200000000000), (68533760263 / 100000000000), (-586521548039 / 200000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1909445590067 / 500000000000), (-1909446022717 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-642604980287 / 500000000000), (345754305511 / 1000000000000), (86438281861 / 250000000000), (-1285195837127 / 1000000000000), (0 / 1)], ![(-2932607951787 / 1000000000000), (342668699383 / 500000000000), (327498565737 / 125000000000), (685337602631 / 1000000000000), (-1466303870097 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-1004588610003 / 125000000000), (-2787799271987 / 1000000000000), (-853149526797 / 1000000000000), (-4418749618463 / 1000000000000), (-883752880669 / 200000000000), (-426574607017 / 500000000000), (-348475189903 / 125000000000), (-8036695833193 / 1000000000000)] : List ℚ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4018354440011 / 500000000000), (-1393899635993 / 500000000000), (-213287381699 / 250000000000), (-2209374809231 / 500000000000), (-276172775209 / 62500000000), (-853149214033 / 1000000000000), (-2787801519223 / 1000000000000), (-1004586979149 / 125000000000)] : List ℚ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 0 12 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
