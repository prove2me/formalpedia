-- Prove2me | solution 1 for mme_released_interior_owner0_cell18_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:20.796897+00:00
-- url     : https://prove2.me/submissions/6ffe1954-b833-4669-8255-e50612f72b1d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(57346550703800000000000000000000000 / 774547568918728595350260393857288253), (15246397993700000000000000000000000 / 110649652702675513621465770551041179), (19115436795600000000000000000000000 / 258182522972909531783420131285762751), (1 / 1), (1 / 1)], ![(148104953917 / 250000000000), (59241862969 / 100000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (150642653769 / 1000000000000), (3931693308723 / 1000000000000), (1965841411013 / 500000000000), (150646183879 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2603166379739 / 1000000000000), (-1982025649771 / 1000000000000), (-2603170570357 / 1000000000000), (0 / 1), (0 / 1)], ![(-523539747337 / 1000000000000), (-523541749261 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-23660559727 / 12500000000), (342267550111 / 250000000000), (684533766609 / 500000000000), (-946410672383 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1301583189869 / 500000000000), (-198202564977 / 100000000000), (-650792642589 / 250000000000), (0 / 1), (0 / 1)], ![(-65442468417 / 125000000000), (-26177087463 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1892844778159 / 1000000000000), (273814040089 / 200000000000), (1369067533219 / 1000000000000), (-378564268953 / 200000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1003905494387 / 200000000000), (-878820297891 / 500000000000), (-71031116493 / 62500000000), (-284124299647 / 250000000000), (-1757640117247 / 1000000000000), (-250977854887 / 50000000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-2509763735967 / 500000000000), (-1757640595781 / 1000000000000), (-1136497863887 / 1000000000000), (-1136497198587 / 1000000000000), (-878820058623 / 500000000000), (-5019557097739 / 1000000000000)] : List ℚ).getD
    ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 0 18 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
