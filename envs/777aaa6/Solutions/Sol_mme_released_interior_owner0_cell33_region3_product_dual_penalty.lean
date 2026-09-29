-- Prove2me | solution 1 for mme_released_interior_owner0_cell33_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:09.190981+00:00
-- url     : https://prove2.me/submissions/da70849b-0cd6-4222-9f6a-c0150aeed853

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(10679627808800000000000000000000000 / 3490133984837703142895703346440601491), (413155351855400000000000000000000000 / 3490133984837703142895703346440601491), (851879597002600000000000000000000000 / 1163377994945901047631901115480200497), (413155293379000000000000000000000000 / 3490133984837703142895703346440601491), (10679627783800000000000000000000000 / 3490133984837703142895703346440601491)], ![(27217215251 / 100000000000), (1450343572439 / 1000000000000), (145034341643 / 100000000000), (136086133643 / 500000000000), (1 / 1)], ![(3947108849 / 10000000000), (394710846027 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-578935742197 / 100000000000), (-426774345737 / 200000000000), (-77909479523 / 250000000000), (-2133871870221 / 1000000000000), (-578935742431 / 100000000000)], ![(-325330124813 / 250000000000), (185900237437 / 500000000000), (371800367307 / 1000000000000), (-1301320077549 / 1000000000000), (0 / 1)], ![(-726251343 / 781250000), (-37184072701 / 40000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5789357421969 / 1000000000000), (-533467932171 / 250000000000), (-311637918091 / 1000000000000), (-106693593511 / 50000000000), (-5789357424309 / 1000000000000)], ![(-1301320499251 / 1000000000000), (2974403799 / 8000000000), (92950091827 / 250000000000), (-325330019387 / 250000000000), (0 / 1)], ![(-929601719039 / 1000000000000), (-232400454381 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8020279315837 / 1000000000000), (-538334635779 / 200000000000), (-4364793525293 / 1000000000000), (-173887852149 / 200000000000), (-13584988591 / 15625000000), (-4364794186991 / 1000000000000), (-134583655719 / 50000000000), (-4010139820667 / 500000000000)] : List ℚ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-2005069828959 / 250000000000), (-1345836589447 / 500000000000), (-1091198381323 / 250000000000), (-108679907593 / 125000000000), (-869439269823 / 1000000000000), (-436479418699 / 100000000000), (-2691673114379 / 1000000000000), (-8020279641333 / 1000000000000)] : List ℚ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 0 33 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
