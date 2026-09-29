-- Prove2me | solution 1 for mme_released_interior_owner0_cell28_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:00.876261+00:00
-- url     : https://prove2.me/submissions/2ef7e5a5-f3a8-4144-b734-ba61c73434e3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(138077693837000000000000000000000000 / 8768957711376281870396838421482526861), (712697367334500000000000000000000000 / 8768957711376281870396838421482526861), (712698996303500000000000000000000000 / 8768957711376281870396838421482526861), (138078689696500000000000000000000000 / 8768957711376281870396838421482526861), (1 / 1)], ![(26652652987 / 500000000000), (508872462681 / 250000000000), (13184521472593 / 1000000000000), (1017749619479 / 500000000000), (26652655579 / 500000000000)], ![(393731479829 / 1000000000000), (393732379171 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4151156705703 / 1000000000000), (-1254958175343 / 500000000000), (-2509914065049 / 1000000000000), (-518893686677 / 125000000000), (0 / 1)], ![(-586343880707 / 200000000000), (355368251407 / 500000000000), (2579043525827 / 1000000000000), (177685278769 / 250000000000), (-732929826571 / 250000000000)], ![(-116510765663 / 125000000000), (-233020960289 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2075578352851 / 500000000000), (-501983270137 / 200000000000), (-313739258131 / 125000000000), (-830229898683 / 200000000000), (0 / 1)], ![(-1465859701767 / 500000000000), (142147300563 / 200000000000), (644760881457 / 250000000000), (710741115077 / 1000000000000), (-2931719306283 / 1000000000000)], ![(-932086125303 / 1000000000000), (-186416768231 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-2186249715911 / 500000000000), (-64119697091 / 8000000000), (-431478333007 / 500000000000), (-1365630680461 / 500000000000), (-1365630701693 / 500000000000), (-862956664523 / 1000000000000), (-801495273799 / 100000000000), (-4372499115887 / 1000000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4372499431821 / 1000000000000), (-4007481068187 / 500000000000), (-862956666013 / 1000000000000), (-2731261360921 / 1000000000000), (-546252280677 / 200000000000), (-431478332261 / 500000000000), (-8014952737989 / 1000000000000), (-2186249557943 / 500000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 0 28 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
