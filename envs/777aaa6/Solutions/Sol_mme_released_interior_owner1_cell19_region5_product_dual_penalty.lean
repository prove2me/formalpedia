-- Prove2me | solution 1 for mme_released_interior_owner1_cell19_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:47.730026+00:00
-- url     : https://prove2.me/submissions/96765af7-3ecd-4404-9ff0-5315cd66d711

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(7416144177250000000000000000000000 / 363365641820939655679682270059668593), (96761230920000000000000000000000000 / 2543559492746577589757775890417680151), (51911326819000000000000000000000000 / 2543559492746577589757775890417680151), (1 / 1), (1 / 1)], ![(401204022671 / 1000000000000), (165988496811 / 200000000000), (401191028697 / 1000000000000), (1 / 1), (1 / 1)], ![(19472512959 / 500000000000), (557195167139 / 250000000000), (17848830151989 / 1000000000000), (445741333001 / 200000000000), (973625251 / 25000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1945875167797 / 500000000000), (-3269073347067 / 1000000000000), (-19458913723 / 5000000000), (0 / 1), (0 / 1)], ![(-913285196347 / 1000000000000), (-11649929807 / 62500000000), (-913317584319 / 1000000000000), (0 / 1), (0 / 1)], ![(-811401054777 / 250000000000), (801454650529 / 1000000000000), (1440968984187 / 500000000000), (400710723187 / 500000000000), (-3245604626811 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3891750335593 / 1000000000000), (-1634536673533 / 500000000000), (-3891782744599 / 1000000000000), (0 / 1), (0 / 1)], ![(-456642598173 / 500000000000), (-186398876911 / 1000000000000), (-456658792159 / 500000000000), (0 / 1), (0 / 1)], ![(-3245604219107 / 1000000000000), (80145465053 / 100000000000), (23055503747 / 8000000000), (6411371571 / 8000000000), (-324560462681 / 100000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-961564974441 / 500000000000), (-819181944109 / 250000000000), (-8050640158637 / 1000000000000), (-338093629227 / 100000000000), (-143383563901 / 250000000000), (-3380937085613 / 1000000000000), (-8050704548127 / 1000000000000), (-1638363480341 / 500000000000), (-30048905863 / 15625000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1923129948881 / 1000000000000), (-655345555287 / 200000000000), (-2012660039659 / 250000000000), (-3380936292269 / 1000000000000), (-573534255603 / 1000000000000), (-845234271403 / 250000000000), (-4025352274063 / 500000000000), (-3276726960681 / 1000000000000), (-1923129975231 / 1000000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 1 19 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
