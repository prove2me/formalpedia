-- Prove2me | solution 1 for mme_released_interior_owner2_cell32_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:46:52.472981+00:00
-- url     : https://prove2.me/submissions/9b98ce1b-cff4-4bc7-9a04-9d3bafedc1b9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 2 32 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(38934277887 / 1000000000000), (73466411961 / 31250000000), (207220378377 / 12500000000), (1175572525183 / 500000000000), (1216702299 / 31250000000)], ![(203602303695500000000000000000000000 / 9852669421184272402844163170132441479), (415370117599000000000000000000000000 / 9852669421184272402844163170132441479), (203621194260000000000000000000000000 / 9852669421184272402844163170132441479), (1 / 1), (1 / 1)], ![(417419958567 / 1000000000000), (792108066097 / 1000000000000), (208729344577 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-649176047351 / 200000000000), (427404472733 / 500000000000), (2808054212481 / 1000000000000), (2671570203 / 3125000000), (-811468802709 / 250000000000)], ![(-1939664552627 / 500000000000), (-197895483267 / 62500000000), (-31033890623 / 8000000000), (0 / 1), (0 / 1)], ![(-873662469079 / 1000000000000), (-29132181173 / 125000000000), (-436784843861 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1622940118377 / 500000000000), (854808945467 / 1000000000000), (1404027106241 / 500000000000), (854902464961 / 1000000000000), (-649175042167 / 200000000000)], ![(-3879329105253 / 1000000000000), (-3166327732271 / 1000000000000), (-1939618163937 / 500000000000), (0 / 1), (0 / 1)], ![(-436831234539 / 500000000000), (-233057449383 / 1000000000000), (-873569687721 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944844580793 / 1000000000000), (-3257484088557 / 1000000000000), (-1599773356799 / 200000000000), (-3185088473493 / 1000000000000), (-295665484589 / 500000000000), (-3185087737413 / 1000000000000), (-199967156291 / 25000000000), (-1628742416449 / 500000000000), (-1944844584171 / 1000000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-243105572599 / 125000000000), (-814371022139 / 250000000000), (-3999433391997 / 500000000000), (-796272118373 / 250000000000), (-591330969177 / 1000000000000), (-796271934353 / 250000000000), (-7998686251639 / 1000000000000), (-3257484832897 / 1000000000000), (-194484458417 / 100000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 32 2 c : ℝ) / 1000000000000) ≤
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
