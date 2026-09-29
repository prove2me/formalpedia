-- Prove2me | solution 1 for mme_released_interior_owner4_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:17:22.429949+00:00
-- url     : https://prove2.me/submissions/58fd2ce0-df33-42ad-920a-52551f3bbcd2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 4 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(202855139493 / 500000000000), (413620590777 / 500000000000), (405759996159 / 1000000000000), (1 / 1), (1 / 1)], ![(38848577591000000000000000000000000 / 19954284950786336981020733184348768063), (2308936843717000000000000000000000000 / 19954284950786336981020733184348768063), (17061949190174000000000000000000000000 / 19954284950786336981020733184348768063), (769740742901000000000000000000000000 / 6651428316928778993673577728116256021), (38848781998000000000000000000000000 / 19954284950786336981020733184348768063)], ![(207978901939 / 500000000000), (196905532127 / 250000000000), (416008780389 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-90211597267 / 100000000000), (-189658992191 / 1000000000000), (-5637458979 / 6250000000), (0 / 1), (0 / 1)], ![(-6241527720457 / 1000000000000), (-2156656726999 / 1000000000000), (-31318622849 / 200000000000), (-2156533134467 / 1000000000000), (-6241522458837 / 1000000000000)], ![(-219292864213 / 250000000000), (-238736836487 / 1000000000000), (-10963111403 / 12500000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-902115972669 / 1000000000000), (-18965899219 / 100000000000), (-901993436639 / 1000000000000), (0 / 1), (0 / 1)], ![(-780190965057 / 125000000000), (-1078328363499 / 500000000000), (-39148278561 / 250000000000), (-1078266567233 / 500000000000), (-1560380614709 / 250000000000)], ![(-877171456851 / 1000000000000), (-119368418243 / 500000000000), (-877048912239 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4010285034701 / 500000000000), (-103043343757 / 31250000000), (-3223364631353 / 1000000000000), (-1935758007711 / 1000000000000), (-584988942921 / 1000000000000), (-967878999587 / 500000000000), (-1611681791793 / 500000000000), (-206086621471 / 62500000000), (-1002601236089 / 125000000000)] : List ℚ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020570069401 / 1000000000000), (-3297387000223 / 1000000000000), (-402920578919 / 125000000000), (-193575800771 / 100000000000), (-14624723573 / 25000000000), (-1935757999173 / 1000000000000), (-644672716717 / 200000000000), (-659477188707 / 200000000000), (-8020809888711 / 1000000000000)] : List ℚ).getD
    ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 4 21 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
