-- Prove2me | solution 1 for mme_released_interior_owner4_cell33_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:18:35.213127+00:00
-- url     : https://prove2.me/submissions/366bc300-bfca-4fba-b00c-ee593ba90a3a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 4 33 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53324103813 / 1000000000000), (2034227361483 / 1000000000000), (6573418859501 / 500000000000), (406846059317 / 200000000000), (53324108637 / 1000000000000)], ![(54776331403200000000000000000000000 / 3517457392035683540106142775199524767), (287148259699600000000000000000000000 / 3517457392035683540106142775199524767), (41021208949600000000000000000000000 / 502493913147954791443734682171360681), (54776449419400000000000000000000000 / 3517457392035683540106142775199524767), (1 / 1)], ![(49142219081 / 125000000000), (78627606091 / 200000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2931366820899 / 1000000000000), (177529017963 / 250000000000), (2576181252061 / 1000000000000), (71011751471 / 100000000000), (-2931366730433 / 1000000000000)], ![(-4162235483823 / 1000000000000), (-1252747504541 / 500000000000), (-2505494302313 / 1000000000000), (-832446665863 / 200000000000), (0 / 1)], ![(-466797606443 / 500000000000), (-466797253123 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1465683410449 / 500000000000), (710116071853 / 1000000000000), (1288090626031 / 500000000000), (710117514711 / 1000000000000), (-45802605163 / 15625000000)], ![(-2081117741911 / 500000000000), (-2505495009081 / 1000000000000), (-313186787789 / 125000000000), (-2081116664657 / 500000000000), (0 / 1)], ![(-186719042577 / 200000000000), (-186718901249 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-802719742771 / 100000000000), (-4385712475367 / 1000000000000), (-545794541451 / 200000000000), (-862908263267 / 1000000000000), (-215727065783 / 250000000000), (-272897273671 / 100000000000), (-4385712470389 / 1000000000000), (-8027194658631 / 1000000000000)] : List ℚ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8027197427709 / 1000000000000), (-2192856237683 / 500000000000), (-1364486353627 / 500000000000), (-431454131633 / 500000000000), (-862908263131 / 1000000000000), (-2728972736709 / 1000000000000), (-1096428117597 / 250000000000), (-802719465863 / 100000000000)] : List ℚ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 33 1 c : ℝ) / 1000000000000) ≤
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
