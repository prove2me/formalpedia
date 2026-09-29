-- Prove2me | solution 1 for mme_released_interior_owner0_cell33_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:09.871995+00:00
-- url     : https://prove2.me/submissions/bbd8c137-59b9-4dd4-b8b6-a04227c9f0af

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53414146272000000000000000000000000 / 17429756296706884558906212556032761893), (2066067387849000000000000000000000000 / 17429756296706884558906212556032761893), (12774178222662000000000000000000000000 / 17429756296706884558906212556032761893), (295152110231000000000000000000000000 / 2489965185243840651272316079433251699), (7630592427000000000000000000000000 / 2489965185243840651272316079433251699)], ![(54542757913 / 200000000000), (723971497499 / 500000000000), (36198546097 / 25000000000), (136356878571 / 500000000000), (1 / 1)], ![(49368645559 / 125000000000), (78989774049 / 200000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5787858534243 / 1000000000000), (-1066265944947 / 500000000000), (-310753070577 / 1000000000000), (-2132533156181 / 1000000000000), (-289392926041 / 50000000000)], ![(-259866484723 / 200000000000), (370143925093 / 1000000000000), (37014313009 / 100000000000), (-259866508501 / 200000000000), (0 / 1)], ![(-928998219903 / 1000000000000), (-464499482439 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2893929267121 / 500000000000), (-2132531889893 / 1000000000000), (-19422066911 / 62500000000), (-106626657809 / 50000000000), (-5787858520819 / 1000000000000)], ![(-649666211807 / 500000000000), (185071962547 / 500000000000), (370143130091 / 1000000000000), (-162416567813 / 125000000000), (0 / 1)], ![(-464499109951 / 500000000000), (-928998964877 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-2004047510397 / 250000000000), (-1345693862337 / 500000000000), (-174434506093 / 40000000000), (-869608110361 / 1000000000000), (-869608160391 / 1000000000000), (-4360864544651 / 1000000000000), (-168211715687 / 62500000000), (-8016189163001 / 1000000000000)] : List ℚ).getD
    ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8016190041587 / 1000000000000), (-2691387724673 / 1000000000000), (-1090215663081 / 250000000000), (-21740202759 / 25000000000), (-86960816039 / 100000000000), (-87217290893 / 20000000000), (-2691387450991 / 1000000000000), (-8016189163 / 1000000000)] : List ℚ).getD
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
        (splitWeight 0 33 5 c : ℝ) / 1000000000000) ≤
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
