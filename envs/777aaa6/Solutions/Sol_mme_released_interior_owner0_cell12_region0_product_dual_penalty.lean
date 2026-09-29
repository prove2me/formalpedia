-- Prove2me | solution 1 for mme_released_interior_owner0_cell12_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:07.583797+00:00
-- url     : https://prove2.me/submissions/1e641c15-5639-417f-9aaf-f051a4cc3757

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(391152703088000000000000000000000000 / 17765133170722065943151089875408940383), (391150953791000000000000000000000000 / 17765133170722065943151089875408940383), (1 / 1), (1 / 1), (1 / 1)], ![(17405078817 / 62500000000), (1404621055221 / 1000000000000), (28092289409 / 20000000000), (27848062813 / 100000000000), (1 / 1)], ![(53203255983 / 1000000000000), (496432228209 / 250000000000), (13777244716143 / 1000000000000), (992856792679 / 500000000000), (10640651411 / 200000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-476986871993 / 125000000000), (-3815899448113 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-639202253539 / 500000000000), (16988377741 / 50000000000), (543620587 / 1600000000), (-319601694979 / 250000000000), (0 / 1)], ![(-146681784091 / 50000000000), (68598605723 / 100000000000), (1311509148781 / 500000000000), (685978338383 / 1000000000000), (-2933635661671 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3815894975943 / 1000000000000), (-238493715507 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1278404507077 / 1000000000000), (339767554821 / 1000000000000), (84940716719 / 250000000000), (-255681355983 / 200000000000), (0 / 1)], ![(-2933635681819 / 1000000000000), (685986057231 / 1000000000000), (2623018297563 / 1000000000000), (42873646149 / 62500000000), (-293363566167 / 100000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8027935145777 / 1000000000000), (-558029816547 / 200000000000), (-170622762301 / 200000000000), (-4408315698667 / 1000000000000), (-551040702097 / 125000000000), (-853113595727 / 1000000000000), (-2790150524017 / 1000000000000), (-160558838223 / 20000000000)] : List ℚ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-501745946611 / 62500000000), (-1395074541367 / 500000000000), (-53319613219 / 62500000000), (-2204157849333 / 500000000000), (-176333024671 / 40000000000), (-426556797863 / 500000000000), (-174384407751 / 62500000000), (-8027941911149 / 1000000000000)] : List ℚ).getD
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
        (splitWeight 0 12 0 c : ℝ) / 1000000000000) ≤
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
