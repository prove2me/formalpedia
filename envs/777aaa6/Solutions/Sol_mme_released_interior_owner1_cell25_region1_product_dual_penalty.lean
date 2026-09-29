-- Prove2me | solution 1 for mme_released_interior_owner1_cell25_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:27.246331+00:00
-- url     : https://prove2.me/submissions/44f3ef26-d034-45f5-89a0-efaac37b9a51

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 1 25 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(792852013900000000000000000000000 / 50800628462895704851201537896243801), (9394037606840000000000000000000000 / 118534799746756644652803588424568869), (9394010139440000000000000000000000 / 118534799746756644652803588424568869), (5549897809780000000000000000000000 / 355604399240269933958410765273706607), (1 / 1)], ![(19552712767 / 50000000000), (195526545571 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(53253328661 / 1000000000000), (248144368861 / 125000000000), (13746898629113 / 1000000000000), (39702842339 / 20000000000), (13313331739 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2080013708049 / 500000000000), (-2535131395333 / 1000000000000), (-507026863851 / 200000000000), (-520004919993 / 125000000000), (0 / 1)], ![(-938908968163 / 1000000000000), (-938911945243 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2932694966281 / 1000000000000), (685696971993 / 1000000000000), (104832529777 / 40000000000), (685690507017 / 1000000000000), (-1466347499149 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4160027416097 / 1000000000000), (-633782848833 / 250000000000), (-1267567159627 / 500000000000), (-4160039359943 / 1000000000000), (0 / 1)], ![(-469454484081 / 500000000000), (-469455972621 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-73317374157 / 25000000000), (342848485997 / 500000000000), (1310406622213 / 500000000000), (342845253509 / 500000000000), (-2932694998297 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4413248854333 / 1000000000000), (-8031631383247 / 1000000000000), (-853230096149 / 1000000000000), (-1394174928243 / 500000000000), (-1394174646249 / 500000000000), (-853230042993 / 1000000000000), (-1003955783973 / 125000000000), (-4413251356121 / 1000000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1103312213583 / 250000000000), (-1606326276649 / 200000000000), (-213307524037 / 250000000000), (-557669971297 / 200000000000), (-2788349292497 / 1000000000000), (-53326877687 / 62500000000), (-8031646271783 / 1000000000000), (-110331283903 / 25000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 1 25 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
