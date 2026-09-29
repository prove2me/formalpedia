-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:14.534011+00:00
-- url     : https://prove2.me/submissions/d3d8b9f5-00bd-4e1d-9c39-7946f7c8517b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(405800387701 / 1000000000000), (51713411919 / 62500000000), (81169932317 / 200000000000), (1 / 1), (1 / 1)], ![(12947793068000000000000000000000000 / 6651504336371635704535120998526838757), (769661145778000000000000000000000000 / 6651504336371635704535120998526838757), (17062674095129000000000000000000000000 / 19954513009114907113605362995580516271), (769755423310000000000000000000000000 / 6651504336371635704535120998526838757), (38843586583000000000000000000000000 / 19954513009114907113605362995580516271)], ![(25991029657 / 62500000000), (492145847 / 625000000), (415906975551 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-440377879 / 488281250), (-189449390709 / 1000000000000), (-450886239809 / 500000000000), (0 / 1), (0 / 1)], ![(-62416729699 / 10000000000), (-2156647976493 / 1000000000000), (-78281028739 / 500000000000), (-269565686467 / 125000000000), (-780208453883 / 125000000000)], ![(-219353772861 / 250000000000), (-238976540181 / 1000000000000), (-877293660191 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-901893896191 / 1000000000000), (-47362347677 / 250000000000), (-901772479617 / 1000000000000), (0 / 1), (0 / 1)], ![(-6241672969899 / 1000000000000), (-539161994123 / 250000000000), (-156562057477 / 1000000000000), (-431305098347 / 200000000000), (-6241667631063 / 1000000000000)], ![(-877415091443 / 1000000000000), (-11948827009 / 50000000000), (-87729366019 / 100000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4010369554147 / 500000000000), (-100730969519 / 31250000000), (-1648698499641 / 500000000000), (-15485996917 / 8000000000), (-58498798837 / 100000000000), (-15123043967 / 7812500000), (-1648697962557 / 500000000000), (-3223389976663 / 1000000000000), (-4010488309033 / 500000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020739108293 / 1000000000000), (-3223391024607 / 1000000000000), (-3297396999281 / 1000000000000), (-60492175457 / 31250000000), (-584987988369 / 1000000000000), (-77429985111 / 40000000000), (-3297395925113 / 1000000000000), (-1611694988331 / 500000000000), (-1604195323613 / 200000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 21 0 c : ℝ) / 1000000000000) ≤
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
