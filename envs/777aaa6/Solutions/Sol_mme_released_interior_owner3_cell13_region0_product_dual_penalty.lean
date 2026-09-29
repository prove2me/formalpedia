-- Prove2me | solution 1 for mme_released_interior_owner3_cell13_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:44.040681+00:00
-- url     : https://prove2.me/submissions/66f09804-a823-4003-84d1-8b801065e2df

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 3 13 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(393015666223 / 1000000000000), (125765133 / 320000000), (1 / 1), (1 / 1), (1 / 1)], ![(5331901033 / 100000000000), (254208528617 / 125000000000), (6577781400893 / 500000000000), (2033671737379 / 1000000000000), (1666219111 / 31250000000)], ![(5471028863540000000000000000000000 / 352021669734395430036089528170937391), (28732751620900000000000000000000000 / 352021669734395430036089528170937391), (28732780293040000000000000000000000 / 352021669734395430036089528170937391), (202630917040000000000000000000000 / 13037839619792423334669982524849533), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-186781160949 / 200000000000), (-933904852107 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2931462344797 / 1000000000000), (88730146463 / 125000000000), (644211173981 / 250000000000), (354921448441 / 500000000000), (-1465731160939 / 500000000000)], ![(-520528255581 / 125000000000), (-501131018373 / 200000000000), (-100226163759 / 40000000000), (-4164224966873 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-116738225593 / 125000000000), (-466952426053 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-732865586199 / 250000000000), (141968234341 / 200000000000), (103073787837 / 40000000000), (709842896883 / 1000000000000), (-2931462321877 / 1000000000000)], ![(-4164226044647 / 1000000000000), (-313206886483 / 125000000000), (-1252827046987 / 500000000000), (-520528120859 / 125000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-1605918833977 / 200000000000), (-4388287999853 / 1000000000000), (-2729717999729 / 1000000000000), (-862715248047 / 1000000000000), (-172543040559 / 200000000000), (-2729717774369 / 1000000000000), (-4388289599921 / 1000000000000), (-8029592164853 / 1000000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-2007398542471 / 250000000000), (-1097071999963 / 250000000000), (-170607374983 / 62500000000), (-431357624023 / 500000000000), (-431357601397 / 500000000000), (-85303680449 / 31250000000), (-54853619999 / 12500000000), (-2007398041213 / 250000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 3 13 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
