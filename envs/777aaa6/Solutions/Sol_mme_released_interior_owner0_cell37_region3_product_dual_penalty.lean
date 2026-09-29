-- Prove2me | solution 1 for mme_released_interior_owner0_cell37_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:16.470229+00:00
-- url     : https://prove2.me/submissions/4836cfc2-3ac7-4252-a181-fa8bd2f69964

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78957310346000000000000000000000000 / 3776237603207663322537742070245171023), (1899352530593500000000000000000000000 / 3776237603207663322537742070245171023), (1899577940177500000000000000000000000 / 3776237603207663322537742070245171023), (78959694222500000000000000000000000 / 3776237603207663322537742070245171023)], ![(293153041169 / 500000000000), (1046826965627 / 1000000000000), (117287802383 / 200000000000), (1 / 1), (1 / 1)], ![(149913407069 / 250000000000), (299860635917 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-193378805941 / 50000000000), (-343607558079 / 500000000000), (-137419289227 / 200000000000), (-3867545927309 / 1000000000000)], ![(-533913300961 / 1000000000000), (22881825699 / 500000000000), (-533686602801 / 1000000000000), (0 / 1), (0 / 1)], ![(-511403076667 / 1000000000000), (-102258055729 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3867576118819 / 1000000000000), (-687215116157 / 1000000000000), (-343548223067 / 500000000000), (-966886481827 / 250000000000)], ![(-3336958131 / 6250000000), (45763651399 / 1000000000000), (-1334216507 / 2500000000), (0 / 1), (0 / 1)], ![(-255701538333 / 500000000000), (-127822569661 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4912553000199 / 1000000000000), (-576370871703 / 500000000000), (-1732304795623 / 1000000000000), (-1732300025741 / 1000000000000), (-576367935701 / 500000000000), (-2456431152499 / 500000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-2456276500099 / 500000000000), (-230548348681 / 200000000000), (-866152397811 / 500000000000), (-86615001287 / 50000000000), (-1152735871401 / 1000000000000), (-4912862304997 / 1000000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 0 37 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
