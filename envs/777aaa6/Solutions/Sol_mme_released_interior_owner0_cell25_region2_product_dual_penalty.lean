-- Prove2me | solution 1 for mme_released_interior_owner0_cell25_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:26.806797+00:00
-- url     : https://prove2.me/submissions/6e977945-e3e4-4963-829c-ace405786f45

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(17469429763687500000000000000000000 / 1108845831998089375889133422584797169), (87513073792250000000000000000000000 / 1108845831998089375889133422584797169), (87512791664687500000000000000000000 / 1108845831998089375889133422584797169), (759537135000000000000000000000000 / 48210688347743016343005800981947703), (1 / 1)], ![(195732299263 / 500000000000), (24466461177 / 62500000000), (1 / 1), (1 / 1), (1 / 1)], ![(53199744081 / 1000000000000), (993151262153 / 500000000000), (13790251260199 / 1000000000000), (1986291228371 / 1000000000000), (53199740213 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4150622479631 / 1000000000000), (-1269643382693 / 500000000000), (-317411248653 / 125000000000), (-12970708783 / 3125000000), (0 / 1)], ![(-937860192861 / 1000000000000), (-468931654293 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1466850846577 / 500000000000), (343137441237 / 500000000000), (2623961912103 / 1000000000000), (343134597771 / 500000000000), (-2933701765861 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-415062247963 / 100000000000), (-507857353077 / 200000000000), (-2539289989223 / 1000000000000), (-4150626810559 / 1000000000000), (0 / 1)], ![(-46893009643 / 50000000000), (-187572661717 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2933701693153 / 1000000000000), (27450995299 / 40000000000), (327995239013 / 125000000000), (686269195543 / 1000000000000), (-146685088293 / 50000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4011092218721 / 500000000000), (-880443318537 / 200000000000), (-2790877762701 / 1000000000000), (-853188161867 / 1000000000000), (-426594134991 / 500000000000), (-558175683069 / 200000000000), (-1100553030229 / 250000000000), (-8022191813213 / 1000000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8022184437441 / 1000000000000), (-1100554148171 / 250000000000), (-27908777627 / 10000000000), (-426594080933 / 500000000000), (-853188269981 / 1000000000000), (-174429900959 / 62500000000), (-880442424183 / 200000000000), (-2005547953303 / 250000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 25 2 c : ℝ) / 1000000000000) ≤
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
