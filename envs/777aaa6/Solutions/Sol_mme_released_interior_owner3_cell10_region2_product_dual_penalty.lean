-- Prove2me | solution 1 for mme_released_interior_owner3_cell10_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:32.493925+00:00
-- url     : https://prove2.me/submissions/44101db3-89c9-49dc-87d7-902588c18842

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 3 10 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(212633537219 / 250000000000), (849554631519 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(53166220701 / 62500000000), (850587994443 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (298729792313000000000000000000000000 / 1889358980339390110692128207672074689), (335925063195000000000000000000000000 / 629786326779796703564042735890691563), (298695552590500000000000000000000000 / 1889358980339390110692128207672074689)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161890716423 / 1000000000000), (-81521514867 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-16174331129 / 100000000000), (-40456852621 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-1844453426519 / 1000000000000), (-157123122283 / 250000000000), (-1844568050791 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-80945358211 / 500000000000), (-163043029733 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161743311289 / 1000000000000), (-161827410483 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-922226713259 / 500000000000), (-628492489131 / 1000000000000), (-184456805079 / 100000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2169323866737 / 1000000000000), (-952210616039 / 1000000000000), (-953278830153 / 1000000000000), (-433640415701 / 200000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-135582741671 / 62500000000), (-476105308019 / 500000000000), (-119159853769 / 125000000000), (-271025259813 / 125000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 3 10 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
