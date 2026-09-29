-- Prove2me | solution 1 for mme_released_interior_owner2_cell12_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:55.332226+00:00
-- url     : https://prove2.me/submissions/9859fe6c-ba0b-4e80-9d9d-275d1821ac90

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 2 12 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(78161820517 / 200000000000), (39080971387 / 100000000000), (1 / 1), (1 / 1), (1 / 1)], ![(27658200177100000000000000000000000 / 1780225310175438125076175192378777961), (141289116247600000000000000000000000 / 1780225310175438125076175192378777961), (141289344252200000000000000000000000 / 1780225310175438125076175192378777961), (27658258517400000000000000000000000 / 1780225310175438125076175192378777961), (1 / 1)], ![(3328730907 / 62500000000), (992222094977 / 500000000000), (6868438655523 / 500000000000), (79377992571 / 40000000000), (6657461793 / 125000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-939536066903 / 1000000000000), (-939534502751 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2082286479713 / 500000000000), (-2533686953151 / 1000000000000), (-158355333713 / 62500000000), (-4164570850097 / 1000000000000), (0 / 1)], ![(-3665719293 / 1250000000), (685338869869 / 1000000000000), (1310041995513 / 500000000000), (68534170407 / 100000000000), (-1466287718777 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-469768033451 / 500000000000), (-3758138011 / 4000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-166582918377 / 40000000000), (-50673739063 / 20000000000), (-2533685339407 / 1000000000000), (-260285678131 / 62500000000), (0 / 1)], ![(-2932575434399 / 1000000000000), (68533886987 / 100000000000), (2620083991027 / 1000000000000), (685341704071 / 1000000000000), (-2932575437553 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4018342231291 / 500000000000), (-2209382879067 / 500000000000), (-557576263197 / 200000000000), (-853137464877 / 1000000000000), (-426568707641 / 500000000000), (-2787880972289 / 1000000000000), (-2209384023553 / 500000000000), (-1607336157777 / 200000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8036684462581 / 1000000000000), (-4418765758133 / 1000000000000), (-174242582249 / 62500000000), (-213284366219 / 250000000000), (-853137415281 / 1000000000000), (-680635003 / 244140625), (-883753609421 / 200000000000), (-2009170197221 / 250000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 12 0 c : ℝ) / 1000000000000) ≤
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
