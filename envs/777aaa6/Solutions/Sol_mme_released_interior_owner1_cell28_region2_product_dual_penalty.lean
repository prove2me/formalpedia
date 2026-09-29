-- Prove2me | solution 1 for mme_released_interior_owner1_cell28_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:36.610034+00:00
-- url     : https://prove2.me/submissions/88458275-0be1-4a68-a6e9-e6d4e963edd1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 1 28 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(138089779307000000000000000000000000 / 8768651866725880577389319023892179993), (712654298446500000000000000000000000 / 8768651866725880577389319023892179993), (712654164755500000000000000000000000 / 8768651866725880577389319023892179993), (138089730027500000000000000000000000 / 8768651866725880577389319023892179993), (1 / 1)], ![(10660873423 / 200000000000), (407091785593 / 200000000000), (3296198843229 / 250000000000), (2035458198859 / 1000000000000), (26652183593 / 500000000000)], ![(24608450977 / 62500000000), (393735144023 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-166041372169 / 40000000000), (-1254970952309 / 500000000000), (-1254971046107 / 500000000000), (-4151034661091 / 1000000000000), (0 / 1)], ![(-366467127069 / 125000000000), (44420081931 / 62500000000), (644766074999 / 250000000000), (355360476347 / 500000000000), (-146586850761 / 50000000000)], ![(-932076637149 / 1000000000000), (-46603840951 / 50000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-129719822007 / 31250000000), (-2509941904617 / 1000000000000), (-2509942092213 / 1000000000000), (-415103466109 / 100000000000), (0 / 1)], ![(-2931737016551 / 1000000000000), (710721310897 / 1000000000000), (2579064299997 / 1000000000000), (142144190539 / 200000000000), (-2931737015219 / 1000000000000)], ![(-233019159287 / 250000000000), (-932076819019 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4007423978863 / 500000000000), (-4372390170577 / 1000000000000), (-2731297589071 / 1000000000000), (-431477211819 / 500000000000), (-862954429367 / 1000000000000), (-136564880017 / 50000000000), (-273274374207 / 62500000000), (-4007424248137 / 500000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-320593918309 / 40000000000), (-273274385661 / 62500000000), (-273129758907 / 100000000000), (-862954423637 / 1000000000000), (-431477214683 / 500000000000), (-2731297600339 / 1000000000000), (-4372389987311 / 1000000000000), (-8014848496273 / 1000000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 1 28 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
