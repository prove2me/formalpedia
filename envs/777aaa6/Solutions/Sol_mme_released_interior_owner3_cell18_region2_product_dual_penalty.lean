-- Prove2me | solution 1 for mme_released_interior_owner3_cell18_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:29.818823+00:00
-- url     : https://prove2.me/submissions/6fe4e429-f5e1-4823-b7c4-ee61ff3902fe

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(573311492273 / 1000000000000), (213745507617 / 200000000000), (286671023009 / 500000000000), (1 / 1), (1 / 1)], ![(592735932083 / 1000000000000), (592751615647 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (21582151600000000000000000000000000 / 1105478861250613221828472481078816889), (3922442485799000000000000000000000000 / 7738352028754292552799307367551718223), (560364564697000000000000000000000000 / 1105478861250613221828472481078816889), (151076430002000000000000000000000000 / 7738352028754292552799307367551718223)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-278163046721 / 500000000000), (66468724051 / 1000000000000), (-69534100177 / 125000000000), (0 / 1), (0 / 1)], ![(-4184050301 / 8000000000), (-522979828361 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-984041805097 / 250000000000), (-42467137867 / 62500000000), (-5435570387 / 8000000000), (-3936158160019 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-556326093441 / 1000000000000), (16617181013 / 250000000000), (-111254560283 / 200000000000), (0 / 1), (0 / 1)], ![(-65375785953 / 125000000000), (-13074495709 / 25000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3936167220387 / 1000000000000), (-679474205871 / 1000000000000), (-339723149187 / 500000000000), (-1968079080009 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-2507709925101 / 500000000000), (-1135985310181 / 1000000000000), (-1758753294913 / 1000000000000), (-70350088807 / 40000000000), (-227196772389 / 200000000000), (-1253872635289 / 250000000000)] : List ℚ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5015419850201 / 1000000000000), (-56799265509 / 50000000000), (-27480520233 / 15625000000), (-879376110087 / 500000000000), (-141997982743 / 125000000000), (-1003098108231 / 200000000000)] : List ℚ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 3 18 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
