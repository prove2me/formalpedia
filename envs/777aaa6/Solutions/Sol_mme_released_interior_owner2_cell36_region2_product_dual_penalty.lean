-- Prove2me | solution 1 for mme_released_interior_owner2_cell36_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:40.381258+00:00
-- url     : https://prove2.me/submissions/ed551e90-044f-444c-8535-13ed3a51f85b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 2 36 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157461004353 / 1000000000000), (1903850835579 / 500000000000), (3807694248827 / 1000000000000), (157460963799 / 1000000000000)], ![(599554141709000000000000000000000000 / 7562118775831338224147618482731092419), (599553131484000000000000000000000000 / 7562118775831338224147618482731092419), (1 / 1), (1 / 1), (1 / 1)], ![(117256818497 / 200000000000), (20914220939 / 20000000000), (586281990571 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-924288721391 / 500000000000), (668512885601 / 500000000000), (267404764381 / 200000000000), (-462144425083 / 250000000000)], ![(-2534720409431 / 1000000000000), (-316840261799 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-26697540371 / 50000000000), (22348540867 / 500000000000), (-533954392573 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1848577442781 / 1000000000000), (1337025771203 / 1000000000000), (668511910953 / 500000000000), (-1848577700331 / 1000000000000)], ![(-253472040943 / 100000000000), (-2534722094391 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533950807419 / 1000000000000), (8939416347 / 200000000000), (-133488598143 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1731649030801 / 1000000000000), (-115299950579 / 100000000000), (-2458624458603 / 500000000000), (-2458626964881 / 500000000000), (-1152999241457 / 1000000000000), (-54114033747 / 31250000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4329122577 / 2500000000), (-1152999505789 / 1000000000000), (-983449783441 / 200000000000), (-4917253929761 / 1000000000000), (-72062452591 / 62500000000), (-1731649079903 / 1000000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 2 36 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
