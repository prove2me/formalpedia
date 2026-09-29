-- Prove2me | solution 1 for mme_released_interior_owner5_cell10_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:20:34.0458+00:00
-- url     : https://prove2.me/submissions/cf8f19b3-3db0-4145-bdf9-2121b676826e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 5 10 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(42523048423 / 50000000000), (13277047299 / 15625000000), (1 / 1), (1 / 1), (1 / 1)], ![(26531061521 / 31250000000), (425216491029 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (14931814787275000000000000000000000 / 94428834592453777483917528219439503), (50430895712525000000000000000000000 / 94428834592453777483917528219439503), (4977674884725000000000000000000000 / 31476278197484592494639176073146501)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161976760663 / 1000000000000), (-162835418239 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-81851598367 / 500000000000), (-162009668537 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-230544040059 / 125000000000), (-62724248027 / 100000000000), (-1844271297643 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-80988380331 / 500000000000), (-81417709119 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-163703196733 / 1000000000000), (-20251208567 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-1844352320471 / 1000000000000), (-627242480269 / 1000000000000), (-922135648821 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2169197407253 / 1000000000000), (-953781095243 / 1000000000000), (-951228909467 / 1000000000000), (-2169951255039 / 1000000000000)] : List ℚ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-542299351813 / 250000000000), (-476890547621 / 500000000000), (-475614454733 / 500000000000), (-1084975627519 / 500000000000)] : List ℚ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 10 0 c : ℝ) / 1000000000000) ≤
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
