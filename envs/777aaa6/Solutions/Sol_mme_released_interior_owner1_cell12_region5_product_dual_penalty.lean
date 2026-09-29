-- Prove2me | solution 1 for mme_released_interior_owner1_cell12_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:25.800994+00:00
-- url     : https://prove2.me/submissions/03bd3ed8-f133-4eb4-a57d-656248e5cb3b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(389641283176000000000000000000000000 / 17908501829688780948801685943849127751), (389656693337000000000000000000000000 / 17908501829688780948801685943849127751), (1 / 1), (1 / 1), (1 / 1)], ![(283990527853 / 1000000000000), (1372226923841 / 1000000000000), (42883789971 / 31250000000), (35503074193 / 125000000000), (1 / 1)], ![(52706305593 / 1000000000000), (122463298243 / 62500000000), (14370444888589 / 1000000000000), (979784550089 / 500000000000), (26353375761 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3827804312491 / 1000000000000), (-1913882381831 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-157351799251 / 125000000000), (79108728003 / 250000000000), (19779657637 / 62500000000), (-251738889517 / 200000000000), (0 / 1)], ![(-91969380621 / 31250000000), (672644822171 / 1000000000000), (2665173659151 / 1000000000000), (42045287639 / 62500000000), (-2943011719269 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-382780431249 / 100000000000), (-3827764763661 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1258814394007 / 1000000000000), (316434912013 / 1000000000000), (316474522193 / 1000000000000), (-39334201487 / 31250000000), (0 / 1)], ![(-2943020179871 / 1000000000000), (168161205543 / 250000000000), (166573353697 / 62500000000), (26908984089 / 40000000000), (-735752929817 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([7, 2, 5, 12, 12, 5, 2, 7] : List ℤ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-882770787581 / 200000000000), (-423078065573 / 500000000000), (-11354579193 / 4000000000), (-8029630426951 / 1000000000000), (-1605895878429 / 200000000000), (-2838645419309 / 1000000000000), (-846156192497 / 1000000000000), (-441385455541 / 100000000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-275865871119 / 62500000000), (-169231226229 / 200000000000), (-2838644798249 / 1000000000000), (-160592608539 / 20000000000), (-501842462009 / 62500000000), (-709661354827 / 250000000000), (-52884762031 / 62500000000), (-4413854555409 / 1000000000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 12 5 c : ℝ) / 1000000000000) ≤
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
