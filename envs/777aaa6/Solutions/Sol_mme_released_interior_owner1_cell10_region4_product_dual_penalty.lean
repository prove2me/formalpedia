-- Prove2me | solution 1 for mme_released_interior_owner1_cell10_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:26.856245+00:00
-- url     : https://prove2.me/submissions/8585b57d-8187-48a3-8804-9b702824e7bc

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 1 10 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(169720702378400000000000000000000000 / 754629336289902216876568960647440273), (169791692218600000000000000000000000 / 754629336289902216876568960647440273), (1 / 1), (1 / 1), (1 / 1)], ![(272231289 / 320000000), (42546714913 / 50000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (299302781187 / 500000000000), (2011560688301 / 1000000000000), (75378802997 / 125000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-746036262303 / 500000000000), (-46614198049 / 31250000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5052155113 / 31250000000), (-6456814349 / 40000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-256576195651 / 500000000000), (698910882621 / 1000000000000), (-505787629173 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-298414504921 / 200000000000), (-1491654337567 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-32333792723 / 200000000000), (-40355089681 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-513152391301 / 1000000000000), (349455441311 / 500000000000), (-126446907293 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-954582000707 / 1000000000000), (-539882279349 / 250000000000), (-2166227087593 / 1000000000000), (-477206209281 / 500000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-477291000353 / 500000000000), (-431905823479 / 200000000000), (-270778385949 / 125000000000), (-954412418561 / 1000000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 10 4 c : ℝ) / 1000000000000) ≤
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
