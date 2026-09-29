-- Prove2me | solution 1 for mme_released_interior_owner4_cell15_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:16:10.668748+00:00
-- url     : https://prove2.me/submissions/18e12576-c3be-4b13-97ee-8d457bf5c4f1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 4 15 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(425956355653 / 500000000000), (106489091137 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (75512371740125000000000000000000000 / 469452096734666960335347721453838913), (247910767324625000000000000000000000 / 469452096734666960335347721453838913), (75512369884375000000000000000000000 / 469452096734666960335347721453838913)], ![(34076508057 / 40000000000), (851912719173 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-160271208921 / 1000000000000), (-80135594019 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-1827269756121 / 1000000000000), (-19953043463 / 31250000000), (-228408722587 / 125000000000)], ![(-160271220519 / 1000000000000), (-80135599843 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4006780223 / 25000000000), (-160271188037 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-45681743903 / 25000000000), (-127699478163 / 200000000000), (-365453956139 / 200000000000)], ![(-80135610259 / 500000000000), (-32054239937 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 15) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-2147812143843 / 1000000000000), (-239759949843 / 250000000000), (-479519899711 / 500000000000), (-268476526267 / 125000000000)] : List ℚ).getD
    ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-1073906071921 / 500000000000), (-959039799371 / 1000000000000), (-959039799421 / 1000000000000), (-429562442027 / 200000000000)] : List ℚ).getD
    ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 15) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 15 =>
        (splitWeight 4 15 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 15, ∏ i, weights i (c.val i) ≤ 1 := by
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
