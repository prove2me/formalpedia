-- Prove2me | solution 1 for mme_released_interior_owner5_cell33_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:23:33.595975+00:00
-- url     : https://prove2.me/submissions/7abe0066-8061-4c74-952f-e800298e158d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 5 33 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53415015307 / 1000000000000), (2066884249603 / 1000000000000), (2555578890379 / 200000000000), (1033442250817 / 500000000000), (6676877517 / 125000000000)], ![(68171689077 / 250000000000), (1448023665779 / 1000000000000), (1448023369469 / 1000000000000), (272687607377 / 1000000000000), (1 / 1)], ![(9871663841875000000000000000000000 / 435809592513980762365966145667402339), (9871662530500000000000000000000000 / 435809592513980762365966145667402339), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929663387017 / 1000000000000), (726042279907 / 1000000000000), (2547716682003 / 1000000000000), (181510600461 / 250000000000), (-732415824153 / 250000000000)], ![(-1299431555371 / 1000000000000), (370199637599 / 1000000000000), (370199432969 / 1000000000000), (-649714217163 / 500000000000), (0 / 1)], ![(-757507403727 / 200000000000), (-1893768575739 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-366207923377 / 125000000000), (181510569977 / 250000000000), (636929170501 / 250000000000), (145208480369 / 200000000000), (-2929663296611 / 1000000000000)], ![(-129943155537 / 100000000000), (462749547 / 1250000000), (37019943297 / 100000000000), (-51977137373 / 40000000000), (0 / 1)], ![(-1893768509317 / 500000000000), (-3787537151477 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-1002078983981 / 125000000000), (-1345647489599 / 500000000000), (-869620903663 / 1000000000000), (-2180461586523 / 500000000000), (-2180463152487 / 500000000000), (-1391393331 / 1600000000), (-672823859649 / 250000000000), (-250519655351 / 31250000000)] : List ℚ).getD
    ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8016631871847 / 1000000000000), (-2691294979197 / 1000000000000), (-434810451831 / 500000000000), (-872184634609 / 200000000000), (-4360926304973 / 1000000000000), (-434810415937 / 500000000000), (-538259087719 / 200000000000), (-8016628971231 / 1000000000000)] : List ℚ).getD
    ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 5 33 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
