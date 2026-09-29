-- Prove2me | solution 1 for mme_released_interior_owner3_cell31_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:39.431779+00:00
-- url     : https://prove2.me/submissions/d6970408-2f09-4695-a25a-ae167fdeb940

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 3 31 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(26663033023 / 500000000000), (508512260163 / 250000000000), (820788214053 / 62500000000), (2034041882417 / 1000000000000), (13331511991 / 250000000000)], ![(392897915869 / 1000000000000), (15347549 / 39062500), (1 / 1), (1 / 1), (1 / 1)], ![(272910009957000000000000000000000000 / 17608779657702263037433198691376292219), (130904515689000000000000000000000000 / 1600798150700205730675745335579662929), (1439947277792000000000000000000000000 / 17608779657702263037433198691376292219), (38986899646000000000000000000000000 / 2515539951100323291061885527339470317), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2931330023339 / 1000000000000), (88753550973 / 125000000000), (2575098558473 / 1000000000000), (710024888573 / 1000000000000), (-2931330362423 / 1000000000000)], ![(-467102728457 / 500000000000), (-1459698657 / 1562500000), (0 / 1), (0 / 1), (0 / 1)], ![(-2083505396923 / 500000000000), (-312973682309 / 125000000000), (-1251895560789 / 500000000000), (-416701706859 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1465665011669 / 500000000000), (142005681557 / 200000000000), (1287549279237 / 500000000000), (355012444287 / 500000000000), (-1465665181211 / 500000000000)], ![(-934205456913 / 1000000000000), (-934207140479 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-833402158769 / 200000000000), (-2503789458471 / 1000000000000), (-2503791121577 / 1000000000000), (-4167017068589 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4391193045749 / 1000000000000), (-8032546614087 / 1000000000000), (-431449020239 / 500000000000), (-2727970026813 / 1000000000000), (-272796985427 / 100000000000), (-431449010009 / 500000000000), (-4016277116491 / 500000000000), (-439119411769 / 100000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-1097798261437 / 250000000000), (-4016273307043 / 500000000000), (-862898040477 / 1000000000000), (-681992506703 / 250000000000), (-2727969854269 / 1000000000000), (-862898020017 / 1000000000000), (-8032554232981 / 1000000000000), (-4391194117689 / 1000000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 3 31 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
