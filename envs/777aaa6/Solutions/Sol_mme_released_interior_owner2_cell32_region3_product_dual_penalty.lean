-- Prove2me | solution 1 for mme_released_interior_owner2_cell32_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:46:53.295302+00:00
-- url     : https://prove2.me/submissions/e2292902-b34c-440c-9f6a-0df619cac949

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 2 32 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(3893542279 / 100000000000), (18368510819 / 7812500000), (16578287351829 / 1000000000000), (2351340936191 / 1000000000000), (19467786921 / 500000000000)], ![(208487415804000000000000000000000000 / 9852008190564009922470843136331538919), (396141990694500000000000000000000000 / 9852008190564009922470843136331538919), (208502507783500000000000000000000000 / 9852008190564009922470843136331538919), (1 / 1), (1 / 1)], ![(203802287141 / 500000000000), (415232481987 / 500000000000), (203817038171 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-649170166229 / 200000000000), (170982562991 / 200000000000), (1404046924171 / 500000000000), (213746444141 / 250000000000), (-3245846951601 / 1000000000000)], ![(-24097199419 / 6250000000), (-642731576251 / 200000000000), (-120483735053 / 31250000000), (0 / 1), (0 / 1)], ![(-897457755219 / 1000000000000), (-37153907497 / 200000000000), (-897385378719 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-405731353893 / 125000000000), (213728203739 / 250000000000), (2808093848343 / 1000000000000), (170997155313 / 200000000000), (-8114617379 / 2500000000)], ![(-3855551907039 / 1000000000000), (-1606828940627 / 500000000000), (-771095904339 / 200000000000), (0 / 1), (0 / 1)], ![(-448728877609 / 500000000000), (-46442384371 / 250000000000), (-448692689359 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-486210859401 / 250000000000), (-318633566733 / 100000000000), (-7998856612627 / 1000000000000), (-3256130444341 / 1000000000000), (-147833392599 / 250000000000), (-1628064930297 / 500000000000), (-499919733173 / 62500000000), (-1593168122439 / 500000000000), (-486210857097 / 250000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944843437603 / 1000000000000), (-3186335667329 / 1000000000000), (-3999428306313 / 500000000000), (-162806522217 / 50000000000), (-295666785197 / 500000000000), (-3256129860593 / 1000000000000), (-7998715730767 / 1000000000000), (-3186336244877 / 1000000000000), (-1944843428387 / 1000000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 2 32 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
