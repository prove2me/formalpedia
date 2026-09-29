-- Prove2me | solution 1 for mme_released_interior_owner3_cell32_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:13:04.147902+00:00
-- url     : https://prove2.me/submissions/aa4fc38c-af24-459e-b5e3-6018fd69a79c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19512558971 / 500000000000), (2332774123259 / 1000000000000), (16629847749233 / 1000000000000), (2332716907737 / 1000000000000), (4878137317 / 125000000000)], ![(5254778503 / 12500000000), (389743307629 / 500000000000), (84074411817 / 200000000000), (1 / 1), (1 / 1)], ![(5048540077250000000000000000000000 / 246668295904193307923242371506272289), (1508183480850000000000000000000000 / 35238327986313329703320338786610327), (5048417784225000000000000000000000 / 246668295904193307923242371506272289), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3243549790369 / 1000000000000), (847058170203 / 1000000000000), (112447965519 / 40000000000), (423516821543 / 500000000000), (-3243550287639 / 1000000000000)], ![(-86659079063 / 100000000000), (-49823952313 / 200000000000), (-866615104879 / 1000000000000), (0 / 1), (0 / 1)], ![(-486118174331 / 125000000000), (-630245683927 / 200000000000), (-777793923677 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-101360930949 / 31250000000), (211764542551 / 250000000000), (351399892247 / 125000000000), (847033643087 / 1000000000000), (-1621775143819 / 500000000000)], ![(-866590790629 / 1000000000000), (-62279940391 / 250000000000), (-433307552439 / 500000000000), (0 / 1), (0 / 1)], ![(-3888945394647 / 1000000000000), (-1575614209817 / 500000000000), (-243060601149 / 62500000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-972180685361 / 500000000000), (-3291031477877 / 1000000000000), (-7999086473269 / 1000000000000), (-3170785323049 / 1000000000000), (-589149043223 / 1000000000000), (-99087049951 / 31250000000), (-7999134513371 / 1000000000000), (-411378905627 / 125000000000), (-972180630933 / 500000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944361370721 / 1000000000000), (-822757869469 / 250000000000), (-1999771618317 / 250000000000), (-396348165381 / 125000000000), (-294574521611 / 500000000000), (-3170785598431 / 1000000000000), (-799913451337 / 100000000000), (-658206249003 / 200000000000), (-388872252373 / 200000000000)] : List ℚ).getD
    ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 32 0 c : ℝ) / 1000000000000) ≤
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
