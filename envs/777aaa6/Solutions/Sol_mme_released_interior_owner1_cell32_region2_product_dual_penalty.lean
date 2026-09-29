-- Prove2me | solution 1 for mme_released_interior_owner1_cell32_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:41.227281+00:00
-- url     : https://prove2.me/submissions/20196b11-d30b-407b-9239-df48222c7e69

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19512546212000000000000000000000000 / 9866092177925038128679120291763700979), (1166436599112500000000000000000000000 / 9866092177925038128679120291763700979), (8315395408536500000000000000000000000 / 9866092177925038128679120291763700979), (1166446374518500000000000000000000000 / 9866092177925038128679120291763700979), (19512549513500000000000000000000000 / 9866092177925038128679120291763700979)], ![(420359708039 / 1000000000000), (24353656861 / 31250000000), (13136350371 / 31250000000), (1 / 1), (1 / 1)], ![(201918449117 / 500000000000), (422333998637 / 500000000000), (201920125141 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1556450367643 / 250000000000), (-2135150386137 / 1000000000000), (-854975903 / 5000000000), (-2668927507 / 1250000000), (-3112900650687 / 500000000000)], ![(-173328897307 / 200000000000), (-124668679417 / 500000000000), (-866636151249 / 1000000000000), (0 / 1), (0 / 1)], ![(-45337209989 / 50000000000), (-84405815733 / 500000000000), (-181347179863 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6225801470571 / 1000000000000), (-266893798267 / 125000000000), (-170995180599 / 1000000000000), (-2135142005599 / 1000000000000), (-6225801301373 / 1000000000000)], ![(-433322243267 / 500000000000), (-249337358833 / 1000000000000), (-54164759453 / 62500000000), (0 / 1), (0 / 1)], ![(-906744199779 / 1000000000000), (-33762326293 / 200000000000), (-453367949657 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7999173521963 / 1000000000000), (-792649537071 / 250000000000), (-3291223667483 / 1000000000000), (-1944375537661 / 1000000000000), (-589144170899 / 1000000000000), (-1944375560419 / 1000000000000), (-1645611770503 / 500000000000), (-3170598144163 / 1000000000000), (-7999189987221 / 1000000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-3999586760981 / 500000000000), (-3170598148283 / 1000000000000), (-1645611833741 / 500000000000), (-97218776883 / 50000000000), (-294572085449 / 500000000000), (-972187780209 / 500000000000), (-658244708201 / 200000000000), (-1585299072081 / 500000000000), (-399959499361 / 50000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 32 2 c : ℝ) / 1000000000000) ≤
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
