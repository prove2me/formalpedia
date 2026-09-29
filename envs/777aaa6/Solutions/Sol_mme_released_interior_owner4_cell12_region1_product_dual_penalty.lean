-- Prove2me | solution 1 for mme_released_interior_owner4_cell12_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:15:21.750172+00:00
-- url     : https://prove2.me/submissions/414de089-8442-4471-9dbf-e9f63d8ece56

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 4 12 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(195409171927 / 500000000000), (19540773289 / 50000000000), (1 / 1), (1 / 1), (1 / 1)], ![(4322367482187500000000000000000000 / 278155261603462027869175282415744519), (22073044844593750000000000000000000 / 278155261603462027869175282415744519), (22072880028578125000000000000000000 / 278155261603462027869175282415744519), (4322292768765625000000000000000000 / 278155261603462027869175282415744519), (1 / 1)], ![(26627750299 / 500000000000), (992272394949 / 500000000000), (1717324170027 / 125000000000), (1984516299553 / 1000000000000), (166423427 / 3125000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-469756210339 / 500000000000), (-93951978493 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-208218808617 / 50000000000), (-2533822278961 / 1000000000000), (-1266914872917 / 500000000000), (-416439345779 / 100000000000), (0 / 1)], ![(-2932654182113 / 1000000000000), (685389562851 / 1000000000000), (2620208906023 / 1000000000000), (685375206637 / 1000000000000), (-1466327128217 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-939512420677 / 1000000000000), (-939519784929 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4164376172339 / 1000000000000), (-31672778487 / 12500000000), (-2533829745833 / 1000000000000), (-4164393457789 / 1000000000000), (0 / 1)], ![(-91645443191 / 31250000000), (171347390713 / 250000000000), (327526113253 / 125000000000), (342687603319 / 500000000000), (-2932654256433 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4418520750653 / 1000000000000), (-8036542849467 / 1000000000000), (-213283289467 / 250000000000), (-2787959492997 / 1000000000000), (-557591993581 / 200000000000), (-106641657561 / 125000000000), (-4018283712117 / 500000000000), (-8629914679 / 1953125000)] : List ℚ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-1104630187663 / 250000000000), (-4018271424733 / 500000000000), (-853133157867 / 1000000000000), (-696989873249 / 250000000000), (-87123748997 / 31250000000), (-853133260487 / 1000000000000), (-8036567424233 / 1000000000000), (-4418516315647 / 1000000000000)] : List ℚ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 12 1 c : ℝ) / 1000000000000) ≤
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
