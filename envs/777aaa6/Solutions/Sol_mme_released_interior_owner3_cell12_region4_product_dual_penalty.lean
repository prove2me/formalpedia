-- Prove2me | solution 1 for mme_released_interior_owner3_cell12_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:42.042169+00:00
-- url     : https://prove2.me/submissions/3bbc77b6-109f-46da-ae7f-8d77921db884

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 3 12 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(38965121979 / 100000000000), (48706333031 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(17757456427 / 62500000000), (27436754537 / 20000000000), (1371835800441 / 1000000000000), (142058917621 / 500000000000), (1 / 1)], ![(1756379629300000000000000000000000 / 596998950751733099892422063910477183), (65322276502900000000000000000000000 / 596998950751733099892422063910477183), (479211015737300000000000000000000000 / 596998950751733099892422063910477183), (65322078714500000000000000000000000 / 596998950751733099892422063910477183), (1756381039700000000000000000000000 / 596998950751733099892422063910477183)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-471251624111 / 500000000000), (-188500934793 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-314590262159 / 250000000000), (316151247417 / 1000000000000), (158074921581 / 500000000000), (-25167324281 / 20000000000), (0 / 1)], ![(-5828660694203 / 1000000000000), (-2212582236817 / 1000000000000), (-109887160777 / 500000000000), (-553146316177 / 250000000000), (-1457164972797 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-942503248221 / 1000000000000), (-235626168491 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-251672209727 / 200000000000), (158075623709 / 500000000000), (316149843163 / 1000000000000), (-1258366214049 / 1000000000000), (0 / 1)], ![(-2914330347101 / 500000000000), (-138286389801 / 62500000000), (-219774321553 / 1000000000000), (-2212585264707 / 1000000000000), (-5828659891187 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8029531582867 / 1000000000000), (-4413451699129 / 1000000000000), (-2838937067617 / 1000000000000), (-846127726611 / 1000000000000), (-846127748099 / 1000000000000), (-88716789547 / 31250000000), (-88269019747 / 20000000000), (-2007381047401 / 250000000000)] : List ℚ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4014765791433 / 500000000000), (-551681462391 / 125000000000), (-88716783363 / 31250000000), (-84612772661 / 100000000000), (-423063874049 / 500000000000), (-2838937265503 / 1000000000000), (-4413450987349 / 1000000000000), (-8029524189603 / 1000000000000)] : List ℚ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 12 4 c : ℝ) / 1000000000000) ≤
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
