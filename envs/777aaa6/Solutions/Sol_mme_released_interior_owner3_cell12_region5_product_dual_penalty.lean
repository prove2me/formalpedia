-- Prove2me | solution 1 for mme_released_interior_owner3_cell12_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:42.861876+00:00
-- url     : https://prove2.me/submissions/d26a785d-a511-4fab-8ee6-e462a5ef9a75

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 3 12 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(390830608897 / 1000000000000), (12213458341 / 31250000000), (1 / 1), (1 / 1), (1 / 1)], ![(55312316157 / 200000000000), (5520788557 / 3906250000), (70666108493 / 50000000000), (276560931319 / 1000000000000), (1 / 1)], ![(26630642804500000000000000000000000 / 8899630362776624671110886952493403861), (991748006681500000000000000000000000 / 8899630362776624671110886952493403861), (6864840208318500000000000000000000000 / 8899630362776624671110886952493403861), (991747931516000000000000000000000000 / 8899630362776624671110886952493403861), (26630646744500000000000000000000000 / 8899630362776624671110886952493403861)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-469740519097 / 500000000000), (-469740444877 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1285321767501 / 1000000000000), (10810714691 / 31250000000), (17297154093 / 50000000000), (-1285324115863 / 1000000000000), (0 / 1)], ![(-1452925621173 / 250000000000), (-1097147986547 / 500000000000), (-129798490469 / 500000000000), (-438859209777 / 200000000000), (-5811702336743 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-939481038193 / 1000000000000), (-939480889753 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-514128707 / 400000000), (345942870113 / 1000000000000), (345943081861 / 1000000000000), (-642662057931 / 500000000000), (0 / 1)], ![(-5811702484691 / 1000000000000), (-2194295973093 / 1000000000000), (-259596980937 / 1000000000000), (-548574012221 / 250000000000), (-2905851168371 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-401825374553 / 50000000000), (-441910112711 / 100000000000), (-278783378099 / 100000000000), (-106641867159 / 125000000000), (-426567500289 / 500000000000), (-1393917108481 / 500000000000), (-110477467653 / 25000000000), (-4018252570649 / 500000000000)] : List ℚ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8036507491059 / 1000000000000), (-4419101127109 / 1000000000000), (-2787833780989 / 1000000000000), (-853134937271 / 1000000000000), (-853135000577 / 1000000000000), (-2787834216961 / 1000000000000), (-4419098706119 / 1000000000000), (-8036505141297 / 1000000000000)] : List ℚ).getD
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
        (splitWeight 3 12 5 c : ℝ) / 1000000000000) ≤
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
