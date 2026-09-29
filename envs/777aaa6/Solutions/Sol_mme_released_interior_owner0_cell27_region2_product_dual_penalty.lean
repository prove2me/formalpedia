-- Prove2me | solution 1 for mme_released_interior_owner0_cell27_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:57.980831+00:00
-- url     : https://prove2.me/submissions/f8a10e65-2a0c-4b3b-8637-8f9498a40b90

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(171185242345000000000000000000000000 / 16180500027350955439977696226019074551), (2393558586671000000000000000000000000 / 16180500027350955439977696226019074551), (2393525417396000000000000000000000000 / 16180500027350955439977696226019074551), (171178176638000000000000000000000000 / 16180500027350955439977696226019074551), (1 / 1)], ![(164977235613 / 1000000000000), (2487014408629 / 1000000000000), (621744984087 / 250000000000), (164970495589 / 1000000000000), (1 / 1)], ![(221946924603 / 500000000000), (84997045827 / 100000000000), (443881824021 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2274407917719 / 500000000000), (-477756402059 / 250000000000), (-238879933257 / 125000000000), (-4548857111501 / 1000000000000), (0 / 1)], ![(-900973890291 / 500000000000), (455541479191 / 500000000000), (911069097377 / 1000000000000), (-1801988635683 / 1000000000000), (0 / 1)], ![(-812169823499 / 1000000000000), (-162553685079 / 1000000000000), (-812196914093 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4548815835437 / 1000000000000), (-382205121647 / 200000000000), (-382207893211 / 200000000000), (-9097714223 / 2000000000), (0 / 1)], ![(-1801947780581 / 1000000000000), (911082958383 / 1000000000000), (455534548689 / 500000000000), (-900994317841 / 500000000000), (0 / 1)], ![(-406084911749 / 500000000000), (-81276842539 / 500000000000), (-203049228523 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-2226802576519 / 500000000000), (-810623845773 / 125000000000), (-1811616930801 / 1000000000000), (-581323355337 / 500000000000), (-283070765981 / 62500000000), (-283070771727 / 62500000000), (-1162646707553 / 1000000000000), (-362323511741 / 200000000000), (-3242495594077 / 500000000000), (-278350342319 / 62500000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4453605153037 / 1000000000000), (-6484990766183 / 1000000000000), (-4529042327 / 2500000000), (-1162646710673 / 1000000000000), (-905826451139 / 200000000000), (-4529132347631 / 1000000000000), (-36332709611 / 31250000000), (-113226097419 / 62500000000), (-6484991188153 / 1000000000000), (-4453605477103 / 1000000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 0 27 2 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1592 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1592 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
