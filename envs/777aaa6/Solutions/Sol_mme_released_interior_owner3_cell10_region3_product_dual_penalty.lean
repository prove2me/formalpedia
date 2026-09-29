-- Prove2me | solution 1 for mme_released_interior_owner3_cell10_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:33.160285+00:00
-- url     : https://prove2.me/submissions/def47b36-a191-43ae-8142-307f553f11eb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 3 10 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(850822789817 / 1000000000000), (34032529499 / 40000000000), (1 / 1), (1 / 1), (1 / 1)], ![(850822838343 / 1000000000000), (212703321969 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (299214445628000000000000000000000000 / 1888198512780793081773582354718486197), (1004983517631500000000000000000000000 / 1888198512780793081773582354718486197), (299219010966500000000000000000000000 / 1888198512780793081773582354718486197)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161551409677 / 1000000000000), (-161562636921 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-80775676321 / 500000000000), (-161562577683 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-1842217959883 / 1000000000000), (-157663016417 / 250000000000), (-460550675563 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-40387852419 / 250000000000), (-4039065923 / 25000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161551352641 / 1000000000000), (-80781288841 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-921108979941 / 500000000000), (-630652065667 / 1000000000000), (-1842202702251 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-541335793621 / 250000000000), (-953766053027 / 1000000000000), (-95376605523 / 100000000000), (-2165305464569 / 1000000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2165343174483 / 1000000000000), (-476883026513 / 500000000000), (-953766055229 / 1000000000000), (-270663183071 / 125000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 3 10 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
