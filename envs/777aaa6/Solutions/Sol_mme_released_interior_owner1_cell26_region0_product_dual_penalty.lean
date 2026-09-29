-- Prove2me | solution 1 for mme_released_interior_owner1_cell26_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:28.526948+00:00
-- url     : https://prove2.me/submissions/c1d47377-4a5b-4acd-bb3e-9f9594d95122

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(165507925580000000000000000000000000 / 16223327254733398328718773804503839433), (2475716185301000000000000000000000000 / 16223327254733398328718773804503839433), (2475817074039000000000000000000000000 / 16223327254733398328718773804503839433), (165527397309000000000000000000000000 / 16223327254733398328718773804503839433), (1 / 1)], ![(443568514343 / 1000000000000), (26535924051 / 31250000000), (13862642269 / 31250000000), (1 / 1), (1 / 1)], ![(169669533059 / 1000000000000), (120669947821 / 50000000000), (1206748270441 / 500000000000), (33938232117 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2292593178553 / 500000000000), (-375984087707 / 200000000000), (-1879879688031 / 1000000000000), (-1146267178927 / 250000000000), (0 / 1)], ![(-812903003611 / 1000000000000), (-81759968327 / 500000000000), (-203205440173 / 250000000000), (0 / 1), (0 / 1)], ![(-886951328493 / 500000000000), (440518054623 / 500000000000), (5506728393 / 6250000000), (-1773775196579 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-917037271421 / 200000000000), (-939960219267 / 500000000000), (-187987968803 / 100000000000), (-4585068715707 / 1000000000000), (0 / 1)], ![(-81290300361 / 100000000000), (-163519936653 / 1000000000000), (-812821760691 / 1000000000000), (0 / 1), (0 / 1)], ![(-354780531397 / 200000000000), (881036109247 / 1000000000000), (881076542881 / 1000000000000), (-886887598289 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4520928922323 / 1000000000000), (-6493270590527 / 1000000000000), (-1811172814279 / 1000000000000), (-581251583623 / 500000000000), (-4470399394099 / 1000000000000), (-1117601211379 / 250000000000), (-290625712917 / 250000000000), (-226396609129 / 125000000000), (-6493280402343 / 1000000000000), (-904186587083 / 200000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2260464461161 / 500000000000), (-3246635295263 / 500000000000), (-905586407139 / 500000000000), (-232500633449 / 200000000000), (-2235199697049 / 500000000000), (-894080969103 / 200000000000), (-1162502851667 / 1000000000000), (-1811172873031 / 1000000000000), (-3246640201171 / 500000000000), (-2260466467707 / 500000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 1 26 0 c : ℝ) / 1000000000000) ≤
          (1672 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1672 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1672 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
