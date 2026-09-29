-- Prove2me | solution 1 for mme_released_interior_owner3_cell19_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:34.287406+00:00
-- url     : https://prove2.me/submissions/f3a8bf34-2b12-492e-b678-b34e21543cf3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(410336320291 / 1000000000000), (797462573571 / 1000000000000), (410287671167 / 1000000000000), (1 / 1), (1 / 1)], ![(204428467601 / 500000000000), (100346033481 / 125000000000), (408808460977 / 1000000000000), (1 / 1), (1 / 1)], ![(1102690457400000000000000000000000 / 578610074011579110361259035056776201), (450978825218400000000000000000000000 / 4050270518081053772528813245397433407), (3542735383371200000000000000000000000 / 4050270518081053772528813245397433407), (450924888199400000000000000000000000 / 4050270518081053772528813245397433407), (7718746669400000000000000000000000 / 4050270518081053772528813245397433407)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-222694540537 / 250000000000), (-56580093779 / 250000000000), (-222724182081 / 250000000000), (0 / 1), (0 / 1)], ![(-894389975813 / 1000000000000), (-27461148711 / 125000000000), (-894508543201 / 1000000000000), (0 / 1), (0 / 1)], ![(-1565718934877 / 250000000000), (-2195118564793 / 1000000000000), (-33471134387 / 250000000000), (-1097619085919 / 500000000000), (-50103095601 / 8000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-890778162147 / 1000000000000), (-45264075023 / 200000000000), (-890896728323 / 1000000000000), (0 / 1), (0 / 1)], ![(-223597493953 / 250000000000), (-219689189687 / 1000000000000), (-1118135679 / 1250000000), (0 / 1), (0 / 1)], ![(-6262875739507 / 1000000000000), (-274389820599 / 125000000000), (-133884537547 / 1000000000000), (-2195238171837 / 1000000000000), (-1565721737531 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8048281010709 / 1000000000000), (-1657973741181 / 500000000000), (-132228179341 / 40000000000), (-959585621541 / 500000000000), (-579894102353 / 1000000000000), (-1919171241501 / 1000000000000), (-661141104589 / 200000000000), (-1657974261751 / 500000000000), (-8048055086629 / 1000000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-2012070252677 / 250000000000), (-3315947482361 / 1000000000000), (-826426120881 / 250000000000), (-1919171243081 / 1000000000000), (-36243381397 / 62500000000), (-3838342483 / 2000000000), (-12912912199 / 3906250000), (-3315948523501 / 1000000000000), (-2012013771657 / 250000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 3 19 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
