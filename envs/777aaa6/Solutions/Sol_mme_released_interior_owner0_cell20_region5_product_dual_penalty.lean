-- Prove2me | solution 1 for mme_released_interior_owner0_cell20_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:12.674167+00:00
-- url     : https://prove2.me/submissions/d9ea3d8e-13ce-4d2e-bbf3-727261352c73

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(443383718756000000000000000000000000 / 16249021825912773777938744891167286399), (849011368461000000000000000000000000 / 16249021825912773777938744891167286399), (443286054566000000000000000000000000 / 16249021825912773777938744891167286399), (1 / 1), (1 / 1)], ![(170356820799 / 1000000000000), (2402763645363 / 1000000000000), (120124893661 / 50000000000), (170302872453 / 1000000000000), (1 / 1)], ![(164388056541 / 1000000000000), (2492059888497 / 1000000000000), (155736666701 / 62500000000), (1283836737 / 7812500000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3601352413199 / 1000000000000), (-2951715413983 / 1000000000000), (-3601572707593 / 1000000000000), (0 / 1), (0 / 1)], ![(-353972019153 / 200000000000), (175323918753 / 200000000000), (7012071813 / 8000000000), (-1770176824439 / 1000000000000), (0 / 1)], ![(-1805525447777 / 1000000000000), (456554816469 / 500000000000), (228249997551 / 250000000000), (-1805871969749 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1800676206599 / 500000000000), (-1475857706991 / 500000000000), (-450196588449 / 125000000000), (0 / 1), (0 / 1)], ![(-442465023941 / 250000000000), (438309796883 / 500000000000), (438254488313 / 500000000000), (-885088412219 / 500000000000), (0 / 1)], ![(-56422670243 / 31250000000), (913109632939 / 1000000000000), (182599998041 / 200000000000), (-451467992437 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2267274370747 / 500000000000), (-452831085137 / 250000000000), (-4462088494431 / 1000000000000), (-3249433408621 / 500000000000), (-1162231409013 / 1000000000000), (-232446475941 / 200000000000), (-3249418532191 / 500000000000), (-446210164713 / 100000000000), (-36226487501 / 20000000000), (-4534533181429 / 1000000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4534548741493 / 1000000000000), (-1811324340547 / 1000000000000), (-446208849443 / 100000000000), (-6498866817241 / 1000000000000), (-290557852253 / 250000000000), (-145279047463 / 125000000000), (-6498837064381 / 1000000000000), (-4462101647129 / 1000000000000), (-1811324375049 / 1000000000000), (-1133633295357 / 250000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 0 20 5 c : ℝ) / 1000000000000) ≤
          (1591 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1591 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1591 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
