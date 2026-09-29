-- Prove2me | solution 1 for mme_released_interior_owner2_cell26_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:35.030265+00:00
-- url     : https://prove2.me/submissions/2b9e6a42-9887-4a00-9ab2-f19cf6cc1858

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 2 26 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(169778935993 / 1000000000000), (244031096577 / 100000000000), (305021335853 / 125000000000), (84878192391 / 500000000000), (1 / 1)], ![(13900325507375000000000000000000000 / 496385651093599622096286021799942293), (9005291584093750000000000000000000 / 165461883697866540698762007266647431), (13898757620468750000000000000000000 / 496385651093599622096286021799942293), (1 / 1), (1 / 1)], ![(7001867201 / 40000000000), (472509962973 / 200000000000), (590604852359 / 250000000000), (21876401771 / 125000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1773258064667 / 1000000000000), (223031369043 / 250000000000), (446033995237 / 500000000000), (-1773390900397 / 1000000000000), (0 / 1)], ![(-1787720444659 / 500000000000), (-1455464249981 / 500000000000), (-1787776845329 / 500000000000), (0 / 1), (0 / 1)], ![(-1742702597629 / 1000000000000), (42987073291 / 50000000000), (171937253479 / 200000000000), (-217863153269 / 125000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-886629032333 / 500000000000), (892125476173 / 1000000000000), (35682719619 / 40000000000), (-443347725099 / 250000000000), (0 / 1)], ![(-3575440889317 / 1000000000000), (-2910928499961 / 1000000000000), (-3575553690657 / 1000000000000), (0 / 1), (0 / 1)], ![(-435675649407 / 250000000000), (859741465821 / 1000000000000), (214921566849 / 250000000000), (-1742905226151 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2214051432817 / 500000000000), (-911704014959 / 500000000000), (-2245547481803 / 500000000000), (-6413280699517 / 1000000000000), (-579594220633 / 500000000000), (-1159190723099 / 1000000000000), (-6413210791953 / 1000000000000), (-112278251031 / 25000000000), (-18234081471 / 10000000000), (-4428070610453 / 1000000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4428102865633 / 1000000000000), (-1823408029917 / 1000000000000), (-898218992721 / 200000000000), (-1603320174879 / 250000000000), (-231837688253 / 200000000000), (-579595361549 / 500000000000), (-400825674497 / 62500000000), (-4491130041239 / 1000000000000), (-1823408147099 / 1000000000000), (-1107017652613 / 250000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 26 2 c : ℝ) / 1000000000000) ≤
          (413 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (413 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((413 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
