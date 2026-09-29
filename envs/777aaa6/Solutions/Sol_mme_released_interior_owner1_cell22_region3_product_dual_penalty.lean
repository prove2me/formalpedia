-- Prove2me | solution 1 for mme_released_interior_owner1_cell22_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:58.065393+00:00
-- url     : https://prove2.me/submissions/d2cae57f-0898-4a9c-bb36-236fefc5e129

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(116677314216400000000000000000000000 / 1518629704898872911406003373755864949), (210357100194800000000000000000000000 / 1518629704898872911406003373755864949), (116677474643000000000000000000000000 / 1518629704898872911406003373755864949), (1 / 1), (1 / 1)], ![(1 / 1), (155946949423 / 1000000000000), (3824866733911 / 1000000000000), (3824867950509 / 1000000000000), (77975391557 / 500000000000)], ![(299164354143 / 500000000000), (598329120083 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1283075785469 / 500000000000), (-49418928341 / 25000000000), (-128307509799 / 50000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1858239397371 / 1000000000000), (1341523625863 / 1000000000000), (1341523943939 / 1000000000000), (-185821481437 / 100000000000)], ![(-256807498321 / 500000000000), (-513614308397 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2566151570937 / 1000000000000), (-1976757133639 / 1000000000000), (-2566150195979 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-185823939737 / 100000000000), (167690453233 / 125000000000), (67076197197 / 50000000000), (-1858214814369 / 1000000000000)], ![(-513614996641 / 1000000000000), (-128403577099 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-987596276401 / 200000000000), (-1738241935397 / 1000000000000), (-1148848186343 / 1000000000000), (-287211954043 / 250000000000), (-347648313351 / 200000000000), (-4938003901683 / 1000000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1234495345501 / 250000000000), (-434560483849 / 250000000000), (-574424093171 / 500000000000), (-1148847816171 / 1000000000000), (-869120783377 / 500000000000), (-2469001950841 / 500000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 1 22 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
