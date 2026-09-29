-- Prove2me | solution 1 for mme_released_interior_owner1_cell26_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:31.103282+00:00
-- url     : https://prove2.me/submissions/fc7dc7d4-f115-4a4f-89b6-8517d42aa528

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1764328441120000000000000000000000 / 158774161286572922585322452218309971), (23438011768030000000000000000000000 / 158774161286572922585322452218309971), (23438094628610000000000000000000000 / 158774161286572922585322452218309971), (1764348222290000000000000000000000 / 158774161286572922585322452218309971), (1 / 1)], ![(11119762809 / 25000000000), (864383495353 / 1000000000000), (88958735327 / 200000000000), (1 / 1), (1 / 1)], ![(2105915869 / 12500000000), (307337937613 / 125000000000), (122935608443 / 50000000000), (168475259813 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4499712691909 / 1000000000000), (-382624736869 / 200000000000), (-478280037261 / 250000000000), (-1124925370061 / 250000000000), (0 / 1)], ![(-1012689833 / 1250000000), (-145738748293 / 1000000000000), (-405072376173 / 500000000000), (0 / 1), (0 / 1)], ![(-890489089819 / 500000000000), (899634178861 / 1000000000000), (56227356517 / 62500000000), (-890483183003 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1124928172977 / 250000000000), (-239140460543 / 125000000000), (-1913120149043 / 1000000000000), (-4499701480243 / 1000000000000), (0 / 1)], ![(-810151866399 / 1000000000000), (-36434687073 / 250000000000), (-162028950469 / 200000000000), (0 / 1), (0 / 1)], ![(-1780978179637 / 1000000000000), (449817089431 / 500000000000), (899637704273 / 1000000000000), (-356193273201 / 200000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2206052705637 / 500000000000), (-3206184714929 / 500000000000), (-911675335851 / 500000000000), (-1159297704827 / 1000000000000), (-4506313677937 / 1000000000000), (-2253157421309 / 500000000000), (-1159297695009 / 1000000000000), (-911675362513 / 500000000000), (-6412370036757 / 1000000000000), (-4412104836153 / 1000000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4412105411273 / 1000000000000), (-6412369429857 / 1000000000000), (-1823350671701 / 1000000000000), (-579648852413 / 500000000000), (-281644604871 / 62500000000), (-4506314842617 / 1000000000000), (-36228052969 / 31250000000), (-72934029001 / 40000000000), (-1603092509189 / 250000000000), (-551513104519 / 125000000000)] : List ℚ).getD
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
        (splitWeight 1 26 3 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (428 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((428 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
