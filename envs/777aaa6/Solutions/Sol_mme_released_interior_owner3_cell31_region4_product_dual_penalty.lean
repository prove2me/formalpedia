-- Prove2me | solution 1 for mme_released_interior_owner3_cell31_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:16:19.42338+00:00
-- url     : https://prove2.me/submissions/372611e7-aeaa-41b1-bb01-f034f14a8311

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 3 31 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1303499816321 / 200000000000000), (63039952928953 / 250000000000000), (389604534617259 / 250000000000000), (126079920347603 / 500000000000000), (50917758321 / 7812500000000)], ![(500000002491923 / 1000000000000000), (124999999377019 / 250000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1575938284859 / 15625000000000), (537899949207041 / 1000000000000000), (134474982860133 / 250000000000000), (20172031911183 / 200000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 2, -1, 2, 7], ![1, 1, 0, 0, 0], ![3, 1, 1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-503326455306879 / 100000000000000), (-1377692218998293 / 1000000000000000), (443671292999741 / 1000000000000000), (-1377692104073587 / 1000000000000000), (-5033268544871259 / 1000000000000000)], ![(-6931471755761 / 10000000000000), (-346573592771897 / 500000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2294021364306953 / 1000000000000000), (-310041352065601 / 500000000000000), (-155020684290149 / 250000000000000), (-573505070095117 / 250000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5033264553068783 / 1000000000000000), (-137769221899829 / 100000000000000), (221835646499871 / 500000000000000), (-86105756504599 / 62500000000000), (-5033268544871253 / 1000000000000000)], ![(-346573587788049 / 500000000000000), (-43321699096487 / 62500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-45880427286139 / 20000000000000), (-193775845041 / 312500000000), (-310041368580297 / 500000000000000), (-458804056076093 / 200000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([6, 12, 1, 4, 4, 1, 12, 6] : List ℤ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4364860653924329 / 1000000000000000), (-8020437084754241 / 1000000000000000), (-434779298337627 / 500000000000000), (-538184396756177 / 200000000000000), (-67273053542567 / 25000000000000), (-869558619736953 / 1000000000000000), (-2005108004748281 / 250000000000000), (-2182429837477427 / 500000000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-1091215163481081 / 250000000000000), (-802043708475423 / 100000000000000), (-217389649168813 / 250000000000000), (-33636524797261 / 12500000000000), (-672730535425669 / 250000000000000), (-869558619736951 / 1000000000000000), (-8020432018993113 / 1000000000000000), (-136401864842339 / 31250000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 3 31 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
