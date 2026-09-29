-- Prove2me | solution 1 for mme_released_interior_owner4_cell36_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:18:58.01765+00:00
-- url     : https://prove2.me/submissions/8de5f268-b066-49e4-b02d-2969d9c8fb56

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 4 36 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157543711903 / 1000000000000), (3806183677151 / 1000000000000), (1903092845807 / 500000000000), (157543538429 / 1000000000000)], ![(23985902988520000000000000000000000 / 302391572915028477533258601173347311), (23985911586640000000000000000000000 / 302391572915028477533258601173347311), (1 / 1), (1 / 1), (1 / 1)], ![(586457465029 / 1000000000000), (1045395087297 / 1000000000000), (58645797779 / 100000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1848052323331 / 1000000000000), (668313513801 / 500000000000), (668313778431 / 500000000000), (-28875834757 / 15625000000)], ![(-633564123569 / 250000000000), (-2534256135811 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266827568457 / 500000000000), (44394887933 / 1000000000000), (-266827131289 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-184805232333 / 100000000000), (1336627027603 / 1000000000000), (1336627556863 / 1000000000000), (-1848053424447 / 1000000000000)], ![(-101370259771 / 40000000000), (-253425613581 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533655136913 / 1000000000000), (22197443967 / 500000000000), (-533654262577 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4915965055693 / 1000000000000), (-1153234049481 / 1000000000000), (-54102616539 / 31250000000), (-1731283715863 / 1000000000000), (-46129368811 / 40000000000), (-4915962721703 / 1000000000000)] : List ℚ).getD
    ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1228991263923 / 250000000000), (-28830851237 / 25000000000), (-1731283729247 / 1000000000000), (-865641857931 / 500000000000), (-576617110137 / 500000000000), (-2457981360851 / 500000000000)] : List ℚ).getD
    ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 4 36 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
