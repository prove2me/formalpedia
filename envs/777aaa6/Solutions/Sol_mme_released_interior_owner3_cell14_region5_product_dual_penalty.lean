-- Prove2me | solution 1 for mme_released_interior_owner3_cell14_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:54.721771+00:00
-- url     : https://prove2.me/submissions/80498be9-986b-4b9f-9905-9b48127a3e9a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(597935089059 / 1000000000000), (597948384621 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (155936434943 / 1000000000000), (3834463889179 / 1000000000000), (766910156403 / 200000000000), (77970736243 / 500000000000)], ![(6942591307000000000000000000000000 / 90511353199883450867226939093578309), (87590839748000000000000000000000000 / 633579472399184156070588573655048163), (145800972717500000000000000000000000 / 1900738417197552468211765720965144489), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-32142067353 / 62500000000), (-5142508421 / 10000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-371661364617 / 200000000000), (134402963083 / 100000000000), (672026145793 / 500000000000), (-1858274518501 / 1000000000000)], ![(-1283900100279 / 500000000000), (-494677254557 / 250000000000), (-320969404893 / 125000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-514273077647 / 1000000000000), (-514250842099 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-464576705771 / 250000000000), (1344029630831 / 1000000000000), (1344052291587 / 1000000000000), (-3716549037 / 2000000000)], ![(-2567800200557 / 1000000000000), (-1978709018227 / 1000000000000), (-2567755239143 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-247017389837 / 50000000000), (-173799875107 / 100000000000), (-1148929804291 / 1000000000000), (-1148930229497 / 1000000000000), (-43449967149 / 25000000000), (-4940312904291 / 1000000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4940347796739 / 1000000000000), (-1737998751069 / 1000000000000), (-114892980429 / 100000000000), (-143616278687 / 125000000000), (-1737998685959 / 1000000000000), (-494031290429 / 100000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 3 14 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
