-- Prove2me | solution 1 for mme_released_interior_owner1_cell31_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:38.193534+00:00
-- url     : https://prove2.me/submissions/06f2f523-cf67-43e7-a8ac-3a730371eb02

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5339750816200000000000000000000000 / 1746604599362153319045327979681199601), (206544774555500000000000000000000000 / 1746604599362153319045327979681199601), (425735139144400000000000000000000000 / 582201533120717773015109326560399867), (206543211935900000000000000000000000 / 1746604599362153319045327979681199601), (1779916946000000000000000000000000 / 582201533120717773015109326560399867)], ![(394537069157 / 1000000000000), (98633856121 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(54309088621 / 200000000000), (726524095501 / 500000000000), (1453041900097 / 1000000000000), (13577211121 / 50000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5790249965049 / 1000000000000), (-2134911738467 / 1000000000000), (-15649962541 / 50000000000), (-2134919304021 / 1000000000000), (-5790249960967 / 1000000000000)], ![(-930042178201 / 1000000000000), (-116255793353 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-81476610981 / 62500000000), (373663550591 / 1000000000000), (46707402641 / 125000000000), (-1303630271031 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-723781245631 / 125000000000), (-1067455869233 / 500000000000), (-312999250819 / 1000000000000), (-106745965201 / 50000000000), (-2895124980483 / 500000000000)], ![(-4650210891 / 5000000000), (-930046346823 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-260725155139 / 200000000000), (2919246489 / 7812500000), (373659221129 / 1000000000000), (-130363027103 / 100000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4011963291913 / 500000000000), (-2691298864159 / 1000000000000), (-4368584187689 / 1000000000000), (-434691023527 / 500000000000), (-217345551973 / 250000000000), (-4368591426551 / 1000000000000), (-2691297931627 / 1000000000000), (-8023917912939 / 1000000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-320957063353 / 40000000000), (-1345649432079 / 500000000000), (-546073023461 / 125000000000), (-869382047053 / 1000000000000), (-869382207891 / 1000000000000), (-87371828531 / 20000000000), (-1345648965813 / 500000000000), (-4011958956469 / 500000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 1 31 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
