-- Prove2me | solution 1 for mme_released_interior_owner5_cell20_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:22:03.527916+00:00
-- url     : https://prove2.me/submissions/ab246f6c-7cb0-4bcc-b30f-b629796a00b3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 5 20 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(443298024397 / 1000000000000), (424472925889 / 500000000000), (443332657111 / 1000000000000), (1 / 1), (1 / 1)], ![(170313205869 / 1000000000000), (1201279027901 / 500000000000), (1201325724393 / 500000000000), (42583536923 / 250000000000), (1 / 1)], ![(8215081485300000000000000000000000 / 812370486641868149746730365560345121), (124591729161300000000000000000000000 / 812370486641868149746730365560345121), (124596617119200000000000000000000000 / 812370486641868149746730365560345121), (8215998296050000000000000000000000 / 812370486641868149746730365560345121), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-25422281057 / 31250000000), (-16375987353 / 100000000000), (-3253739487 / 4000000000), (0 / 1), (0 / 1)], ![(-885058074791 / 500000000000), (219133506579 / 250000000000), (876572897871 / 1000000000000), (-221249149561 / 125000000000), (0 / 1)], ![(-918796965983 / 200000000000), (-374982855083 / 200000000000), (-58589845137 / 31250000000), (-459387323521 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-813512993823 / 1000000000000), (-163759873529 / 1000000000000), (-813434871749 / 1000000000000), (0 / 1), (0 / 1)], ![(-1770116149581 / 1000000000000), (876534026317 / 1000000000000), (54785806117 / 62500000000), (-1769993196487 / 1000000000000), (0 / 1)], ![(-2296992414957 / 500000000000), (-937457137707 / 500000000000), (-1874875044383 / 1000000000000), (-4593873235209 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2267395521457 / 500000000000), (-6499153829007 / 1000000000000), (-1811296127857 / 1000000000000), (-581118401251 / 500000000000), (-4462088631627 / 1000000000000), (-446209421187 / 100000000000), (-232447288893 / 200000000000), (-452824036833 / 250000000000), (-3249582588047 / 500000000000), (-4534796419869 / 1000000000000)] : List ℚ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4534791042913 / 1000000000000), (-3249576914503 / 500000000000), (-113206007991 / 62500000000), (-1162236802501 / 1000000000000), (-2231044315813 / 500000000000), (-4462094211869 / 1000000000000), (-72639777779 / 62500000000), (-1811296147331 / 1000000000000), (-6499165176093 / 1000000000000), (-1133699104967 / 250000000000)] : List ℚ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 20 0 c : ℝ) / 1000000000000) ≤
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
