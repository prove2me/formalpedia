-- Prove2me | solution 1 for mme_released_interior_owner2_cell36_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:41.9437+00:00
-- url     : https://prove2.me/submissions/60579063-29d6-4168-902c-e8db038f8d45

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 2 36 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78561236439 / 500000000000), (476516505723 / 125000000000), (1906067092577 / 500000000000), (78561234647 / 500000000000)], ![(2395865723492000000000000000000000 / 30306857285445206026011583848976743), (114088897516000000000000000000000 / 1443183680259295525048170659475083), (1 / 1), (1 / 1), (1 / 1)], ![(116873441961 / 200000000000), (1050676409667 / 1000000000000), (292183909183 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-370145939143 / 200000000000), (669094312347 / 500000000000), (669094592947 / 500000000000), (-74029188741 / 40000000000)], ![(-2537629363227 / 1000000000000), (-1268814446971 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-134306427461 / 250000000000), (12358539111 / 250000000000), (-268612334221 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-925364847857 / 500000000000), (267637724939 / 200000000000), (267637837179 / 200000000000), (-462682429631 / 250000000000)], ![(-1268814681613 / 500000000000), (-2537628893941 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-537225709843 / 1000000000000), (9886831289 / 200000000000), (-537224668441 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-868332703487 / 500000000000), (-575003010443 / 500000000000), (-76962262369 / 15625000000), (-49255832581 / 10000000000), (-1150006112803 / 1000000000000), (-1736665417893 / 1000000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1736665406973 / 1000000000000), (-230001204177 / 200000000000), (-985116958323 / 200000000000), (-4925583258099 / 1000000000000), (-575003056401 / 500000000000), (-434166354473 / 250000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 36 5 c : ℝ) / 1000000000000) ≤
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
