-- Prove2me | solution 1 for mme_released_interior_owner4_cell19_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:17:53.485604+00:00
-- url     : https://prove2.me/submissions/2143fa09-0f8c-4c2b-adbc-5aa716b4aafc

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 4 19 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(415443165969 / 1000000000000), (386923711199 / 500000000000), (415423453433 / 1000000000000), (1 / 1), (1 / 1)], ![(25070250767187500000000000000000000 / 1272096038723932562687835338197050597), (5765810384750000000000000000000000 / 141344004302659173631981704244116733), (8356353981875000000000000000000000 / 424032012907977520895945112732350199), (1 / 1), (1 / 1)], ![(38941769369 / 1000000000000), (557216951031 / 250000000000), (8925862807987 / 500000000000), (2228759644001 / 1000000000000), (19470871259 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-439204729357 / 500000000000), (-25638055351 / 100000000000), (-878456909257 / 1000000000000), (0 / 1), (0 / 1)], ![(-490842416049 / 125000000000), (-3199250952239 / 1000000000000), (-490848343641 / 125000000000), (0 / 1), (0 / 1)], ![(-324568784173 / 100000000000), (801493745387 / 1000000000000), (720525044179 / 250000000000), (32057808691 / 40000000000), (-3245688531247 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-878409458713 / 1000000000000), (-256380553509 / 1000000000000), (-109807113657 / 125000000000), (0 / 1), (0 / 1)], ![(-3926739328391 / 1000000000000), (-1599625476119 / 500000000000), (-3926786749127 / 1000000000000), (0 / 1), (0 / 1)], ![(-3245687841729 / 1000000000000), (200373436347 / 250000000000), (2882100176717 / 1000000000000), (200361304319 / 250000000000), (-1622844265623 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-240387008071 / 125000000000), (-845418662251 / 250000000000), (-1006354664957 / 125000000000), (-819053525509 / 250000000000), (-573531329033 / 1000000000000), (-3276215207727 / 1000000000000), (-8050931498239 / 1000000000000), (-42270919661 / 12500000000), (-192309602749 / 100000000000)] : List ℚ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1923096064567 / 1000000000000), (-3381674649003 / 1000000000000), (-1610167463931 / 200000000000), (-655242820407 / 200000000000), (-71691416129 / 125000000000), (-1638107603863 / 500000000000), (-4025465749119 / 500000000000), (-3381673572879 / 1000000000000), (-1923096027489 / 1000000000000)] : List ℚ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 4 19 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
