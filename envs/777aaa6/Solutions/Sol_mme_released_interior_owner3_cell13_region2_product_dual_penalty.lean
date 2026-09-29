-- Prove2me | solution 1 for mme_released_interior_owner3_cell13_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:45.444249+00:00
-- url     : https://prove2.me/submissions/92565313-b549-4a36-b04e-880f761ac00c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 3 13 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(196638413359 / 500000000000), (196638477179 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(26652711347 / 500000000000), (203466971969 / 100000000000), (13165136022201 / 1000000000000), (1017335430489 / 500000000000), (26652712143 / 500000000000)], ![(2144117155976562500000000000000000 / 137330495987295069825010833230181841), (11192302159507812500000000000000000 / 137330495987295069825010833230181841), (11192305979898437500000000000000000 / 137330495987295069825010833230181841), (2144117467023437500000000000000000 / 137330495987295069825010833230181841), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-466620760699 / 500000000000), (-933241196843 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1465858606943 / 500000000000), (142066701163 / 200000000000), (1288786062501 / 500000000000), (44395879171 / 62500000000), (-2931717184021 / 1000000000000)], ![(-207983125741 / 50000000000), (-2507164165371 / 1000000000000), (-2507163824031 / 1000000000000), (-16638649479 / 4000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-933241521397 / 1000000000000), (-466620598421 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-586343442777 / 200000000000), (88791688227 / 125000000000), (2577572125003 / 1000000000000), (710334066737 / 1000000000000), (-146585859201 / 50000000000)], ![(-4159662514819 / 1000000000000), (-250716416537 / 100000000000), (-250716382403 / 100000000000), (-4159662369749 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8024621219489 / 1000000000000), (-2191284822479 / 500000000000), (-2730071620029 / 1000000000000), (-86283323721 / 100000000000), (-431416610213 / 500000000000), (-2730071515053 / 1000000000000), (-54782129817 / 12500000000), (-8024620779531 / 1000000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-250769413109 / 31250000000), (-4382569644957 / 1000000000000), (-682517905007 / 250000000000), (-862833237209 / 1000000000000), (-34513328817 / 40000000000), (-682517878763 / 250000000000), (-4382570385359 / 1000000000000), (-802462077953 / 100000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 3 13 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
