-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:12:36.707538+00:00
-- url     : https://prove2.me/submissions/77058604-e397-4c38-ac69-3e502dc3b5cf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(36874286689033531257133109661 / 100000000000000000000000000000), (38479549225888515204507741111 / 50000000000000000000000000000), (18437142758772915628572412269 / 50000000000000000000000000000), (1 / 1), (1 / 1)], ![(270113206549897298867934501 / 100000000000000000000000000000), (7944227200819620557727991803 / 50000000000000000000000000000), (29654824749099803451752508999 / 25000000000000000000000000000), (993028398090890069716019091 / 6250000000000000000000000000), (270111341673697298886583263 / 100000000000000000000000000000)], ![(33003573066247369964269337523 / 100000000000000000000000000000), (61153437430019288465625699801 / 100000000000000000000000000000), (16501787231924134982127680757 / 50000000000000000000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![9, 3, 0, 3, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-124706964442677 / 125000000000000), (-261896094203193 / 1000000000000000), (-997655747311189 / 1000000000000000), (0 / 1), (0 / 1)], ![(-1478521077582123 / 250000000000000), (-1839577478789673 / 1000000000000000), (170749010747289 / 1000000000000000), (-1839577480815357 / 1000000000000000), (-2957045607203229 / 500000000000000)], ![(-110855435564813 / 100000000000000), (-122946028087977 / 250000000000000), (-1108554313301173 / 1000000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-498827857770707 / 500000000000000), (-32737011775399 / 125000000000000), (-997655747311187 / 1000000000000000), (0 / 1), (0 / 1)], ![(-5914084310328483 / 1000000000000000), (-1839577478789669 / 1000000000000000), (17074901074729 / 100000000000000), (-919788740407677 / 500000000000000), (-5914091214406449 / 1000000000000000)], ![(-1108554355648127 / 1000000000000000), (-245892056175953 / 500000000000000), (-1108554313301171 / 1000000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-501268830349747 / 62500000000000), (-3210027866156469 / 1000000000000000), (-1935461110245951 / 1000000000000000), (-416127172671277 / 125000000000000), (-582931195807781 / 1000000000000000), (-133160690631647 / 40000000000000), (-1935461000061317 / 1000000000000000), (-321002795080419 / 100000000000000), (-8020294370940801 / 1000000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020301285595941 / 1000000000000000), (-200626741634779 / 62500000000000), (-483865277561487 / 250000000000000), (-3329017381370211 / 1000000000000000), (-582931195807779 / 1000000000000000), (-332901726579117 / 100000000000000), (-967730500030657 / 500000000000000), (-642005590160837 / 200000000000000), (-802029437094079 / 100000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
