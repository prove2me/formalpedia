-- Prove2me | solution 1 for mme_released_interior_owner2_cell28_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:33.792974+00:00
-- url     : https://prove2.me/submissions/476d4c31-358f-4d3f-9f80-e1bb5932c2e8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 2 28 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(55012556153 / 200000000000), (286111793159 / 200000000000), (1430565961449 / 1000000000000), (275064955029 / 1000000000000), (1 / 1)], ![(5331950363200000000000000000000000 / 1756239457626867743990099301866233909), (203394174166900000000000000000000000 / 1756239457626867743990099301866233909), (1316558561895800000000000000000000000 / 1756239457626867743990099301866233909), (203395974359000000000000000000000000 / 1756239457626867743990099301866233909), (5331950334200000000000000000000000 / 1756239457626867743990099301866233909)], ![(393456807229 / 1000000000000), (393458676867 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-16134448921 / 12500000000), (358065253067 / 1000000000000), (358070143209 / 1000000000000), (-1290748009101 / 1000000000000), (0 / 1)], ![(-1449303259311 / 250000000000), (-2155784289333 / 1000000000000), (-288153669323 / 1000000000000), (-2155775438617 / 1000000000000), (-5797213042683 / 1000000000000)], ![(-932783982769 / 1000000000000), (-186555846191 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1290755913679 / 1000000000000), (89516313267 / 250000000000), (35807014321 / 100000000000), (-12907480091 / 10000000000), (0 / 1)], ![(-5797213037243 / 1000000000000), (-538946072333 / 250000000000), (-144076834661 / 500000000000), (-269471929827 / 125000000000), (-2898606521341 / 500000000000)], ![(-58298998923 / 62500000000), (-466389615477 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-802074027697 / 100000000000), (-68262334427 / 25000000000), (-4379316281243 / 1000000000000), (-86286764721 / 100000000000), (-431433754439 / 500000000000), (-1094827645821 / 250000000000), (-2730494168311 / 1000000000000), (-8020752940761 / 1000000000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-8020740276969 / 1000000000000), (-2730493377079 / 1000000000000), (-2189658140621 / 500000000000), (-862867647209 / 1000000000000), (-862867508877 / 1000000000000), (-4379310583283 / 1000000000000), (-273049416831 / 100000000000), (-200518823519 / 25000000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 2 28 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
