-- Prove2me | solution 1 for mme_released_interior_owner1_cell13_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:33.204974+00:00
-- url     : https://prove2.me/submissions/f07ec0cd-8e73-4812-8cae-5308f43acba0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(196491089120500000000000000000000000 / 8800552949909676001100903887107546647), (196491543162500000000000000000000000 / 8800552949909676001100903887107546647), (1 / 1), (1 / 1), (1 / 1)], ![(26659669531 / 500000000000), (1016846193987 / 500000000000), (13154912234909 / 1000000000000), (1016852158021 / 500000000000), (26659677169 / 500000000000)], ![(136774160303 / 500000000000), (359205434797 / 250000000000), (28736495361 / 20000000000), (54710641093 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-475244093927 / 125000000000), (-950487610167 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-586291235887 / 200000000000), (709853051171 / 1000000000000), (515359048571 / 200000000000), (709858916381 / 1000000000000), (-586291178587 / 200000000000)], ![(-5185107991 / 4000000000), (90608387183 / 250000000000), (362435656759 / 1000000000000), (-1296259140519 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-760390550283 / 200000000000), (-3801950440667 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1465728089717 / 500000000000), (177463262793 / 250000000000), (322099405357 / 125000000000), (354929458191 / 500000000000), (-1465727946467 / 500000000000)], ![(-1296276997749 / 1000000000000), (362433548733 / 1000000000000), (9060891419 / 25000000000), (-648129570259 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8029685641053 / 1000000000000), (-1364830143151 / 500000000000), (-431360925901 / 500000000000), (-4388358840761 / 1000000000000), (-2194184260999 / 500000000000), (-431360824541 / 500000000000), (-272966173273 / 100000000000), (-4014832880523 / 500000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-2007421410263 / 250000000000), (-2729660286301 / 1000000000000), (-862721851801 / 1000000000000), (-109708971019 / 25000000000), (-4388368521997 / 1000000000000), (-862721649081 / 1000000000000), (-2729661732729 / 1000000000000), (-1605933152209 / 200000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 13 2 c : ℝ) / 1000000000000) ≤
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
