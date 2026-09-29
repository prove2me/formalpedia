-- Prove2me | solution 1 for mme_released_interior_owner3_cell18_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:30.639279+00:00
-- url     : https://prove2.me/submissions/74b394b4-4c37-4850-95df-8a08d4904baa

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(114695924773 / 200000000000), (1067324182049 / 1000000000000), (57348201379 / 100000000000), (1 / 1), (1 / 1)], ![(148115931401 / 250000000000), (592464965971 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (150696797863000000000000000000000000 / 7744286659458085780092468436362587071), (3930526433343000000000000000000000000 / 7744286659458085780092468436362587071), (3930535222484000000000000000000000000 / 7744286659458085780092468436362587071), (150696557610000000000000000000000000 / 7744286659458085780092468436362587071)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-278016436243 / 500000000000), (65154751899 / 1000000000000), (-111205741017 / 200000000000), (0 / 1), (0 / 1)], ![(-523465630457 / 1000000000000), (-130865884221 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3939440788261 / 1000000000000), (-13563639937 / 20000000000), (-67817976073 / 100000000000), (-3939442382543 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-111206574497 / 200000000000), (651547519 / 10000000000), (-139007176271 / 250000000000), (0 / 1), (0 / 1)], ![(-65433203807 / 125000000000), (-523463536883 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-196972039413 / 50000000000), (-678181996849 / 1000000000000), (-678179760729 / 1000000000000), (-1969721191271 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5018933030287 / 1000000000000), (-1136490781833 / 1000000000000), (-1757676332389 / 1000000000000), (-17576761701 / 10000000000), (-142061329911 / 125000000000), (-2509470442739 / 500000000000)] : List ℚ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-2509466515143 / 500000000000), (-142061347729 / 125000000000), (-439419083097 / 250000000000), (-1757676170099 / 1000000000000), (-1136490639287 / 1000000000000), (-5018940885477 / 1000000000000)] : List ℚ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 3 18 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
