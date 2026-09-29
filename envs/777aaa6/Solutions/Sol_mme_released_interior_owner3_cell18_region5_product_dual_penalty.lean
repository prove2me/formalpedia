-- Prove2me | solution 1 for mme_released_interior_owner3_cell18_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:31.379802+00:00
-- url     : https://prove2.me/submissions/91fda742-9e01-42cf-9160-5b70d21a36ff

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(114796415779 / 200000000000), (266088324131 / 250000000000), (286995745867 / 500000000000), (1 / 1), (1 / 1)], ![(296156490927 / 500000000000), (296158894611 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (75097121152000000000000000000000000 / 3875982119685915987446750090087343861), (1970757918892000000000000000000000000 / 3875982119685915987446750090087343861), (1970774994212000000000000000000000000 / 3875982119685915987446750090087343861), (25032406495500000000000000000000000 / 1291994039895305329148916696695781287)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-138789276147 / 250000000000), (62367381409 / 1000000000000), (-2168518381 / 3906250000), (0 / 1), (0 / 1)], ![(-523720098239 / 1000000000000), (-523711982009 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-394377213541 / 100000000000), (-169095220443 / 250000000000), (-169093054367 / 250000000000), (-197188541299 / 50000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-555157104587 / 1000000000000), (6236738141 / 100000000000), (-111028141107 / 200000000000), (0 / 1), (0 / 1)], ![(-261860049119 / 500000000000), (-65463997751 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3943772135409 / 1000000000000), (-676380881771 / 1000000000000), (-676372217467 / 1000000000000), (-3943770825979 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-502262482291 / 100000000000), (-1137725482371 / 1000000000000), (-877620842773 / 500000000000), (-351048260813 / 200000000000), (-142215616787 / 125000000000), (-5022648028893 / 1000000000000)] : List ℚ).getD
    ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5022624822909 / 1000000000000), (-113772548237 / 100000000000), (-351048337109 / 200000000000), (-428525709 / 244140625), (-227544986859 / 200000000000), (-1255662007223 / 250000000000)] : List ℚ).getD
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
        (splitWeight 3 18 5 c : ℝ) / 1000000000000) ≤
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
