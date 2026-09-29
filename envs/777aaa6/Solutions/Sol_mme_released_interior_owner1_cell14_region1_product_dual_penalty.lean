-- Prove2me | solution 1 for mme_released_interior_owner1_cell14_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:35.384275+00:00
-- url     : https://prove2.me/submissions/90e0e842-8bb3-4b03-975f-5b411af9875e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(119728869161600000000000000000000000 / 1517050295624039866209250040652694377), (119728710338200000000000000000000000 / 1517050295624039866209250040652694377), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (38992792193 / 250000000000), (3817849975243 / 1000000000000), (954461617469 / 250000000000), (155971205023 / 1000000000000)], ![(583649741263 / 1000000000000), (1051913265893 / 1000000000000), (583648479817 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2539293370683 / 1000000000000), (-2539294697209 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-929042052189 / 500000000000), (669843715231 / 500000000000), (1339686512309 / 1000000000000), (-1858083871957 / 1000000000000)], ![(-538454234193 / 1000000000000), (25305332023 / 500000000000), (-538456395501 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1269646685341 / 500000000000), (-317411837151 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1858084104377 / 1000000000000), (1339687430463 / 1000000000000), (133968651231 / 100000000000), (-464520967989 / 250000000000)], ![(-33653389637 / 62500000000), (50610664047 / 1000000000000), (-1076912791 / 2000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2467915738423 / 500000000000), (-1148996194329 / 1000000000000), (-1738062335721 / 1000000000000), (-108628901193 / 62500000000), (-11489966027 / 10000000000), (-1233958799273 / 250000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-987166295369 / 200000000000), (-143624524291 / 125000000000), (-43451558393 / 25000000000), (-1738062419087 / 1000000000000), (-1148996602699 / 1000000000000), (-4935835197091 / 1000000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 1 14 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
