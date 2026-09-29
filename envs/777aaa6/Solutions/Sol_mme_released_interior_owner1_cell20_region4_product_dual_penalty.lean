-- Prove2me | solution 1 for mme_released_interior_owner1_cell20_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:49.597717+00:00
-- url     : https://prove2.me/submissions/c6c7fd13-40df-4ce5-a6e8-32677bd5448f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 1 20 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(222258302090500000000000000000000000 / 7959728537214007367188008209765502349), (431912077196500000000000000000000000 / 7959728537214007367188008209765502349), (222210469437500000000000000000000000 / 7959728537214007367188008209765502349), (1 / 1), (1 / 1)], ![(168952034161 / 1000000000000), (1224901097283 / 500000000000), (612384821941 / 250000000000), (33779160503 / 200000000000), (1 / 1)], ![(21878419207 / 125000000000), (2361019822143 / 1000000000000), (236076491871 / 100000000000), (174972573583 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1789154973229 / 500000000000), (-291392813237 / 100000000000), (-223657823851 / 62500000000), (0 / 1), (0 / 1)], ![(-1778140425877 / 1000000000000), (179201456877 / 200000000000), (895899961063 / 1000000000000), (-444618326843 / 250000000000), (0 / 1)], ![(-435703252667 / 250000000000), (859093653723 / 1000000000000), (42949284231 / 50000000000), (-435781509931 / 250000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3578309946457 / 1000000000000), (-2913928132369 / 1000000000000), (-715705036323 / 200000000000), (0 / 1), (0 / 1)], ![(-444535106469 / 250000000000), (448003642193 / 500000000000), (111987495133 / 125000000000), (-1778473307371 / 1000000000000), (0 / 1)], ![(-1742813010667 / 1000000000000), (214773413431 / 250000000000), (858985684621 / 1000000000000), (-1743126039723 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-562459030323 / 125000000000), (-911575584977 / 500000000000), (-4427273043329 / 1000000000000), (-1284311827169 / 200000000000), (-115900479823 / 100000000000), (-1159005442529 / 1000000000000), (-802692407101 / 125000000000), (-4427282550093 / 1000000000000), (-1823151112703 / 1000000000000), (-2249831294739 / 500000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4499672242583 / 1000000000000), (-1823151169953 / 1000000000000), (-34588070651 / 7812500000), (-1605389783961 / 250000000000), (-1159004798229 / 1000000000000), (-36218920079 / 31250000000), (-6421539256807 / 1000000000000), (-1106820637523 / 250000000000), (-911575556351 / 500000000000), (-4499662589477 / 1000000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 20 4 c : ℝ) / 1000000000000) ≤
          (400 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (400 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((400 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
