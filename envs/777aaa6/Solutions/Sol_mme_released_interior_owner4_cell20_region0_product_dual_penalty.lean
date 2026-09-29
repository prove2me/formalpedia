-- Prove2me | solution 1 for mme_released_interior_owner4_cell20_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:17:54.551279+00:00
-- url     : https://prove2.me/submissions/6f6b8e84-2d5c-4f6e-b523-c47f755a18d0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 4 20 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(221630921491 / 500000000000), (848596082963 / 1000000000000), (11082529081 / 25000000000), (1 / 1), (1 / 1)], ![(82349317587500000000000000000000000 / 8128149852472258694289214621112994267), (1242587802125500000000000000000000000 / 8128149852472258694289214621112994267), (1242643083423500000000000000000000000 / 8128149852472258694289214621112994267), (82359916941500000000000000000000000 / 8128149852472258694289214621112994267), (1 / 1)], ![(84827596111 / 500000000000), (1205579457893 / 500000000000), (2411265410733 / 1000000000000), (169678697789 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-81359461587 / 100000000000), (-164171962107 / 1000000000000), (-203376478297 / 250000000000), (0 / 1), (0 / 1)], ![(-4592118436367 / 1000000000000), (-939068592527 / 500000000000), (-1878092697197 / 1000000000000), (-918397946509 / 200000000000), (0 / 1)], ![(-1773987182727 / 1000000000000), (880107509837 / 1000000000000), (880151676397 / 1000000000000), (-1773848643267 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-813594615869 / 1000000000000), (-82085981053 / 500000000000), (-813505913187 / 1000000000000), (0 / 1), (0 / 1)], ![(-2296059218183 / 500000000000), (-1878137185053 / 1000000000000), (-469523174299 / 250000000000), (-71749839571 / 15625000000), (0 / 1)], ![(-886993591363 / 500000000000), (440053754919 / 500000000000), (440075838199 / 500000000000), (-886924321633 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2264726851117 / 500000000000), (-1300214152531 / 200000000000), (-5659403407 / 3125000000), (-1162295029339 / 1000000000000), (-4469329605853 / 1000000000000), (-279333433693 / 62500000000), (-581147354653 / 500000000000), (-452752284619 / 250000000000), (-325054029469 / 50000000000), (-905891569257 / 200000000000)] : List ℚ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4529453702233 / 1000000000000), (-3250535381327 / 500000000000), (-1811009090239 / 1000000000000), (-581147514669 / 500000000000), (-1117332401463 / 250000000000), (-4469334939087 / 1000000000000), (-232458941861 / 200000000000), (-72440365539 / 40000000000), (-6501080589379 / 1000000000000), (-1132364461571 / 250000000000)] : List ℚ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 20 0 c : ℝ) / 1000000000000) ≤
          (1641 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1641 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1641 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
