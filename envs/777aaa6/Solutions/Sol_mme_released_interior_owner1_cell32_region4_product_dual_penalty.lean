-- Prove2me | solution 1 for mme_released_interior_owner1_cell32_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:41.793059+00:00
-- url     : https://prove2.me/submissions/dcda1075-39ed-49c8-912f-6a1e3ecad43c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(39024870739000000000000000000000000 / 19732813661123011662241193442877228331), (2332647607925000000000000000000000000 / 19732813661123011662241193442877228331), (16629286696729000000000000000000000000 / 19732813661123011662241193442877228331), (2332585550277000000000000000000000000 / 19732813661123011662241193442877228331), (39024849134000000000000000000000000 / 19732813661123011662241193442877228331)], ![(40370288301 / 100000000000), (422683037939 / 500000000000), (403692252013 / 1000000000000), (1 / 1), (1 / 1)], ![(210282399067 / 500000000000), (194689961657 / 250000000000), (420553706299 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-6225839042983 / 1000000000000), (-1067639491629 / 500000000000), (-17111751841 / 100000000000), (-427061117513 / 200000000000), (-1556459899151 / 250000000000)], ![(-907076109683 / 1000000000000), (-3359710391 / 20000000000), (-181420488749 / 200000000000), (0 / 1), (0 / 1)], ![(-43307835681 / 50000000000), (-15628285301 / 62500000000), (-54136442977 / 62500000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3112919521491 / 500000000000), (-2135278983257 / 1000000000000), (-171117518409 / 1000000000000), (-533826396891 / 250000000000), (-6225839596603 / 1000000000000)], ![(-453538054841 / 500000000000), (-167985519549 / 1000000000000), (-28346951367 / 31250000000), (0 / 1), (0 / 1)], ![(-866156713619 / 1000000000000), (-50010512963 / 200000000000), (-866183087631 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7999124574569 / 1000000000000), (-1646217022009 / 500000000000), (-3169447544291 / 1000000000000), (-972188331107 / 500000000000), (-589155602773 / 1000000000000), (-1944376729283 / 1000000000000), (-633889573379 / 200000000000), (-3292434209881 / 1000000000000), (-31246376637 / 3906250000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-999890571821 / 125000000000), (-3292434044017 / 1000000000000), (-316944754429 / 100000000000), (-1944376662213 / 1000000000000), (-147288900693 / 250000000000), (-972188364641 / 500000000000), (-1584723933447 / 500000000000), (-82310855247 / 25000000000), (-7999072419071 / 1000000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 1 32 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
