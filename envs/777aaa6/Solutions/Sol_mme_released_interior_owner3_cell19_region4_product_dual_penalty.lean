-- Prove2me | solution 1 for mme_released_interior_owner3_cell19_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:33.603349+00:00
-- url     : https://prove2.me/submissions/5571121b-725a-4bbf-9183-2c4738457502

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(415459532573 / 1000000000000), (193420252513 / 250000000000), (415438304107 / 1000000000000), (1 / 1), (1 / 1)], ![(401097358267 / 1000000000000), (415212275531 / 500000000000), (200538439489 / 500000000000), (1 / 1), (1 / 1)], ![(2433740496062500000000000000000000 / 1272077495529776319333212259795005567), (139295398971875000000000000000000000 / 1272077495529776319333212259795005567), (1115768826648750000000000000000000000 / 1272077495529776319333212259795005567), (139288211313812500000000000000000000 / 1272077495529776319333212259795005567), (2433738787500000000000000000000000 / 1272077495529776319333212259795005567)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-21959251599 / 25000000000), (-128297811029 / 500000000000), (-54901322601 / 62500000000), (0 / 1), (0 / 1)], ![(-913551092449 / 1000000000000), (-2903409401 / 15625000000), (-456801075951 / 500000000000), (0 / 1), (0 / 1)], ![(-3129488646783 / 500000000000), (-1105904907799 / 500000000000), (-1311076893 / 10000000000), (-27648267713 / 12500000000), (-3129488997799 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-878370063959 / 1000000000000), (-256595622057 / 1000000000000), (-175684232323 / 200000000000), (0 / 1), (0 / 1)], ![(-28548471639 / 31250000000), (-185818201663 / 1000000000000), (-913602151901 / 1000000000000), (0 / 1), (0 / 1)], ![(-1251795458713 / 200000000000), (-2211809815597 / 1000000000000), (-131107689299 / 1000000000000), (-2211861417039 / 1000000000000), (-6258977995597 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4025500302803 / 500000000000), (-3382007589641 / 1000000000000), (-819012294697 / 250000000000), (-1923079905141 / 1000000000000), (-573521513021 / 1000000000000), (-1923079943381 / 1000000000000), (-3276049682743 / 1000000000000), (-3382008131473 / 1000000000000), (-8050899152953 / 1000000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1610200121121 / 200000000000), (-84550189741 / 25000000000), (-3276049178787 / 1000000000000), (-96153995257 / 50000000000), (-28676075651 / 50000000000), (-96153997169 / 50000000000), (-1638024841371 / 500000000000), (-211375508217 / 62500000000), (-1006362394119 / 125000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 3 19 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
