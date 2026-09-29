-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:37.003987+00:00
-- url     : https://prove2.me/submissions/cfe80122-8272-418f-9e7d-a4e9a056de82

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(51565684919 / 125000000000), (402618022713 / 500000000000), (412527377311 / 1000000000000), (1 / 1), (1 / 1)], ![(3898918329 / 100000000000), (289096151871 / 125000000000), (3379324687701 / 200000000000), (1156389951309 / 500000000000), (7797837849 / 200000000000)], ![(13709029120000000000000000000000000 / 661298943125373090582297727105195263), (26987596937200000000000000000000000 / 661298943125373090582297727105195263), (13709093392900000000000000000000000 / 661298943125373090582297727105195263), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-885457306989 / 1000000000000), (-108309910207 / 500000000000), (-885452706171 / 1000000000000), (0 / 1), (0 / 1)], ![(-3244471022861 / 1000000000000), (838445600911 / 1000000000000), (706778451357 / 250000000000), (838450222049 / 1000000000000), (-1622235435063 / 500000000000)], ![(-3876151320899 / 1000000000000), (-3198828608739 / 1000000000000), (-3876146632547 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-221364326747 / 250000000000), (-216619820413 / 1000000000000), (-88545270617 / 100000000000), (0 / 1), (0 / 1)], ![(-162223551143 / 50000000000), (52402850057 / 62500000000), (2827113805429 / 1000000000000), (16769004441 / 20000000000), (-25955766961 / 8000000000)], ![(-1938075660449 / 500000000000), (-3198828608737 / 1000000000000), (-1938073316273 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4003039749573 / 500000000000), (-3254320919271 / 1000000000000), (-386898044329 / 200000000000), (-1622917846841 / 500000000000), (-588334623721 / 1000000000000), (-3245835713997 / 1000000000000), (-483622533527 / 250000000000), (-406790106507 / 125000000000), (-8006070360821 / 1000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1601215899829 / 200000000000), (-325432091927 / 100000000000), (-483622555411 / 250000000000), (-3245835693681 / 1000000000000), (-14708365593 / 25000000000), (-811458928499 / 250000000000), (-1934490134107 / 1000000000000), (-650864170411 / 200000000000), (-400303518041 / 50000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
