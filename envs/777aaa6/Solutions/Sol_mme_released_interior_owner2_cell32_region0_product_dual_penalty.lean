-- Prove2me | solution 1 for mme_released_interior_owner2_cell32_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:37.735339+00:00
-- url     : https://prove2.me/submissions/e3dab07b-bcce-40c0-8f69-879f9dd413ff

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 2 32 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(39025078591 / 1000000000000), (2332759104033 / 1000000000000), (16630858552701 / 1000000000000), (1166348197701 / 500000000000), (9756264307 / 250000000000)], ![(8074361167760000000000000000000000 / 394677828285800602906219214054682057), (16904902994480000000000000000000000 / 394677828285800602906219214054682057), (2691381928440000000000000000000000 / 131559276095266867635406404684894019), (1 / 1), (1 / 1)], ![(42053936079 / 100000000000), (38942197769 / 50000000000), (84105627813 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-5068048123 / 1562500000), (211762932957 / 250000000000), (2811259918613 / 1000000000000), (211756212431 / 250000000000), (-1621775673069 / 500000000000)], ![(-3889376053879 / 1000000000000), (-3150466109637 / 1000000000000), (-3889402729093 / 1000000000000), (0 / 1), (0 / 1)], ![(-433108599609 / 500000000000), (-49988913439 / 200000000000), (-866243883699 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3243550798719 / 1000000000000), (847051731829 / 1000000000000), (1405629959307 / 500000000000), (33880993989 / 40000000000), (-3243551346137 / 1000000000000)], ![(-1944688026939 / 500000000000), (-630093221927 / 200000000000), (-972350682273 / 250000000000), (0 / 1), (0 / 1)], ![(-866217199217 / 1000000000000), (-124972283597 / 500000000000), (-433121941849 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1944360002713 / 1000000000000), (-823073958479 / 250000000000), (-7999144598213 / 1000000000000), (-3169658316857 / 1000000000000), (-294575379109 / 500000000000), (-792414600949 / 250000000000), (-7999197409781 / 1000000000000), (-1646147750943 / 500000000000), (-60761250811 / 31250000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-243045000339 / 125000000000), (-658459166783 / 200000000000), (-1999786149553 / 250000000000), (-396207289607 / 125000000000), (-589150758217 / 1000000000000), (-633931680759 / 200000000000), (-399959870489 / 50000000000), (-658459100377 / 200000000000), (-1944360025951 / 1000000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 32 0 c : ℝ) / 1000000000000) ≤
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
