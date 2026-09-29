-- Prove2me | solution 1 for mme_released_interior_owner2_cell18_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:00.425572+00:00
-- url     : https://prove2.me/submissions/cc70ef72-0a90-415b-bd33-2e5f668da89a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 2 18 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(573514823097 / 1000000000000), (533703264987 / 500000000000), (71689134667 / 125000000000), (1 / 1), (1 / 1)], ![(296256018206500000000000000000000000 / 3871486873439602924397317104312008177), (296255564607500000000000000000000000 / 3871486873439602924397317104312008177), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (150760544899 / 1000000000000), (3929239583093 / 1000000000000), (982308188519 / 250000000000), (37690093017 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-277985748011 / 500000000000), (65231902543 / 1000000000000), (-111194907999 / 200000000000), (0 / 1), (0 / 1)], ![(-642542477599 / 250000000000), (-2570171441501 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1892062496243 / 1000000000000), (342111479213 / 250000000000), (1368444178851 / 1000000000000), (-946031821319 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-555971496021 / 1000000000000), (4076993909 / 62500000000), (-277987269997 / 500000000000), (0 / 1), (0 / 1)], ![(-514033982079 / 200000000000), (-5140342883 / 2000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-946031248121 / 500000000000), (1368445916853 / 1000000000000), (342111044713 / 250000000000), (-1892063642637 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1003641009797 / 200000000000), (-1136493828999 / 1000000000000), (-878849266769 / 500000000000), (-439424689669 / 250000000000), (-227298724421 / 200000000000), (-1254552119437 / 250000000000)] : List ℚ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-627275631123 / 125000000000), (-568246914499 / 500000000000), (-1757698533537 / 1000000000000), (-70307950347 / 40000000000), (-142061702763 / 125000000000), (-5018208477747 / 1000000000000)] : List ℚ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 18 2 c : ℝ) / 1000000000000) ≤
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
