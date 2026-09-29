-- Prove2me | solution 1 for mme_released_interior_owner1_cell27_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:34.597621+00:00
-- url     : https://prove2.me/submissions/7b71ce57-07a2-4b06-9441-08b0c7765e4e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(3528401097840000000000000000000000 / 317123941279676094995302864672131859), (46890651759480000000000000000000000 / 317123941279676094995302864672131859), (46894385586900000000000000000000000 / 317123941279676094995302864672131859), (320839902400000000000000000000000 / 28829449207243281363209351333830169), (1 / 1)], ![(21118739417 / 125000000000), (1226078899561 / 500000000000), (15327205303 / 6250000000), (16899045977 / 100000000000), (1 / 1)], ![(445187775107 / 1000000000000), (864999883507 / 1000000000000), (89051724833 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4498447857873 / 1000000000000), (-95573717333 / 50000000000), (-1911394721433 / 1000000000000), (-2249105216653 / 500000000000), (0 / 1)], ![(-1778152966941 / 1000000000000), (896968371273 / 1000000000000), (897047910037 / 1000000000000), (-888956508359 / 500000000000), (0 / 1)], ![(-809259119287 / 1000000000000), (-5801036269 / 40000000000), (-101137498467 / 125000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-281152991117 / 62500000000), (-1911474346659 / 1000000000000), (-238924340179 / 125000000000), (-899642086661 / 200000000000), (0 / 1)], ![(-88907648347 / 50000000000), (448484185637 / 500000000000), (448523955019 / 500000000000), (-1777913016717 / 1000000000000), (0 / 1)], ![(-404629559643 / 500000000000), (-36256476681 / 250000000000), (-161819997547 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-3203595094459 / 500000000000), (-2206207910223 / 500000000000), (-900147819521 / 200000000000), (-1159526483991 / 1000000000000), (-22791474091 / 12500000000), (-1823317894851 / 1000000000000), (-579763198861 / 500000000000), (-4500740287971 / 1000000000000), (-4412417063411 / 1000000000000), (-256287708669 / 40000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-6407190188917 / 1000000000000), (-882483164089 / 200000000000), (-1125184774401 / 250000000000), (-115952648399 / 100000000000), (-1823317927279 / 1000000000000), (-36466357897 / 20000000000), (-1159526397721 / 1000000000000), (-450074028797 / 100000000000), (-441241706341 / 100000000000), (-1601798179181 / 250000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 1 27 5 c : ℝ) / 1000000000000) ≤
          (440 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (440 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((440 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
