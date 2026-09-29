-- Prove2me | solution 1 for mme_released_interior_owner2_cell33_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:11:49.736519+00:00
-- url     : https://prove2.me/submissions/c0ccc6a7-c400-4f86-95ba-52fc28d9e040

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 2 33 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53397666617 / 1000000000000), (2066390830333 / 1000000000000), (12781922275813 / 1000000000000), (2066380134751 / 1000000000000), (13349414191 / 250000000000)], ![(17010113652125000000000000000000000 / 1090755799272362199329861505171764883), (90633638588687500000000000000000000 / 1090755799272362199329861505171764883), (90633430872625000000000000000000000 / 1090755799272362199329861505171764883), (17009924937125000000000000000000000 / 1090755799272362199329861505171764883), (1 / 1)], ![(394683558551 / 1000000000000), (78936525141 / 200000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1464994115141 / 500000000000), (725803525281 / 1000000000000), (318503981307 / 125000000000), (145159669859 / 200000000000), (-2929988414803 / 1000000000000)], ![(-4160818040891 / 1000000000000), (-99512027911 / 40000000000), (-2487802989599 / 1000000000000), (-832165827047 / 200000000000), (0 / 1)], ![(-46483547637 / 50000000000), (-58104582267 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929988230281 / 1000000000000), (362901762641 / 500000000000), (2548031850457 / 1000000000000), (45362396831 / 62500000000), (-1464994207401 / 500000000000)], ![(-416081804089 / 100000000000), (-1243900348887 / 500000000000), (-1243901494799 / 500000000000), (-2080414567617 / 500000000000), (0 / 1)], ![(-929670952739 / 1000000000000), (-929673316271 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4364693007833 / 1000000000000), (-8020477407911 / 1000000000000), (-86944216359 / 100000000000), (-107666932049 / 40000000000), (-2691672780591 / 1000000000000), (-21736052297 / 25000000000), (-501280667687 / 62500000000), (-4364696562723 / 1000000000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-545586625979 / 125000000000), (-802047740791 / 100000000000), (-869442163589 / 1000000000000), (-336459162653 / 125000000000), (-269167278059 / 100000000000), (-869442091879 / 1000000000000), (-8020490682991 / 1000000000000), (-2182348281361 / 500000000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 2 33 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
