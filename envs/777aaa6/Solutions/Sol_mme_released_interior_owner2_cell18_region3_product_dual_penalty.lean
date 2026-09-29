-- Prove2me | solution 1 for mme_released_interior_owner2_cell18_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:01.485829+00:00
-- url     : https://prove2.me/submissions/46c87865-d564-4b11-95ad-f9b187051f59

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 2 18 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(286685550251 / 500000000000), (1068751157919 / 1000000000000), (573368442263 / 1000000000000), (1 / 1), (1 / 1)], ![(98785305694500000000000000000000000 / 1289615077834289353318823620899323297), (296355253382500000000000000000000000 / 3868845233502868059956470862697969891), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (6043833857 / 40000000000), (1961105568739 / 500000000000), (3922200737087 / 1000000000000), (151095686517 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-139055531761 / 250000000000), (66490824701 / 1000000000000), (-556226763213 / 1000000000000), (0 / 1), (0 / 1)], ![(-2569150197649 / 1000000000000), (-321144054649 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-472460224749 / 250000000000), (68332778023 / 50000000000), (1366652908791 / 1000000000000), (-1889841957319 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-556222127043 / 1000000000000), (33245412351 / 500000000000), (-139056690803 / 250000000000), (0 / 1), (0 / 1)], ![(-160571887353 / 62500000000), (-2569152437191 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-377968179799 / 200000000000), (1366655560461 / 1000000000000), (170831613599 / 125000000000), (-944920978659 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5015214282079 / 1000000000000), (-1136006464157 / 1000000000000), (-1758721400401 / 1000000000000), (-439680413861 / 250000000000), (-1136006052029 / 1000000000000), (-5015220099423 / 1000000000000)] : List ℚ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-2507607141039 / 500000000000), (-284001616039 / 250000000000), (-4396803501 / 2500000000), (-1758721655443 / 1000000000000), (-284001513007 / 250000000000), (-2507610049711 / 500000000000)] : List ℚ).getD
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
        (splitWeight 2 18 3 c : ℝ) / 1000000000000) ≤
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
