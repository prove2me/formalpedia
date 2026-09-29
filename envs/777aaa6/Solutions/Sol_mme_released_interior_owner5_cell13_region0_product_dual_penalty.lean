-- Prove2me | solution 1 for mme_released_interior_owner5_cell13_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:20:34.641352+00:00
-- url     : https://prove2.me/submissions/e8277ab4-4e01-4d81-8809-8048d8dff792

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 5 13 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(9787015021 / 25000000000), (391477510171 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(53074530421 / 1000000000000), (2004685198637 / 1000000000000), (212461588871 / 15625000000), (1002326734157 / 500000000000), (26537237387 / 500000000000)], ![(13830532939750000000000000000000000 / 886905635792464420762808715586433443), (70778914909500000000000000000000000 / 886905635792464420762808715586433443), (70778354655050000000000000000000000 / 886905635792464420762808715586433443), (13830214613650000000000000000000000 / 886905635792464420762808715586433443), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-187563863127 / 200000000000), (-937827210487 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1468029059447 / 500000000000), (69548704027 / 100000000000), (2609889018149 / 1000000000000), (347735606031 / 500000000000), (-2936059167363 / 1000000000000)], ![(-4160859910863 / 1000000000000), (-505635489303 / 200000000000), (-1264092681051 / 500000000000), (-260055182957 / 62500000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-468909657817 / 500000000000), (-468913605243 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2936058118893 / 1000000000000), (695487040271 / 1000000000000), (52197780363 / 20000000000), (695471212063 / 1000000000000), (-1468029583681 / 500000000000)], ![(-2080429955431 / 500000000000), (-1264088723257 / 500000000000), (-2528185362101 / 1000000000000), (-4160882927311 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-550401988653 / 125000000000), (-1606947678887 / 200000000000), (-856115638851 / 1000000000000), (-692631387523 / 250000000000), (-2770525532321 / 1000000000000), (-856115659589 / 1000000000000), (-251086507973 / 31250000000), (-1100803800683 / 250000000000)] : List ℚ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-4403215909223 / 1000000000000), (-4017369197217 / 500000000000), (-17122312777 / 20000000000), (-2770525550091 / 1000000000000), (-17315784577 / 6250000000), (-214028914897 / 250000000000), (-1606953651027 / 200000000000), (-4403215202731 / 1000000000000)] : List ℚ).getD
    ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 5 13 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
