-- Prove2me | solution 1 for mme_released_interior_owner3_cell33_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:37.371407+00:00
-- url     : https://prove2.me/submissions/e15a80ab-3947-4128-9e31-789ab0d63770

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 3 33 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53411906797 / 1000000000000), (1033168951857 / 500000000000), (6388392696147 / 500000000000), (2066238769433 / 1000000000000), (26705902047 / 500000000000)], ![(272819636419 / 1000000000000), (361910816003 / 250000000000), (361902878119 / 250000000000), (272794073159 / 1000000000000), (1 / 1)], ![(98733594155250000000000000000000000 / 4357165074028933871105561684380149281), (98731377749000000000000000000000000 / 4357165074028933871105561684380149281), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-585944316829 / 200000000000), (18144447797 / 25000000000), (127381494153 / 50000000000), (725729934897 / 1000000000000), (-585944701399 / 200000000000)], ![(-324736093649 / 250000000000), (184968449489 / 500000000000), (369914965477 / 1000000000000), (-649519039603 / 500000000000), (0 / 1)], ![(-3787151657643 / 1000000000000), (-946793526561 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-183107599009 / 62500000000), (725777911881 / 1000000000000), (2547629883061 / 1000000000000), (362864967449 / 500000000000), (-1464861753497 / 500000000000)], ![(-259788874919 / 200000000000), (369936898979 / 1000000000000), (184957482739 / 500000000000), (-259807615841 / 200000000000), (0 / 1)], ![(-1893575828821 / 500000000000), (-3787174106243 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4360411824961 / 1000000000000), (-54350425569 / 62500000000), (-2691484823771 / 1000000000000), (-1603163908027 / 200000000000), (-8015933769201 / 1000000000000), (-2691481228879 / 1000000000000), (-869607324207 / 1000000000000), (-4360388545967 / 1000000000000)] : List ℚ).getD
    ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-13626286953 / 3125000000), (-869606809103 / 1000000000000), (-269148482377 / 100000000000), (-4007909770067 / 500000000000), (-20039834423 / 2500000000), (-1345740614439 / 500000000000), (-434803662103 / 500000000000), (-2180194272983 / 500000000000)] : List ℚ).getD
    ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 33 1 c : ℝ) / 1000000000000) ≤
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
