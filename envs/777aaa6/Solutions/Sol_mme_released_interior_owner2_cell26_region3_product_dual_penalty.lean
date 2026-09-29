-- Prove2me | solution 1 for mme_released_interior_owner2_cell26_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:36.129293+00:00
-- url     : https://prove2.me/submissions/69e5ca59-e501-4f0a-9605-201a6d1b6537

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 2 26 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(165546388493 / 1000000000000), (309539360471 / 125000000000), (2476149927561 / 1000000000000), (165520764303 / 1000000000000), (1 / 1)], ![(18484726243000000000000000000000000 / 676062162773274849849194486581097907), (106145701065500000000000000000000000 / 2028186488319824549547583459743293721), (55446935044375000000000000000000000 / 2028186488319824549547583459743293721), (1 / 1), (1 / 1)], ![(169673321161 / 1000000000000), (2413338687713 / 1000000000000), (2413184291439 / 1000000000000), (33926685839 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1798503830431 / 1000000000000), (906771521117 / 1000000000000), (181340981063 / 200000000000), (-1798658627969 / 1000000000000), (0 / 1)], ![(-719868049197 / 200000000000), (-737521157149 / 250000000000), (-3599470879203 / 1000000000000), (0 / 1), (0 / 1)], ![(-1773880330881 / 1000000000000), (110126392049 / 125000000000), (880947158131 / 1000000000000), (-354823093789 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-179850383043 / 100000000000), (453385760559 / 500000000000), (226676226329 / 250000000000), (-14052020531 / 7812500000), (0 / 1)], ![(-112479382687 / 31250000000), (-590016925719 / 200000000000), (-1799735439601 / 500000000000), (0 / 1), (0 / 1)], ![(-2771688017 / 1562500000), (881011136393 / 1000000000000), (220236789533 / 250000000000), (-110882216809 / 62500000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4470485736989 / 1000000000000), (-1811154828613 / 1000000000000), (-4520986104853 / 1000000000000), (-3246741565807 / 500000000000), (-1162505313553 / 1000000000000), (-1162507940721 / 1000000000000), (-32467014417 / 5000000000), (-4521025769313 / 1000000000000), (-905577433873 / 500000000000), (-4470447997431 / 1000000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1117621434247 / 250000000000), (-452788707153 / 250000000000), (-4520986104851 / 1000000000000), (-6493483131613 / 1000000000000), (-72656582097 / 62500000000), (-14531349259 / 12500000000), (-6493402883399 / 1000000000000), (-141282055291 / 31250000000), (-362230973549 / 200000000000), (-447044799743 / 100000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 2 26 3 c : ℝ) / 1000000000000) ≤
          (1672 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1672 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1672 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
