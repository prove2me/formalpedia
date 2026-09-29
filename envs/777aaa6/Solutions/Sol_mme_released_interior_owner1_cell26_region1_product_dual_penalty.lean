-- Prove2me | solution 1 for mme_released_interior_owner1_cell26_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:29.175453+00:00
-- url     : https://prove2.me/submissions/4be3a053-c126-4f86-9fc0-b34c8cba8e35

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(10611081547250000000000000000000000 / 992792734774537799504488074651568571), (152511744898875000000000000000000000 / 992792734774537799504488074651568571), (152518781936250000000000000000000000 / 992792734774537799504488074651568571), (10612491453437500000000000000000000 / 992792734774537799504488074651568571), (1 / 1)], ![(111176068969 / 250000000000), (54026075751 / 62500000000), (55593147857 / 125000000000), (1 / 1), (1 / 1)], ![(17504640623 / 100000000000), (1181371852663 / 500000000000), (472570372833 / 200000000000), (175071630613 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2269311515963 / 500000000000), (-1873280307137 / 1000000000000), (-117077135453 / 62500000000), (-2269245084821 / 500000000000), (0 / 1)], ![(-10129322079 / 12500000000), (-36424935613 / 250000000000), (-810253783623 / 1000000000000), (0 / 1), (0 / 1)], ![(-435676040439 / 250000000000), (859823530759 / 1000000000000), (214967326627 / 250000000000), (-871280035509 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-181544921277 / 40000000000), (-29270004799 / 15625000000), (-1873234167247 / 1000000000000), (-4538490169641 / 1000000000000), (0 / 1)], ![(-810345766319 / 1000000000000), (-145699742451 / 1000000000000), (-405126891811 / 500000000000), (0 / 1), (0 / 1)], ![(-348540832351 / 200000000000), (21495588269 / 25000000000), (859869306509 / 1000000000000), (-1742560071017 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-7017207037 / 1562500000), (-6413069985377 / 1000000000000), (-911715935119 / 500000000000), (-46367297811 / 40000000000), (-2214034471217 / 500000000000), (-4428074899133 / 1000000000000), (-579591040989 / 500000000000), (-911715968639 / 500000000000), (-6413081225807 / 1000000000000), (-4491017385447 / 1000000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4491012503679 / 1000000000000), (-200408437043 / 31250000000), (-1823431870237 / 1000000000000), (-579591222637 / 500000000000), (-4428068942433 / 1000000000000), (-1107018724783 / 250000000000), (-1159182081977 / 1000000000000), (-1823431937277 / 1000000000000), (-3206540612903 / 500000000000), (-2245508692723 / 500000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 26 1 c : ℝ) / 1000000000000) ≤
          (414 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (414 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((414 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
