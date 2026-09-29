-- Prove2me | solution 1 for mme_released_interior_owner2_cell28_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:34.692293+00:00
-- url     : https://prove2.me/submissions/c4abc93b-814a-4830-8547-863034ce0af3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 2 28 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(276187541827 / 1000000000000), (1425492948581 / 1000000000000), (712745290393 / 500000000000), (69046716497 / 250000000000), (1 / 1)], ![(26652100207500000000000000000000000 / 8767120275144089315149443928678091567), (1017314049959000000000000000000000000 / 8767120275144089315149443928678091567), (6589884990624000000000000000000000000 / 8767120275144089315149443928678091567), (1017311030792500000000000000000000000 / 8767120275144089315149443928678091567), (26652098101000000000000000000000000 / 8767120275144089315149443928678091567)], ![(393768853409 / 1000000000000), (15750728673 / 40000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1286675144647 / 1000000000000), (354517682729 / 1000000000000), (88629005423 / 250000000000), (-2010433737 / 1562500000), (0 / 1)], ![(-5795895716029 / 1000000000000), (-2153842521839 / 1000000000000), (-285472495333 / 1000000000000), (-1076922744813 / 500000000000), (-2897947897533 / 500000000000)], ![(-186398241663 / 200000000000), (-931992824961 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-643337572323 / 500000000000), (35451768273 / 100000000000), (354516021693 / 1000000000000), (-1286677591679 / 1000000000000), (0 / 1)], ![(-1448973929007 / 250000000000), (-1076921260919 / 500000000000), (-71368123833 / 250000000000), (-17230763917 / 8000000000), (-1159179159013 / 200000000000)], ![(-465995604157 / 500000000000), (-1456238789 / 1562500000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-1602913226243 / 200000000000), (-546263865021 / 200000000000), (-2186255660917 / 500000000000), (-862947637563 / 1000000000000), (-215736920489 / 250000000000), (-4372513459241 / 1000000000000), (-2731319015217 / 1000000000000), (-8014562147697 / 1000000000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4007283065607 / 500000000000), (-170707457819 / 62500000000), (-4372511321833 / 1000000000000), (-431473818781 / 500000000000), (-172589536391 / 200000000000), (-109312836481 / 25000000000), (-170707438451 / 62500000000), (-500910134231 / 62500000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 2 28 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
