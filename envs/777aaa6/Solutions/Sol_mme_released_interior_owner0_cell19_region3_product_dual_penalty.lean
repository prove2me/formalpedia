-- Prove2me | solution 1 for mme_released_interior_owner0_cell19_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:25.895672+00:00
-- url     : https://prove2.me/submissions/3483075d-f4e9-4961-8748-02e36133778d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(103834876303250000000000000000000000 / 5088212200909602909838707366023932333), (193367512760500000000000000000000000 / 5088212200909602909838707366023932333), (103835266032250000000000000000000000 / 5088212200909602909838707366023932333), (1 / 1), (1 / 1)], ![(200569097083 / 500000000000), (207639238591 / 250000000000), (401139697271 / 1000000000000), (1 / 1), (1 / 1)], ![(38940354331 / 1000000000000), (1114494362389 / 500000000000), (17853969350581 / 1000000000000), (445799453431 / 200000000000), (38940355793 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-486484987599 / 125000000000), (-3270089220917 / 1000000000000), (-1945938073723 / 500000000000), (0 / 1), (0 / 1)], ![(-91344928719 / 100000000000), (-185658773877 / 1000000000000), (-913445540097 / 1000000000000), (0 / 1), (0 / 1)], ![(-3245724179671 / 1000000000000), (801547995969 / 1000000000000), (1441112928043 / 500000000000), (400775914181 / 500000000000), (-1622862071063 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3891879900791 / 1000000000000), (-817522305229 / 250000000000), (-778375229489 / 200000000000), (0 / 1), (0 / 1)], ![(-913449287189 / 1000000000000), (-46414693469 / 250000000000), (-3568146641 / 3906250000), (0 / 1), (0 / 1)], ![(-324572417967 / 100000000000), (80154799597 / 100000000000), (2882225856087 / 1000000000000), (801551828363 / 1000000000000), (-25965793137 / 8000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1610210665883 / 200000000000), (-818996707367 / 250000000000), (-1923099589157 / 1000000000000), (-422748337309 / 125000000000), (-143380534677 / 250000000000), (-845496686581 / 250000000000), (-1923099574193 / 1000000000000), (-3275986942201 / 1000000000000), (-503190366643 / 62500000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4025526664707 / 500000000000), (-3275986829467 / 1000000000000), (-480774897289 / 250000000000), (-3381986698471 / 1000000000000), (-573522138707 / 1000000000000), (-3381986746323 / 1000000000000), (-120193723387 / 62500000000), (-16379934711 / 5000000000), (-8051045866287 / 1000000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 0 19 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
