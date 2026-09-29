-- Prove2me | solution 1 for mme_released_interior_owner1_cell22_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:57.347522+00:00
-- url     : https://prove2.me/submissions/f153aa08-d0a3-49b0-b9ee-6dd319a62a50

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(291075495473500000000000000000000000 / 3814271757183471056690785079521223887), (27669081749500000000000000000000000 / 200751145114919529299515004185327573), (291076215290000000000000000000000000 / 3814271757183471056690785079521223887), (1 / 1), (1 / 1)], ![(1 / 1), (38741516733 / 250000000000), (481478136933 / 125000000000), (3851828191777 / 1000000000000), (154969957247 / 1000000000000)], ![(119523305439 / 200000000000), (149404322827 / 250000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-128646118401 / 50000000000), (-990875224763 / 500000000000), (-2572919895069 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-37290982181 / 20000000000), (674273543371 / 500000000000), (674273945299 / 500000000000), (-1864524005063 / 1000000000000)], ![(-257402994799 / 500000000000), (-257402355499 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2572922368019 / 1000000000000), (-79270017981 / 40000000000), (-643229973767 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1864549109049 / 1000000000000), (1348547086743 / 1000000000000), (1348547890599 / 1000000000000), (-932262002531 / 500000000000)], ![(-514805989597 / 1000000000000), (-514804710997 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-495225236271 / 100000000000), (-1739179188417 / 1000000000000), (-574004274263 / 500000000000), (-1148008073779 / 1000000000000), (-1739178797923 / 1000000000000), (-39618189721 / 8000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4952252362709 / 1000000000000), (-27174674819 / 15625000000), (-45920341941 / 40000000000), (-574004036889 / 500000000000), (-869589398961 / 500000000000), (-1238068428781 / 250000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 1 22 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
