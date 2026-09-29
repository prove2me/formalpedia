-- Prove2me | solution 1 for mme_released_interior_owner2_cell22_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:21.445983+00:00
-- url     : https://prove2.me/submissions/77f6903c-228e-484c-a023-406386634704

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 2 22 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(583206477969 / 1000000000000), (1051182676107 / 1000000000000), (36450063949 / 62500000000), (1 / 1), (1 / 1)], ![(1 / 1), (77987573771000000000000000000000000 / 3801100391876455845658826932516948861), (1916847762596500000000000000000000000 / 3801100391876455845658826932516948861), (1916837996133500000000000000000000000 / 3801100391876455845658826932516948861), (77987481690500000000000000000000000 / 3801100391876455845658826932516948861)], ![(597969926591 / 1000000000000), (149491806319 / 250000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-539213990721 / 1000000000000), (49915888501 / 1000000000000), (-539223343859 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-777299275447 / 200000000000), (-85576069389 / 125000000000), (-68461365019 / 100000000000), (-3886497557943 / 1000000000000)], ![(-257107408139 / 500000000000), (-102843866753 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1685043721 / 3125000000), (24957944251 / 500000000000), (-269611671929 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1943248188617 / 500000000000), (-684608555111 / 1000000000000), (-684613650189 / 1000000000000), (-1943248778971 / 500000000000)], ![(-514214816277 / 1000000000000), (-128554833441 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-987987810961 / 200000000000), (-574456000189 / 500000000000), (-1738046715247 / 1000000000000), (-69521878987 / 40000000000), (-1148912577967 / 1000000000000), (-4939926364939 / 1000000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1234984763701 / 250000000000), (-1148912000377 / 1000000000000), (-869023357623 / 500000000000), (-869023487337 / 500000000000), (-574456288983 / 500000000000), (-2469963182469 / 500000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 22 4 c : ℝ) / 1000000000000) ≤
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
