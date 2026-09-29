-- Prove2me | solution 1 for mme_released_interior_owner2_cell22_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:20.542449+00:00
-- url     : https://prove2.me/submissions/b01b032d-3a59-4b54-9a39-9d6263eeb78c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 2 22 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(116315440617 / 200000000000), (263513376703 / 250000000000), (145394603069 / 250000000000), (1 / 1), (1 / 1)], ![(1 / 1), (155256889127000000000000000000000000 / 7624797769919578647776564299755346239), (3845539101740000000000000000000000000 / 7624797769919578647776564299755346239), (3845543222843000000000000000000000000 / 7624797769919578647776564299755346239), (155256864854000000000000000000000000 / 7624797769919578647776564299755346239)], ![(149384344049 / 250000000000), (597537994229 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-135502887607 / 250000000000), (26321607153 / 500000000000), (-67751183909 / 125000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3894079984909 / 1000000000000), (-17112299963 / 25000000000), (-684490926863 / 1000000000000), (-3894080141249 / 1000000000000)], ![(-51493844283 / 100000000000), (-514937408531 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-542011550427 / 1000000000000), (52643214307 / 1000000000000), (-542009471271 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-973519996227 / 250000000000), (-684491998519 / 1000000000000), (-342245463431 / 500000000000), (-60845002207 / 15625000000)], ![(-514938442829 / 1000000000000), (-51493740853 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-618878358083 / 125000000000), (-1146786192743 / 1000000000000), (-870719956311 / 500000000000), (-1741439885823 / 1000000000000), (-229357231077 / 200000000000), (-1237757533633 / 250000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4951026864663 / 1000000000000), (-573393096371 / 500000000000), (-1741439912621 / 1000000000000), (-870719942911 / 500000000000), (-143348269423 / 125000000000), (-4951030134531 / 1000000000000)] : List ℚ).getD
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
        (splitWeight 2 22 3 c : ℝ) / 1000000000000) ≤
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
