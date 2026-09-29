-- Prove2me | solution 1 for mme_released_interior_owner1_cell28_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:35.269043+00:00
-- url     : https://prove2.me/submissions/86a2b0d0-9e06-4c5f-85d5-98f3a6619822

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 1 28 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(275048004631000000000000000000000000 / 17564100271581199897812146624707518901), (1430321836732000000000000000000000000 / 17564100271581199897812146624707518901), (1430323390708000000000000000000000000 / 17564100271581199897812146624707518901), (275048539276000000000000000000000000 / 17564100271581199897812146624707518901), (1 / 1)], ![(26659148073 / 500000000000), (63580873787 / 31250000000), (3292528767983 / 250000000000), (2034591971371 / 1000000000000), (13329574227 / 250000000000)], ![(196713584029 / 500000000000), (393427588097 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-831333339173 / 200000000000), (-2507957582009 / 1000000000000), (-2507956495557 / 1000000000000), (-4156664752043 / 1000000000000), (0 / 1)], ![(-1465737869717 / 500000000000), (177573330579 / 250000000000), (515590050629 / 200000000000), (710295293321 / 1000000000000), (-1465737862571 / 500000000000)], ![(-932859315783 / 1000000000000), (-932858248143 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-519583336983 / 125000000000), (-313494697751 / 125000000000), (-626989123889 / 250000000000), (-2078332376021 / 500000000000), (0 / 1)], ![(-2931475739433 / 1000000000000), (710293322317 / 1000000000000), (1288975126573 / 500000000000), (355147646661 / 500000000000), (-2931475725141 / 1000000000000)], ![(-466429657891 / 500000000000), (-466429124071 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-8021001735653 / 1000000000000), (-1094807412671 / 250000000000), (-1365260802233 / 500000000000), (-215716394251 / 250000000000), (-215716389549 / 250000000000), (-682630355347 / 250000000000), (-2189615372769 / 500000000000), (-401049937007 / 50000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-2005250433913 / 250000000000), (-4379229650683 / 1000000000000), (-546104320893 / 200000000000), (-862865577003 / 1000000000000), (-172573111639 / 200000000000), (-2730521421387 / 1000000000000), (-4379230745537 / 1000000000000), (-8020998740139 / 1000000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 28 0 c : ℝ) / 1000000000000) ≤
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
