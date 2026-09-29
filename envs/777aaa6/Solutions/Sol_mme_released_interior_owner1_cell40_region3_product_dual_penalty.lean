-- Prove2me | solution 1 for mme_released_interior_owner1_cell40_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:05.233621+00:00
-- url     : https://prove2.me/submissions/3acc96bb-7f00-4502-999b-1e5d220e087e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 1 40 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1 / 1), (19071996100156250000000000000000000 / 116669757056185047406604406294772999), (61086305126656250000000000000000000 / 116669757056185047406604406294772999), (19071997006875000000000000000000000 / 116669757056185047406604406294772999)], ![(853080250431 / 1000000000000), (426540135661 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(853080259279 / 1000000000000), (426540140079 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 0, 3, 1, 3], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-362225253623 / 200000000000), (-647059652143 / 1000000000000), (-1811126220573 / 1000000000000)], ![(-39725413923 / 250000000000), (-158901631203 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-3972541133 / 25000000000), (-79450810423 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-905563134057 / 500000000000), (-323529826071 / 500000000000), (-452781555143 / 250000000000)], ![(-158901655691 / 1000000000000), (-79450815601 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-158901645319 / 1000000000000), (-31780324169 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 40) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-532232380041 / 250000000000), (-482431464333 / 500000000000), (-24121573217 / 25000000000), (-425785904317 / 200000000000)] : List ℚ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-2128929520163 / 1000000000000), (-192972585733 / 200000000000), (-964862928679 / 1000000000000), (-133058095099 / 62500000000)] : List ℚ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 40) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 40 =>
        (splitWeight 1 40 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 40, ∏ i, weights i (c.val i) ≤ 1 := by
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
