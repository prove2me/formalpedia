-- Prove2me | solution 1 for mme_released_interior_owner4_cell37_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:20:09.641982+00:00
-- url     : https://prove2.me/submissions/587bfe6e-565b-47e3-a61f-69111169f83a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 4 37 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (19732198439 / 125000000000), (3800677159257 / 1000000000000), (3800680786867 / 1000000000000), (157861107633 / 1000000000000)], ![(293206971401000000000000000000000000 / 3775697962037238080198254839116225583), (523433050936000000000000000000000000 / 3775697962037238080198254839116225583), (293207725594000000000000000000000000 / 3775697962037238080198254839116225583), (1 / 1), (1 / 1)], ![(599302750539 / 1000000000000), (299651774889 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-230757749659 / 125000000000), (1335179250661 / 1000000000000), (333795051281 / 250000000000), (-923019849087 / 500000000000)], ![(-1277730894261 / 500000000000), (-987965700243 / 500000000000), (-511091843261 / 200000000000), (0 / 1), (0 / 1)], ![(-511988381943 / 1000000000000), (-511987048329 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1846061997271 / 1000000000000), (667589625331 / 500000000000), (10681441641 / 8000000000), (-1846039698173 / 1000000000000)], ![(-2555461788521 / 1000000000000), (-395186280097 / 200000000000), (-159716201019 / 62500000000), (0 / 1), (0 / 1)], ![(-255994190971 / 500000000000), (-63998381041 / 125000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-2456744934307 / 500000000000), (-1732268631727 / 1000000000000), (-230547915461 / 200000000000), (-23054783963 / 20000000000), (-1732268347589 / 1000000000000), (-98270165239 / 20000000000)] : List ℚ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4913489868613 / 1000000000000), (-866134315863 / 500000000000), (-144092447163 / 125000000000), (-1152739198149 / 1000000000000), (-433067086897 / 250000000000), (-4913508261949 / 1000000000000)] : List ℚ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 4 37 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
