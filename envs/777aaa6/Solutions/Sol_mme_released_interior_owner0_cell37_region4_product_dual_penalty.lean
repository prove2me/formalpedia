-- Prove2me | solution 1 for mme_released_interior_owner0_cell37_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:17.725182+00:00
-- url     : https://prove2.me/submissions/ad3e9f05-7307-44a9-b36b-fc37fd15868c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157543882748000000000000000000000000 / 7560218670049715420445881446311920163), (140966185984000000000000000000000000 / 280008098890730200757254868381922969), (1268695628455000000000000000000000000 / 2520072890016571806815293815437306721), (157543788982000000000000000000000000 / 7560218670049715420445881446311920163)], ![(586366076971 / 1000000000000), (1045666053917 / 1000000000000), (586365933261 / 1000000000000), (1 / 1), (1 / 1)], ![(599633430417 / 1000000000000), (18738541091 / 31250000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-774190270657 / 200000000000), (-34314924073 / 50000000000), (-137259703449 / 200000000000), (-3870951948459 / 1000000000000)], ![(-133452744931 / 250000000000), (893081091 / 20000000000), (-53381122481 / 100000000000), (0 / 1), (0 / 1)], ![(-511436759777 / 1000000000000), (-511436952403 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-967737838321 / 250000000000), (-686298481459 / 1000000000000), (-171574629311 / 250000000000), (-1935475974229 / 500000000000)], ![(-533810979723 / 1000000000000), (44654054551 / 1000000000000), (-533811224809 / 1000000000000), (0 / 1), (0 / 1)], ![(-15982398743 / 31250000000), (-255718476201 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4916199530437 / 1000000000000), (-1153081379311 / 1000000000000), (-1731546466047 / 1000000000000), (-173154644937 / 100000000000), (-1153081222473 / 1000000000000), (-4916199687939 / 1000000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1229049882609 / 250000000000), (-115308137931 / 100000000000), (-865773233023 / 500000000000), (-1731546449369 / 1000000000000), (-144135152809 / 125000000000), (-2458099843969 / 500000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 37 4 c : ℝ) / 1000000000000) ≤
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
