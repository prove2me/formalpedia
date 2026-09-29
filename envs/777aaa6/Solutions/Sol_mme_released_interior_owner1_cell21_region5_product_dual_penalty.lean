-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:55.753276+00:00
-- url     : https://prove2.me/submissions/c8eb76e3-c6e8-4f3d-84b4-f6b723363f56

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(415652919314000000000000000000000000 / 19946029840183504390343495190747977643), (262886949249000000000000000000000000 / 6648676613394501463447831730249325881), (415644920225000000000000000000000000 / 19946029840183504390343495190747977643), (1 / 1), (1 / 1)], ![(38849643647 / 1000000000000), (577017255759 / 250000000000), (682109964511 / 40000000000), (2308024199601 / 1000000000000), (485620147 / 12500000000)], ![(406116486111 / 1000000000000), (826251740561 / 1000000000000), (203054330073 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1935467406783 / 500000000000), (-161522450967 / 50000000000), (-3870954058387 / 1000000000000), (0 / 1), (0 / 1)], ![(-1624028187373 / 500000000000), (836411254193 / 1000000000000), (2836311429017 / 1000000000000), (418195916843 / 500000000000), (-3248057195527 / 1000000000000)], ![(-901115248929 / 1000000000000), (-4771394531 / 25000000000), (-901134519361 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-774186962713 / 200000000000), (-3230449019339 / 1000000000000), (-1935477029193 / 500000000000), (0 / 1), (0 / 1)], ![(-649611274949 / 200000000000), (418205627097 / 500000000000), (1418155714509 / 500000000000), (836391833687 / 1000000000000), (-1624028597763 / 500000000000)], ![(-28159851529 / 31250000000), (-190855781239 / 1000000000000), (-2816045373 / 3125000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-2005026814597 / 250000000000), (-1612699376957 / 500000000000), (-483939476473 / 250000000000), (-329517244231 / 100000000000), (-584993371559 / 1000000000000), (-1647586138401 / 500000000000), (-967878938159 / 500000000000), (-5039685301 / 1562500000), (-2005036238113 / 250000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020107258387 / 1000000000000), (-3225398753913 / 1000000000000), (-1935757905891 / 1000000000000), (-3295172442309 / 1000000000000), (-292496685779 / 500000000000), (-3295172276801 / 1000000000000), (-1935757876317 / 1000000000000), (-3225398592639 / 1000000000000), (-8020144952451 / 1000000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 1 21 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
