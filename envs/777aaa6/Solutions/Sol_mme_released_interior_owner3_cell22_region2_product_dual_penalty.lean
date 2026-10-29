-- Prove2me | solution 1 for mme_released_interior_owner3_cell22_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:13:33.547691+00:00
-- url     : https://prove2.me/submissions/537fc33b-100c-4fc4-9969-e101f5f32272

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 3 22 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(238018256217809 / 500000000000000), (862798955056353 / 1000000000000000), (476036474789571 / 1000000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (3373861087787 / 125000000000000), (669022982534021 / 1000000000000000), (6690229072341 / 10000000000000), (26990946738899 / 1000000000000000)], ![(137580298795851 / 250000000000000), (275160610558189 / 500000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 5, 1, 1, 5], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-742260720895017 / 1000000000000000), (-147573575575481 / 1000000000000000), (-92782599997161 / 125000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3612255925399239 / 1000000000000000), (-401936865880421 / 1000000000000000), (-25121061152031 / 62500000000000), (-3612253775172129 / 1000000000000000)], ![(-298626589984797 / 500000000000000), (-597253132846253 / 1000000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-148452144179003 / 200000000000000), (-3689339389387 / 25000000000000), (-371130399988643 / 500000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1806127962699617 / 500000000000000), (-401936865880419 / 1000000000000000), (-200968489216247 / 500000000000000), (-903063443793031 / 250000000000000)], ![(-74656647496199 / 125000000000000), (-597253132846251 / 1000000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([7, 2, 3, 3, 2, 7] : List ℤ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4951767676036737 / 1000000000000000), (-114676373397757 / 100000000000000), (-870725422913651 / 500000000000000), (-348290166434753 / 200000000000000), (-1146763574302153 / 1000000000000000), (-2475884929111399 / 500000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-495176767603673 / 100000000000000), (-1146763733977567 / 1000000000000000), (-1741450845827299 / 1000000000000000), (-1741450832173761 / 1000000000000000), (-22935271486043 / 20000000000000), (-4951769858222791 / 1000000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 3 22 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
