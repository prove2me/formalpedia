-- Prove2me | solution 1 for mme_released_interior_owner3_cell27_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:30:52.380221+00:00
-- url     : https://prove2.me/submissions/f51d54d8-d6c2-48f6-a975-53e58cf0a309

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 3 27 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(24946875494681 / 500000000000000), (93300938137643 / 125000000000000), (373203358776229 / 500000000000000), (9979196985407 / 200000000000000), (1 / 1)], ![(47957451176613 / 1000000000000000), (8470591380271 / 12500000000000), (677648468779441 / 1000000000000000), (47955538778177 / 1000000000000000), (1 / 1)], ![(64595152712541 / 200000000000000), (309091889420311 / 500000000000000), (161488000916143 / 500000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![4, 1, 1, 4, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-299785951474079 / 100000000000000), (-146241787216857 / 500000000000000), (-146242314776599 / 500000000000000), (-1498907370923003 / 500000000000000), (0 / 1)], ![(-1898400684381 / 625000000000), (-97282079376637 / 250000000000000), (-389126608126531 / 1000000000000000), (-1518740486393549 / 500000000000000), (0 / 1)], ![(-1130177993984361 / 1000000000000000), (-480969488967393 / 1000000000000000), (-282544314063139 / 250000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1498929757370393 / 500000000000000), (-292483574433713 / 1000000000000000), (-292484629553197 / 1000000000000000), (-2997814741846001 / 1000000000000000), (0 / 1)], ![(-759360273752399 / 250000000000000), (-194564158753273 / 500000000000000), (-389126608126529 / 1000000000000000), (-3037480972787093 / 1000000000000000), (0 / 1)], ![(-565088996992179 / 500000000000000), (-480969488967391 / 1000000000000000), (-1130177256252553 / 1000000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([6, 3, 7, 9, 2, 2, 9, 7, 3, 6] : List ℤ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-557987924807573 / 125000000000000), (-905629028393961 / 500000000000000), (-4521103185239681 / 1000000000000000), (-1297478529615019 / 200000000000000), (-1162718482101573 / 1000000000000000), (-1162721235695453 / 1000000000000000), (-3243654046070389 / 500000000000000), (-1130286338852111 / 250000000000000), (-905628986680487 / 500000000000000), (-2231931997723849 / 500000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-2231951699230289 / 500000000000000), (-905629028393959 / 500000000000000), (-2260551592619837 / 500000000000000), (-6487392648075087 / 1000000000000000), (-116271848210157 / 100000000000000), (-1162721235695451 / 1000000000000000), (-6487308092140769 / 1000000000000000), (-4521145355408437 / 1000000000000000), (-1811257973360971 / 1000000000000000), (-1115965998861923 / 250000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 3 27 3 c : ℝ) / 1000000000000) ≤
          (1649 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1649 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1649 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
