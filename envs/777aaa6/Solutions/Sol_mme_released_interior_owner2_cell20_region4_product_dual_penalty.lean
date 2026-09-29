-- Prove2me | solution 1 for mme_released_interior_owner2_cell20_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:13.174812+00:00
-- url     : https://prove2.me/submissions/5a2967ff-6e68-44f1-b968-0b1ad36684b2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 2 20 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(443441916169 / 1000000000000), (6793932843 / 8000000000), (44351168861 / 100000000000), (1 / 1), (1 / 1)], ![(170227171329000000000000000000000000 / 16244674453822251308843820246876889313), (2401443603598000000000000000000000000 / 16244674453822251308843820246876889313), (2401632605098000000000000000000000000 / 16244674453822251308843820246876889313), (170267169916000000000000000000000000 / 16244674453822251308843820246876889313), (1 / 1)], ![(32850394487 / 200000000000), (249160027867 / 100000000000), (2491796350907 / 1000000000000), (164290583287 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-406594226367 / 500000000000), (-81705778371 / 500000000000), (-813031122203 / 1000000000000), (0 / 1), (0 / 1)], ![(-4558386561197 / 1000000000000), (-23896188389 / 12500000000), (-477904092733 / 250000000000), (-2279075808493 / 500000000000), (0 / 1)], ![(-1806353612953 / 1000000000000), (912925186241 / 1000000000000), (22825096911 / 25000000000), (-1806118569721 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-813188452733 / 1000000000000), (-163411556741 / 1000000000000), (-406515561101 / 500000000000), (0 / 1), (0 / 1)], ![(-1139596640299 / 250000000000), (-1911695071119 / 1000000000000), (-1911616370931 / 1000000000000), (-911630323397 / 200000000000), (0 / 1)], ![(-225794201619 / 125000000000), (456462593121 / 500000000000), (913003876441 / 1000000000000), (-45152964243 / 25000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6499326791357 / 1000000000000), (-2231041025461 / 500000000000), (-70858547763 / 15625000000), (-1162238308291 / 1000000000000), (-1811282004153 / 1000000000000), (-226410243041 / 125000000000), (-290559574583 / 250000000000), (-1133736516107 / 250000000000), (-557760391307 / 125000000000), (-1299865378877 / 200000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1624831697839 / 250000000000), (-4462082050921 / 1000000000000), (-4534947056831 / 1000000000000), (-116223830829 / 100000000000), (-226410250519 / 125000000000), (-1811281944327 / 1000000000000), (-1162238298331 / 1000000000000), (-4534946064427 / 1000000000000), (-892416626091 / 200000000000), (-406207930899 / 62500000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 2 20 4 c : ℝ) / 1000000000000) ≤
          (1591 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1591 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1591 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
