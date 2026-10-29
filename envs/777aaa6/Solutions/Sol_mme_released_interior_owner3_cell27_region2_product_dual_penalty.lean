-- Prove2me | solution 1 for mme_released_interior_owner3_cell27_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:30:21.890164+00:00
-- url     : https://prove2.me/submissions/6e0509cc-9d63-4599-b978-44016d2d4a52

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 3 27 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5182439766447048175602335529 / 100000000000000000000000000000), (74540678461072354593215389269 / 100000000000000000000000000000), (37270304610117527296953898821 / 50000000000000000000000000000), (2591326607207674086733927923 / 50000000000000000000000000000), (1 / 1)], ![(5044849103889049551508961109 / 100000000000000000000000000000), (67664002876903023359971230963 / 100000000000000000000000000000), (67664110873127023358891268723 / 100000000000000000000000000000), (630583844408093694161555919 / 12500000000000000000000000000), (1 / 1)], ![(32007803662526379921963374733 / 100000000000000000000000000000), (12438236081987575617639180123 / 20000000000000000000000000000), (32007824330801579921756691981 / 100000000000000000000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![4, 1, 1, 4, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2959894243217553 / 1000000000000000), (-36728148750667 / 125000000000000), (-146913059452891 / 500000000000000), (-2959853057293081 / 1000000000000000), (0 / 1)], ![(-1493401221330869 / 500000000000000), (-390615862740477 / 1000000000000000), (-390614266675609 / 1000000000000000), (-2986837795904867 / 1000000000000000), (0 / 1)], ![(-1139190448464519 / 1000000000000000), (-474956990349131 / 1000000000000000), (-569594901369299 / 500000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2959894243217549 / 1000000000000000), (-58765038001067 / 200000000000000), (-293826118905781 / 1000000000000000), (-739963264323269 / 250000000000000), (0 / 1)], ![(-1493401221330867 / 500000000000000), (-15624634509619 / 40000000000000), (-390614266675607 / 1000000000000000), (-2986837795904863 / 1000000000000000), (0 / 1)], ![(-1139190448464517 / 1000000000000000), (-474956990349129 / 1000000000000000), (-227837960547719 / 200000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([6, 3, 6, 9, 2, 2, 9, 6, 3, 6] : List ℤ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1105442098464619 / 250000000000000), (-1823345597352467 / 1000000000000000), (-1122928274641963 / 250000000000000), (-640762620042401 / 100000000000000), (-1159469864363819 / 1000000000000000), (-289868095801549 / 250000000000000), (-6407549530195971 / 1000000000000000), (-280734496632487 / 62500000000000), (-911672809392427 / 500000000000000), (-4421733421269723 / 1000000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-442176839385847 / 100000000000000), (-113959099834529 / 62500000000000), (-4491713098567847 / 1000000000000000), (-3203813100212001 / 500000000000000), (-144933733045477 / 125000000000000), (-579736191603097 / 500000000000000), (-3203774765097981 / 500000000000000), (-2245875973059893 / 500000000000000), (-36466912375697 / 20000000000000), (-4421733421269717 / 1000000000000000)] : List ℚ).getD
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
        (splitWeight 3 27 2 c : ℝ) / 1000000000000) ≤
          (431 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (431 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((431 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
