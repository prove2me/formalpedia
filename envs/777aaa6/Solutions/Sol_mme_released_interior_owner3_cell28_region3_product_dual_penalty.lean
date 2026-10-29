-- Prove2me | solution 1 for mme_released_interior_owner3_cell28_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:15:59.763192+00:00
-- url     : https://prove2.me/submissions/52a602fb-62ba-4945-b80f-c2710f064095

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 3 28 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(18820803816137511791961838623 / 100000000000000000000000000000), (94810631724184151893682758149 / 100000000000000000000000000000), (94810643112077751893568879213 / 100000000000000000000000000000), (18820802841896711791971581031 / 100000000000000000000000000000), (1 / 1)], ![(174397878135298256021218647 / 50000000000000000000000000000), (13179349830820568206501691793 / 100000000000000000000000000000), (44804290741669251957092583303 / 50000000000000000000000000000), (1317935151298086820648487019 / 10000000000000000000000000000), (174400542168098255994578319 / 50000000000000000000000000000)], ![(1562499914517684375000854823 / 3125000000000000000000000000), (50000002735433199999972645663 / 100000000000000000000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![8, 3, 0, 3, 8], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-26096989718787 / 15625000000000), (-53288634026059 / 1000000000000000), (-53288513914077 / 1000000000000000), (-1670207393766407 / 1000000000000000), (0 / 1)], ![(-2829219469832411 / 500000000000000), (-12665743675711 / 6250000000000), (-109719095109697 / 1000000000000000), (-506629715119427 / 250000000000000), (-176825739505569 / 31250000000000)], ![(-69314723526863 / 100000000000000), (-173286781462821 / 250000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-334041468400473 / 200000000000000), (-26644317013029 / 500000000000000), (-13322128478519 / 250000000000000), (-417551848441601 / 250000000000000), (0 / 1)], ![(-2829219469832407 / 500000000000000), (-2026518988113757 / 1000000000000000), (-1714360861089 / 15625000000000), (-253314857559713 / 125000000000000), (-5658423664178201 / 1000000000000000)], ![(-173286808817157 / 250000000000000), (-346573562925641 / 500000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 4, 1, 6, 6, 1, 4, 12] : List ℤ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4010889120724647 / 500000000000000), (-2772954729772369 / 1000000000000000), (-214038711073093 / 250000000000000), (-1097468404287191 / 250000000000000), (-68591770755177 / 15625000000000), (-85615485498701 / 100000000000000), (-2772954627879087 / 1000000000000000), (-8021793459282593 / 1000000000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-2005444560362321 / 250000000000000), (-554590945954473 / 200000000000000), (-856154844292371 / 1000000000000000), (-2194936808574379 / 500000000000000), (-4389873328331323 / 1000000000000000), (-3344354902293 / 3906250000000), (-2772954627879083 / 1000000000000000), (-4010896729641291 / 500000000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 3 28 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
