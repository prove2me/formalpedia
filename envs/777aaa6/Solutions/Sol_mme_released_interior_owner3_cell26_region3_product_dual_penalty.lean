-- Prove2me | solution 1 for mme_released_interior_owner3_cell26_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:35:33.270482+00:00
-- url     : https://prove2.me/submissions/9369f91f-e99d-4298-911e-1bc3bfb966ea

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 3 26 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5202406121725847975938782741 / 100000000000000000000000000000), (9346744185294206532558147057 / 12500000000000000000000000000), (3738697716077862613022839221 / 5000000000000000000000000000), (2601202403879073987975961209 / 50000000000000000000000000000), (1 / 1)], ![(3753594150686662464058493133 / 10000000000000000000000000000), (729576195651692704238043483 / 1000000000000000000000000000), (37535941686624724640583133749 / 100000000000000000000000000000), (1 / 1), (1 / 1)], ![(4260916524557657390834754423 / 100000000000000000000000000000), (57515113803957124848861960423 / 100000000000000000000000000000), (57515114080555124848859194443 / 100000000000000000000000000000), (4260916229548857390837704511 / 100000000000000000000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![1, 0, 1, 0, 0], ![5, 1, 1, 5, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-739012237926027 / 250000000000000), (-290700577125303 / 1000000000000000), (-58140113180419 / 200000000000000), (-369506150534171 / 125000000000000), (0 / 1)], ![(-979871271839143 / 1000000000000000), (-1970571670801 / 6250000000000), (-122483908381273 / 125000000000000), (0 / 1), (0 / 1)], ![(-3155685902237749 / 1000000000000000), (-553122423959 / 1000000000000), (-69140302393733 / 125000000000000), (-3155685971473747 / 1000000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-369506118963013 / 125000000000000), (-145350288562651 / 500000000000000), (-145350282951047 / 500000000000000), (-739012301068341 / 250000000000000), (0 / 1)], ![(-489935635919571 / 500000000000000), (-315291467328159 / 1000000000000000), (-489935633525091 / 500000000000000), (0 / 1), (0 / 1)], ![(-197230368889859 / 62500000000000), (-276561211979499 / 500000000000000), (-276561209574931 / 500000000000000), (-1577842985736871 / 500000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([6, 9, 3, 2, 6, 6, 2, 3, 9, 6] : List ℤ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4428139948649777 / 1000000000000000), (-6413216979496319 / 1000000000000000), (-227926960943961 / 125000000000000), (-1159186133168173 / 1000000000000000), (-224552359980729 / 50000000000000), (-112276173439767 / 25000000000000), (-579593069779393 / 500000000000000), (-911707838155719 / 500000000000000), (-6413216794101203 / 1000000000000000), (-4428140034687163 / 1000000000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4428139948649771 / 1000000000000000), (-6413216979496311 / 1000000000000000), (-364683137510337 / 200000000000000), (-115918613316817 / 100000000000000), (-2245523599807287 / 500000000000000), (-2245523468795337 / 500000000000000), (-1159186139558783 / 1000000000000000), (-911707838155717 / 500000000000000), (-1282643358820239 / 200000000000000), (-4428140034687157 / 1000000000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 3 26 3 c : ℝ) / 1000000000000) ≤
          (413 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (413 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((413 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
