-- Prove2me | solution 1 for mme_released_interior_owner3_cell26_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:29:23.498867+00:00
-- url     : https://prove2.me/submissions/22c6fb0a-7887-4939-9270-fe6161e01889

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 3 26 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(625708095285893742919047141 / 12500000000000000000000000000), (74882259494340951177405056583 / 100000000000000000000000000000), (74882264373178151177356268211 / 100000000000000000000000000000), (1001131277459289988687225407 / 20000000000000000000000000000), (1 / 1)], ![(37887690023338921123099766607 / 100000000000000000000000000000), (4532941607516654670583924833 / 6250000000000000000000000000), (18943845139998710561548600011 / 50000000000000000000000000000), (1 / 1), (1 / 1)], ![(4048449629632059515503703679 / 100000000000000000000000000000), (28792749506291412072504937083 / 50000000000000000000000000000), (57585496946114124145030538853 / 100000000000000000000000000000), (506056865274894939431347251 / 12500000000000000000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![1, 0, 1, 0, 0], ![5, 1, 1, 5, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-187162497650179 / 62500000000000), (-289253179403001 / 1000000000000000), (-144626557124779 / 500000000000000), (-1497300817753429 / 500000000000000), (0 / 1)], ![(-970543928154157 / 1000000000000000), (-321210373514603 / 1000000000000000), (-194108784275993 / 200000000000000), (0 / 1), (0 / 1)], ![(-1603418092828699 / 500000000000000), (-551899403235187 / 1000000000000000), (-110379887824083 / 200000000000000), (-1603417439175557 / 500000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-149729998120143 / 50000000000000), (-289253179403 / 1000000000000), (-289253114249557 / 1000000000000000), (-1497300817753427 / 500000000000000), (0 / 1)], ![(-194108785630831 / 200000000000000), (-160605186757301 / 500000000000000), (-970543921379963 / 1000000000000000), (0 / 1), (0 / 1)], ![(-3206836185657393 / 1000000000000000), (-110379880647037 / 200000000000000), (-551899439120413 / 1000000000000000), (-3206834878351109 / 1000000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([6, 9, 3, 2, 7, 7, 2, 3, 9, 6] : List ℤ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2235217329711959 / 500000000000000), (-3246714164620009 / 500000000000000), (-905581576492317 / 500000000000000), (-290625561923491 / 250000000000000), (-4521043348201053 / 1000000000000000), (-2260520854486227 / 500000000000000), (-232500469670373 / 200000000000000), (-362232626100521 / 200000000000000), (-6493425353069381 / 1000000000000000), (-11176083575327 / 2500000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-558804332427989 / 125000000000000), (-649342832924001 / 100000000000000), (-181116315298463 / 100000000000000), (-1162502247693961 / 1000000000000000), (-4521043348201047 / 1000000000000000), (-4521041708972447 / 1000000000000000), (-581251174175931 / 500000000000000), (-1811163130502601 / 1000000000000000), (-6493425353069373 / 1000000000000000), (-2235216715065397 / 500000000000000)] : List ℚ).getD
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
        (splitWeight 3 26 2 c : ℝ) / 1000000000000) ≤
          (1672 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1672 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1672 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
