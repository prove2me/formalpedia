-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:13:14.814056+00:00
-- url     : https://prove2.me/submissions/096ec2c2-2130-47a6-8c3b-2170dae6d1ea

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(7483108854650625168911453493 / 20000000000000000000000000000), (9534363454096004656365459039 / 12500000000000000000000000000), (37415540569820325844594301793 / 100000000000000000000000000000), (1 / 1), (1 / 1)], ![(269780663151897302193368481 / 100000000000000000000000000000), (16028391146273539716088537263 / 100000000000000000000000000000), (23686515888852663134841111471 / 20000000000000000000000000000), (16028386266082539716137339173 / 100000000000000000000000000000), (269792015183897302079848161 / 100000000000000000000000000000)], ![(32567565144867374324348551323 / 100000000000000000000000000000), (15418047305515145819526944847 / 25000000000000000000000000000), (32567564883946574324351160531 / 100000000000000000000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![9, 3, 0, 3, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-491541972817563 / 500000000000000), (-33853270795323 / 125000000000000), (-983084044616259 / 1000000000000000), (0 / 1), (0 / 1)], ![(-1478829048702667 / 250000000000000), (-457702147394189 / 250000000000000), (84586831418139 / 500000000000000), (-228851111756059 / 125000000000000), (-1478818529237489 / 250000000000000)], ![(-1121853327097529 / 1000000000000000), (-483337098635349 / 1000000000000000), (-560926667554603 / 500000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-245770986408781 / 250000000000000), (-270826166362583 / 1000000000000000), (-491542022308129 / 500000000000000), (0 / 1), (0 / 1)], ![(-295765809740533 / 50000000000000), (-1830808589576753 / 1000000000000000), (169173662836279 / 1000000000000000), (-457702223512117 / 250000000000000), (-5915274116949947 / 1000000000000000)], ![(-560926663548763 / 500000000000000), (-483337098635347 / 1000000000000000), (-1121853335109203 / 1000000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4010105694841343 / 500000000000000), (-402936047624147 / 125000000000000), (-1935763710675059 / 1000000000000000), (-206076871583307 / 62500000000000), (-584989602161623 / 1000000000000000), (-1648614862907171 / 500000000000000), (-967881808055221 / 500000000000000), (-3223488097563893 / 1000000000000000), (-401012678726801 / 50000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-2005052847420669 / 250000000000000), (-3223488380993171 / 1000000000000000), (-120985231917191 / 62500000000000), (-3297229945332907 / 1000000000000000), (-292494801080811 / 500000000000000), (-3297229725814337 / 1000000000000000), (-1935763616110439 / 1000000000000000), (-201468006097743 / 62500000000000), (-8020253574536009 / 1000000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
