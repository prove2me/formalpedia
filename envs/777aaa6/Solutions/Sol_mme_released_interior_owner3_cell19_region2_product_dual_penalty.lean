-- Prove2me | solution 1 for mme_released_interior_owner3_cell19_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:11:58.432644+00:00
-- url     : https://prove2.me/submissions/89b11f02-2e1c-4bbf-9e92-94700bdf0cf9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19910567188830700894328111691 / 50000000000000000000000000000), (41192317910372488076820896271 / 50000000000000000000000000000), (39821136284594301788637154053 / 100000000000000000000000000000), (1 / 1), (1 / 1)], ![(19876623391028901233766089709 / 50000000000000000000000000000), (7408700882034225912991179657 / 10000000000000000000000000000), (3975324868827260246751311727 / 10000000000000000000000000000), (1 / 1), (1 / 1)], ![(100727717250698992722827493 / 50000000000000000000000000000), (2881920071743071180799282569 / 25000000000000000000000000000), (46163237413424238367625865753 / 50000000000000000000000000000), (5763839997786642361600022133 / 50000000000000000000000000000), (201463367798897985366322011 / 100000000000000000000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![9, 3, 0, 3, 9]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-92077240012191 / 100000000000000), (-38754244988863 / 200000000000000), (-460386176117227 / 500000000000000), (0 / 1), (0 / 1)], ![(-922478668171617 / 1000000000000000), (-149964994309927 / 500000000000000), (-184495724044089 / 200000000000000), (0 / 1), (0 / 1)], ![(-3103678638386229 / 500000000000000), (-432083812256599 / 200000000000000), (-638714008651 / 8000000000000), (-432083817312239 / 200000000000000), (-6207317897634747 / 1000000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-920772400121909 / 1000000000000000), (-96885612472157 / 500000000000000), (-230193088058613 / 250000000000000), (0 / 1), (0 / 1)], ![(-184495733634323 / 200000000000000), (-299929988619853 / 1000000000000000), (-922478620220443 / 1000000000000000), (0 / 1), (0 / 1)], ![(-124147145535449 / 20000000000000), (-135026191330187 / 62500000000000), (-39919625540687 / 500000000000000), (-2160419086561191 / 1000000000000000), (-6207317897634739 / 1000000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8050608249227519 / 1000000000000000), (-1638334454162097 / 500000000000000), (-1690560700027101 / 500000000000000), (-1923090270938981 / 1000000000000000), (-71692558080689 / 125000000000000), (-961545135986067 / 500000000000000), (-845280369346501 / 250000000000000), (-327666897780063 / 100000000000000), (-8050568965928477 / 1000000000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-2012652062306877 / 250000000000000), (-3276668908324189 / 1000000000000000), (-3381121400054197 / 1000000000000000), (-961545135469489 / 500000000000000), (-57354046464551 / 100000000000000), (-192309027197213 / 100000000000000), (-3381121477385999 / 1000000000000000), (-5242670364481 / 1600000000000), (-8050568965928467 / 1000000000000000)] : List ℚ).getD
    ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 3 19 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
