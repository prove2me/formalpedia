-- Prove2me | solution 1 for Erdos146.binomialProbabilityMass_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:06:51.976217+00:00
-- url     : https://prove2.me/submissions/2d4ea8f3-88bf-4230-bc77-9ce9bc4ecd85

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by
  have hc :
      ((trialCount.choose (successCount + 1) : ℕ) : ℝ) *
          ((successCount + 1 : ℕ) : ℝ) =
        ((trialCount.choose successCount : ℕ) : ℝ) *
          ((trialCount - successCount : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq trialCount successCount
  have hs : trialCount - successCount =
      (trialCount - (successCount + 1)) + 1 := by omega
  unfold binomialProbabilityMass
  rw [hs] at hc ⊢
  simp only [pow_succ]
  linear_combination
    (probability ^ successCount *
      (1 - probability) ^ (trialCount - (successCount + 1)) *
      probability * (1 - probability)) * hc
