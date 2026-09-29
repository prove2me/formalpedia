-- Prove2me | solution 1 for Erdos146.hammingRetentionProbability_mul_wordCount_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:23:47.751896+00:00
-- url     : https://prove2.me/submissions/69e661bc-dd61-4ecb-855b-5a9ec1cda58f

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_eq_exp
import Theorems.Thm_Erdos146_midpointBeta_lt_one

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - midpointBeta) * Real.log 2 :=
    mul_pos (sub_pos.mpr midpointBeta_lt_one) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - midpointBeta) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [hammingRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring
