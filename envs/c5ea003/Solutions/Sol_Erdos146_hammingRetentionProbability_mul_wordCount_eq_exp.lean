-- Prove2me | solution 1 for Erdos146.hammingRetentionProbability_mul_wordCount_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:23:06.354214+00:00
-- url     : https://prove2.me/submissions/911e2ff5-95f7-4e2e-8f2d-b78a6a2617e1

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ) :
    hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_add]
  congr 1
  ring
