-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:26:33.730663+00:00
-- url     : https://prove2.me/submissions/5706f5b9-d5cc-4ea7-9529-c4a324608ca0

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Function.L2Space
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (hammingRetentionMeasure_integrable dimension observable).aestronglyMeasurable).mpr
  exact hammingRetentionMeasure_integrable dimension
    (fun retained => observable retained ^ 2)
