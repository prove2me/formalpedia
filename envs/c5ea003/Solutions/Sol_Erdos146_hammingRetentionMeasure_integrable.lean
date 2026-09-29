-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:25:52.172967+00:00
-- url     : https://prove2.me/submissions/c09791b0-754e-4c55-8fac-64bbbf692e21

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (hammingRetentionMeasure dimension) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  exact MeasureTheory.Integrable.of_finite
