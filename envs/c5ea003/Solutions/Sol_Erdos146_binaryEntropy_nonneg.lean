-- Prove2me | solution 1 for Erdos146.binaryEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:55:37.888676+00:00
-- url     : https://prove2.me/submissions/fc8bc425-d76c-4dcc-991b-d9ac26395dd2

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ binaryEntropy x := by
  exact div_nonneg (Real.binEntropy_nonneg hzero hone) log_two_pos.le
