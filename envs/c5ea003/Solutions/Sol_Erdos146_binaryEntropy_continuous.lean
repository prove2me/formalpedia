-- Prove2me | solution 1 for Erdos146.binaryEntropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:57:42.195593+00:00
-- url     : https://prove2.me/submissions/b52a2f53-98d0-4753-b6bf-8750e5085e77

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

@[fun_prop] theorem solution : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _
