-- Prove2me | solution 1 for Erdos146.binaryEntropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:57:00.78925+00:00
-- url     : https://prove2.me/submissions/3bb4231e-49a4-4c44-ae79-69498626b92c

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

@[simp] theorem solution : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]
