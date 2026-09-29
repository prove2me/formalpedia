-- Prove2me | solution 1 for Erdos146.manuscriptExtremalPower_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:51:14.737289+00:00
-- url     : https://prove2.me/submissions/03df14b5-ae1a-4346-b497-d31bb6c35c6a

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Theorems.Thm_Erdos146_exponentGain_pos

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution :
    0 < manuscriptExtremalPower := by
  unfold manuscriptExtremalPower
  linarith [exponentGain_pos]
