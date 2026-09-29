-- Prove2me | solution 1 for Erdos146.exponentGain_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:11:01.016612+00:00
-- url     : https://prove2.me/submissions/a8b7d807-98fd-45ed-aaf3-f72a5f0bff74

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Theorems.Thm_Erdos146_midpointBeta_lt_one

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution : 0 < exponentGain := by
  unfold exponentGain
  exact div_pos certifiedWindowWidth_pos
    (mul_pos (by norm_num) (sub_pos.mpr midpointBeta_lt_one))
