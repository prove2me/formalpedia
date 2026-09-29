-- Prove2me | solution 1 for Erdos146.midpointBeta_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:09:37.931289+00:00
-- url     : https://prove2.me/submissions/63fa965e-0989-4361-a932-8f9566591a56

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.Basic
import Theorems.Thm_Erdos146_entropyUpperEndpoint_lt_one
import Theorems.Thm_Erdos146_midpointBeta_lt_upper_unconditional

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution : midpointBeta < 1 :=
  midpointBeta_lt_upper_unconditional.trans entropyUpperEndpoint_lt_one
