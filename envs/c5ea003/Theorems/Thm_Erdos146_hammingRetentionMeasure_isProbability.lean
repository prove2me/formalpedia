-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability
-- name    : Erdos146.hammingRetentionMeasure_isProbability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:47:25.024138+00:00
-- url     : https://prove2.me/theorems/96bb05d5-f007-4311-91c0-db4d924b4095
-- title:
--   The retention measure is a probability measure
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. Independent retention of each vertex with probability $p = 2^{-\beta m}$ defines a probability measure.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14800-L14804

import Definitions.Def_erdos146_core2
import Mathlib.Probability.Distributions.SetBernoulli

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_isProbability (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by sorry
