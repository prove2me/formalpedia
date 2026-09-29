-- Prove2me | Theorems.Thm_Erdos146_hammingRetainedEdgeCount_lower_tail_probability_le
-- name    : Erdos146.hammingRetainedEdgeCount_lower_tail_probability_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:51:25.271623+00:00
-- url     : https://prove2.me/theorems/5b7a7554-9e96-415c-bcfa-fa021b6bd462
-- title:
--   Lower-tail bound for the retained edge count
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The probability that the retained edge count falls far below its mean is small. With Proposition 8.1's exclusion bound this leaves a positive-probability event on which the sampled graph is simultaneously $H$-free and dense.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L16669-L16750

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetainedEdgeCount_lower_tail_probability_le
    (dimension radius : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by sorry
