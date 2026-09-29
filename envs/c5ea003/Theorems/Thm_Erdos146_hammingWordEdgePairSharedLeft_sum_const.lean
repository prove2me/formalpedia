-- Prove2me | Theorems.Thm_Erdos146_hammingWordEdgePairSharedLeft_sum_const
-- name    : Erdos146.hammingWordEdgePairSharedLeft_sum_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:50:46.286467+00:00
-- url     : https://prove2.me/theorems/95d4b23c-013d-4406-bf64-ba4388862b83
-- title:
--   Counts of edge pairs sharing a left endpoint are constant
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The number of pairs of edges sharing their left endpoint is the same for every word — a second-moment input.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L16058-L16118

import Definitions.Def_erdos146_core2
import Mathlib.InformationTheory.Hamming

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingWordEdgePairSharedLeft_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by sorry
